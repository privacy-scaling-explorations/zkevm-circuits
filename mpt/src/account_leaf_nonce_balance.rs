use halo2_proofs::{
    circuit::Chip,
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, VirtualCells},
    poly::Rotation,
};
use itertools::Itertools;
use pairing::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::{
    helpers::{compute_rlc, key_len_lookup, mult_diff_lookup, range_lookups},
    mpt::FixedTableTag,
    param::HASH_WIDTH,
};

#[derive(Clone, Debug)]
pub(crate) struct AccountLeafNonceBalanceConfig {}

// Verifies the hash of a leaf is in the parent branch.
pub(crate) struct AccountLeafNonceBalanceChip<F> {
    config: AccountLeafNonceBalanceConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> AccountLeafNonceBalanceChip<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: impl Fn(&mut VirtualCells<'_, F>) -> Expression<F> + Copy,
        s_rlp1: Column<Advice>,
        s_rlp2: Column<Advice>,
        c_rlp1: Column<Advice>,
        c_rlp2: Column<Advice>,
        s_advices: [Column<Advice>; HASH_WIDTH],
        c_advices: [Column<Advice>; HASH_WIDTH],
        acc: Column<Advice>,
        acc_mult_s: Column<Advice>,
        acc_mult_c: Column<Advice>,
        mult_diff_nonce: Column<Advice>,
        mult_diff_balance: Column<Advice>,
        r_table: Vec<Expression<F>>,
        fixed_table: [Column<Fixed>; 3],
    ) -> AccountLeafNonceBalanceConfig {
        let config = AccountLeafNonceBalanceConfig {};

        meta.create_gate("account leaf nonce balance", |meta| {
            let q_enable = q_enable(meta);
            let mut constraints = vec![];

            /*
            [248,112,157,59,158,160,175,159,65,212,107,23,98,208,38,205,150,63,244,2,185,236,246,95,240,224,191,229,27,102,202,231,184,80
            There are 112 bytes after the first two bytes.
            157 means the key is 29 (157 - 128) bytes long.
            */

            // TODO: RLP properties

            // Nonce, balance, storage, codehash are string in RLP: s_rlp1 and s_rlp2
            // contains the length of this string, for example 184 80 means the second
            // part is of length 1 (183 + 1 = 184) and there are 80 bytes in this string.
            // Then there is a list rlp meta data 248 78 where (this is stored in c_rlp1 and
            // c_rlp2) 78 = 3 (nonce) + 9 (balance) + 33 (storage) + 33
            // (codehash). We have nonce in s_advices and balance in c_advices.

            // TODO: nonce and balance compared to the input

            let c248 = Expression::Constant(F::from(248));
            let acc_prev = meta.query_advice(acc, Rotation::prev());
            let acc_mult_prev = meta.query_advice(acc_mult_s, Rotation::prev());
            let acc_mult_after_nonce = meta.query_advice(acc_mult_c, Rotation::cur());
            let mult_diff_nonce = meta.query_advice(mult_diff_nonce, Rotation::cur());
            let mult_diff_balance = meta.query_advice(mult_diff_balance, Rotation::cur());

            let s_advices0 = meta.query_advice(s_advices[0], Rotation::cur());

            let mut expr =
                acc_prev + meta.query_advice(s_rlp1, Rotation::cur()) * acc_mult_prev.clone();
            let mut rind = 0;
            expr = expr
                + meta.query_advice(s_rlp2, Rotation::cur())
                    * acc_mult_prev.clone()
                    * r_table[rind].clone();
            rind += 1;

            let c_rlp1 = meta.query_advice(c_rlp1, Rotation::cur());
            constraints.push((
                "leaf nonce balance c_rlp1",
                q_enable.clone() * (c_rlp1.clone() - c248),
            ));
            expr = expr + c_rlp1 * acc_mult_prev.clone() * r_table[rind].clone();
            rind += 1;
            expr = expr
                + meta.query_advice(c_rlp2, Rotation::cur())
                    * acc_mult_prev.clone()
                    * r_table[rind].clone();
            rind += 1;

            expr = expr + s_advices0 * acc_mult_prev.clone() * r_table[rind].clone();
            rind += 1;

            expr = expr
                + compute_rlc(
                    meta,
                    s_advices.iter().skip(1).map(|v| *v).collect_vec(),
                    rind,
                    acc_mult_prev.clone(),
                    0,
                    r_table.clone(),
                );

            let c_advices0 = meta.query_advice(c_advices[0], Rotation::cur());
            expr = expr + c_advices0 * acc_mult_after_nonce.clone();
            rind = 0;
            for ind in 1..HASH_WIDTH {
                let c = meta.query_advice(c_advices[ind], Rotation::cur());
                expr = expr + c * acc_mult_after_nonce.clone() * r_table[rind].clone();
                rind += 1;
            }

            let acc = meta.query_advice(acc, Rotation::cur());
            constraints.push(("leaf nonce balance acc", q_enable.clone() * (expr - acc)));

            let acc_mult_final = meta.query_advice(acc_mult_s, Rotation::cur());

            constraints.push((
                "leaf nonce acc mult",
                q_enable.clone()
                    * (acc_mult_after_nonce.clone()
                        - acc_mult_prev.clone() * mult_diff_nonce.clone()),
            ));

            // Balance mult:

            constraints.push((
                "leaf nonce acc mult",
                q_enable.clone()
                    * (acc_mult_final.clone()
                        - acc_mult_after_nonce.clone() * mult_diff_balance.clone()),
            ));

            constraints
        });

        // mult_diff_nonce corresponds to nonce length:
        mult_diff_lookup(
            meta,
            q_enable.clone(),
            5, // 4 for s_rlp1, s_rlp2, c_rlp1, c_rlp1; 1 for byte with length info
            s_advices[0],
            mult_diff_nonce,
            fixed_table,
        );

        // There are zeros in s_advices after nonce length:
        /*
        for ind in 1..HASH_WIDTH {
            key_len_lookup(
                meta,
                q_enable,
                ind,
                s_advices[0],
                s_advices[ind],
                fixed_table,
            )
        }
        */

        // mult_diff_balance corresponds to balance length:
        mult_diff_lookup(
            meta,
            q_enable,
            1, // 1 for byte with length info
            c_advices[0],
            mult_diff_balance,
            fixed_table,
        );

        // There are zeros in c_advices after balance length:
        /*
        for ind in 1..HASH_WIDTH {
            key_len_lookup(
                meta,
                q_enable,
                ind,
                c_advices[0],
                c_advices[ind],
                fixed_table,
            )
        }
        */

        range_lookups(
            meta,
            q_enable,
            s_advices.to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );
        range_lookups(
            meta,
            q_enable,
            c_advices.to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );
        // c_rlp1 is always 248 (checked above)
        range_lookups(
            meta,
            q_enable,
            [s_rlp1, s_rlp2, c_rlp2].to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );

        config
    }

    pub fn construct(config: AccountLeafNonceBalanceConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }
}

impl<F: FieldExt> Chip<F> for AccountLeafNonceBalanceChip<F> {
    type Config = AccountLeafNonceBalanceConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}
