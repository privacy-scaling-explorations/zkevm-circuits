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

// Verifies the intermediate account leaf RLC.
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
        s_mod_node_hash_rlc: Column<Advice>,
        c_mod_node_hash_rlc: Column<Advice>,
        sel1: Column<Advice>,
        sel2: Column<Advice>,
        is_storage_mod: Column<Advice>,
        is_nonce_mod: Column<Advice>,
        is_balance_mod: Column<Advice>,
        is_codehash_mod: Column<Advice>,
        fixed_table: [Column<Fixed>; 3],
        is_s: bool,
    ) -> AccountLeafNonceBalanceConfig {
        let config = AccountLeafNonceBalanceConfig {};
        let one = Expression::Constant(F::one());

        meta.create_gate("account leaf nonce balance", |meta| {
            let q_enable = q_enable(meta);
            let mut constraints = vec![];

            /*
            [248,112,157,59,158,160,175,159,65,212,107,23,98,208,38,205,150,63,244,2,185,236,246,95,240,224,191,229,27,102,202,231,184,80
            There are 112 bytes after the first two bytes.
            157 means the key is 29 (157 - 128) bytes long.
            */

            // Nonce, balance, storage, codehash are string in RLP: s_rlp1 and s_rlp2
            // contains the length of this string, for example 184 80 means the second
            // part is of length 1 (183 + 1 = 184) and there are 80 bytes in this string.
            // Then there is a list rlp meta data 248 78 where (this is stored in c_rlp1 and
            // c_rlp2) 78 = 3 (nonce) + 9 (balance) + 33 (storage) + 33
            // (codehash). We have nonce in s_advices and balance in c_advices.
            // s_rlp1  s_rlp2  c_rlp1  c_rlp2  s_advices  c_advices
            // 184     80      248     78      nonce      balance

            // TODO: nonce and balance compared to the input

            let mut rot = -1;
            if !is_s {
                rot = -2;
            }

            let c128 = Expression::Constant(F::from(128));
            let c248 = Expression::Constant(F::from(248));
            let acc_prev = meta.query_advice(acc, Rotation(rot));
            let acc_mult_prev = meta.query_advice(acc_mult_s, Rotation(rot));
            let acc_mult_after_nonce = meta.query_advice(acc_mult_c, Rotation::cur());
            let mult_diff_nonce = meta.query_advice(mult_diff_nonce, Rotation::cur());
            let mult_diff_balance = meta.query_advice(mult_diff_balance, Rotation::cur());

            let key_len = meta.query_advice(s_advices[0], Rotation(rot)) - c128.clone();
            // nonce_len + 128:
            let s_advices0_cur = meta.query_advice(s_advices[0], Rotation::cur());

            let s_rlp1 = meta.query_advice(s_rlp1, Rotation::cur());
            let rlp_len = meta.query_advice(s_rlp2, Rotation(rot));
            let s_rlp2 = meta.query_advice(s_rlp2, Rotation::cur());

            let mut expr = acc_prev + s_rlp1.clone() * acc_mult_prev.clone();
            let mut rind = 0;
            expr = expr + s_rlp2.clone() * acc_mult_prev.clone() * r_table[rind].clone();
            rind += 1;

            let c_rlp1 = meta.query_advice(c_rlp1, Rotation::cur());
            let c_rlp2 = meta.query_advice(c_rlp2, Rotation::cur());
            constraints.push((
                "leaf nonce balance c_rlp1",
                q_enable.clone() * (c_rlp1.clone() - c248.clone()),
            ));
            expr = expr + c_rlp1.clone() * acc_mult_prev.clone() * r_table[rind].clone();
            rind += 1;
            expr = expr + c_rlp2.clone() * acc_mult_prev.clone() * r_table[rind].clone();
            rind += 1;

            let nonce_rlc = s_advices0_cur.clone()
                + compute_rlc(
                    meta,
                    s_advices.iter().skip(1).map(|v| *v).collect_vec(),
                    0,
                    one.clone(),
                    0,
                    r_table.clone(),
                );

            let nonce_stored = meta.query_advice(s_mod_node_hash_rlc, Rotation::cur());
            constraints.push((
                "nonce RLC",
                q_enable.clone() * (nonce_rlc.clone() - nonce_stored.clone()),
            ));

            expr = expr + nonce_rlc * r_table[rind].clone() * acc_mult_prev.clone();

            let c_advices0_prev = meta.query_advice(c_advices[0], Rotation::prev());
            // balance_len + 128:
            let c_advices0_cur = meta.query_advice(c_advices[0], Rotation::cur());

            let balance_stored = meta.query_advice(c_mod_node_hash_rlc, Rotation::cur());
            let balance_rlc = c_advices0_cur.clone()
                + compute_rlc(
                    meta,
                    c_advices.iter().skip(1).map(|v| *v).collect_vec(),
                    0,
                    one.clone(),
                    0,
                    r_table.clone(),
                );

            constraints.push((
                "balance RLC",
                q_enable.clone() * (balance_rlc.clone() - balance_stored.clone()),
            ));

            if !is_s {
                let nonce_s_from_prev = meta.query_advice(s_mod_node_hash_rlc, Rotation::prev());
                let nonce_s_from_cur = meta.query_advice(sel1, Rotation::cur());
                let balance_s_from_prev = meta.query_advice(c_mod_node_hash_rlc, Rotation::prev());
                let balance_s_from_cur = meta.query_advice(sel2, Rotation::cur());
                // We need correct previous nonce to enable lookup in nonce balance C row:
                constraints.push((
                    "nonce prev RLC",
                    q_enable.clone() * (nonce_s_from_prev.clone() - nonce_s_from_cur.clone()),
                ));
                // We need correct previous balance to enable lookup in nonce balance C row:
                constraints.push((
                    "balance prev RLC",
                    q_enable.clone() * (balance_s_from_prev.clone() - balance_s_from_cur.clone()),
                ));

                // Check there is only one modification at once:
                let is_storage_mod = meta.query_advice(is_storage_mod, Rotation::cur());
                let is_nonce_mod = meta.query_advice(is_nonce_mod, Rotation::cur());
                let is_balance_mod = meta.query_advice(is_balance_mod, Rotation::cur());
                let is_codehash_mod = meta.query_advice(is_codehash_mod, Rotation::cur());

                constraints.push((
                    "if storage / codehash / balance mod: nonce_s = nonce_c",
                    q_enable.clone()
                        * (is_storage_mod.clone()
                            + is_codehash_mod.clone()
                            + is_balance_mod.clone())
                        * (nonce_s_from_cur.clone() - nonce_stored.clone()),
                ));
                constraints.push((
                    "if storage / codehash / nonce mod: balance_s = balance_c",
                    q_enable.clone()
                        * (is_storage_mod.clone() + is_codehash_mod.clone() + is_nonce_mod.clone())
                        * (balance_s_from_cur.clone() - balance_stored.clone()),
                ));
            }

            expr = expr + balance_rlc * acc_mult_after_nonce.clone();

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

            // RLP:
            let c66 = Expression::Constant(F::from(66)); // the number of bytes in storage codehash row
            let c184 = Expression::Constant(F::from(184));
            let nonce_len = s_advices0_cur - c128.clone();
            let balance_len = c_advices0_cur - c128.clone();
            // s_rlp1  s_rlp2  c_rlp1  c_rlp2  s_advices  c_advices
            // 184     80      248     78      nonce      balance
            constraints.push(("RLP 1", q_enable.clone() * (s_rlp1.clone() - c184)));
            constraints.push(("RLP 2", q_enable.clone() * (c_rlp1.clone() - c248)));
            constraints.push((
                "RLP 3",
                q_enable.clone() * (s_rlp2.clone() - c_rlp2.clone() - one.clone() - one.clone()),
            ));
            constraints.push((
                "RLP 4",
                q_enable.clone()
                    * (c_rlp2.clone() - nonce_len - one.clone() - balance_len - one.clone() - c66),
            ));
            constraints.push((
                "account leaf RLP length",
                q_enable.clone() * (rlp_len - key_len - one.clone() - s_rlp2 - one.clone() - one),
                // -1 because key_len is stored in 1 column
                // -1 because of s_rlp1
                // -1 because of s_rlp2
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
