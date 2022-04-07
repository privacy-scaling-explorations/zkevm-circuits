use halo2_proofs::{
    circuit::Chip,
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, VirtualCells},
    poly::Rotation,
};
use pairing::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::{
    helpers::{compute_rlc, key_len_lookup, mult_diff_lookup, range_lookups},
    mpt::FixedTableTag,
    param::{HASH_WIDTH, IS_BRANCH_C16_POS, IS_BRANCH_C1_POS, LAYOUT_OFFSET, R_TABLE_LEN},
};

#[derive(Clone, Debug)]
pub(crate) struct AccountLeafKeyConfig {}

// Verifies the address RLC. Verified the intermediate account leaf RLC.
pub(crate) struct AccountLeafKeyChip<F> {
    config: AccountLeafKeyConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> AccountLeafKeyChip<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: impl Fn(&mut VirtualCells<'_, F>) -> Expression<F> + Copy,
        q_not_first: Column<Fixed>,
        s_rlp1: Column<Advice>,
        s_rlp2: Column<Advice>,
        c_rlp1: Column<Advice>,
        c_rlp2: Column<Advice>,
        s_advices: [Column<Advice>; HASH_WIDTH],
        acc: Column<Advice>,
        acc_mult: Column<Advice>,
        key_rlc: Column<Advice>,
        key_rlc_mult: Column<Advice>,
        r_table: Vec<Expression<F>>,
        fixed_table: [Column<Fixed>; 3],
        address_rlc: Column<Advice>,
    ) -> AccountLeafKeyConfig {
        let config = AccountLeafKeyConfig {};

        meta.create_gate("account leaf key", |meta| {
            let q_enable = q_enable(meta);
            let mut constraints = vec![];

            /*
            [248,112,157,59,158,160,175,159,65,212,107,23,98,208,38,205,150,63,244,2,185,236,246,95,240,224,191,229,27,102,202,231,184,80
            There are 112 bytes after the first two bytes.
            157 means the key is 29 (157 - 128) bytes long.
            */

            let one = Expression::Constant(F::one());
            let c248 = Expression::Constant(F::from(248));

            let s_rlp1 = meta.query_advice(s_rlp1, Rotation::cur());
            constraints.push((
                "account leaf key s_rlp1 = 248",
                q_enable.clone() * (s_rlp1.clone() - c248),
            ));

            let mut ind = 0;
            let mut expr =
                s_rlp1 + meta.query_advice(s_rlp2, Rotation::cur()) * r_table[ind].clone();
            ind += 1;

            expr = expr
                + compute_rlc(
                    meta,
                    s_advices.to_vec(),
                    ind,
                    one.clone(),
                    0,
                    r_table.clone(),
                );

            let c_rlp1 = meta.query_advice(c_rlp1, Rotation::cur());
            let c_rlp2 = meta.query_advice(c_rlp2, Rotation::cur());
            expr = expr + c_rlp1.clone() * r_table[R_TABLE_LEN - 1].clone() * r_table[1].clone();
            expr = expr + c_rlp2.clone() * r_table[R_TABLE_LEN - 1].clone() * r_table[2].clone();

            let acc = meta.query_advice(acc, Rotation::cur());

            constraints.push(("leaf key acc", q_enable.clone() * (expr - acc)));

            constraints
        });

        // Note: key length is always in s_advices[0] here as opposed to storage
        // key leaf where it can appear in s_rlp2 too. This is because account
        // leaf contains nonce, balance, ... which makes it always longer than 55 bytes,
        // which makes a RLP to start with 248 (s_rlp1) and having one byte (in s_rlp2)
        // for the length of the remaining stream.
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
        key_len_lookup(meta, q_enable, 32, s_advices[0], c_rlp1, fixed_table);
        key_len_lookup(meta, q_enable, 33, s_advices[0], c_rlp2, fixed_table);
        */

        // acc_mult corresponds to key length:
        mult_diff_lookup(meta, q_enable, 3, s_advices[0], acc_mult, fixed_table);

        // No need to check key_rlc_mult as it's not used after this row.
        meta.create_gate("Account leaf address RLC", |meta| {
            let q_enable = q_enable(meta);
            let mut constraints = vec![];

            // key rlc is in the first branch node
            let rot = -18;
            let key_rlc_acc_start = meta.query_advice(key_rlc, Rotation(rot));
            let key_mult_start = meta.query_advice(key_rlc_mult, Rotation(rot));
            // sel1, sel2 is in init branch
            let sel1 = meta.query_advice(
                s_advices[IS_BRANCH_C16_POS - LAYOUT_OFFSET],
                Rotation(rot - 1),
            );
            let sel2 = meta.query_advice(
                s_advices[IS_BRANCH_C1_POS - LAYOUT_OFFSET],
                Rotation(rot - 1),
            );

            let c32 = Expression::Constant(F::from(32));
            let c48 = Expression::Constant(F::from(48));

            // If sel1 = 1, we have nibble+48 in s_advices[0].
            let s_advice1 = meta.query_advice(s_advices[1], Rotation::cur());
            let mut key_rlc_acc = key_rlc_acc_start
                + (s_advice1.clone() - c48) * key_mult_start.clone() * sel1.clone();
            let mut key_mult = key_mult_start.clone() * r_table[0].clone() * sel1;
            key_mult = key_mult + key_mult_start.clone() * sel2.clone(); // set to key_mult_start if sel2, stays key_mult if sel1

            // If sel2 = 1, we have 32 in s_advices[0].
            constraints.push((
                "Account leaf key acc s_advice1",
                q_enable.clone() * (s_advice1 - c32) * sel2,
            ));

            let s_advices2 = meta.query_advice(s_advices[2], Rotation::cur());
            key_rlc_acc = key_rlc_acc + s_advices2 * key_mult.clone();

            for ind in 3..HASH_WIDTH {
                let s = meta.query_advice(s_advices[ind], Rotation::cur());
                key_rlc_acc = key_rlc_acc + s * key_mult.clone() * r_table[ind - 3].clone();
            }

            let c_rlp1 = meta.query_advice(c_rlp1, Rotation::cur());
            let c_rlp2 = meta.query_advice(c_rlp2, Rotation::cur());
            key_rlc_acc = key_rlc_acc + c_rlp1 * key_mult.clone() * r_table[30].clone();
            key_rlc_acc = key_rlc_acc + c_rlp2 * key_mult * r_table[31].clone();

            let key_rlc = meta.query_advice(key_rlc, Rotation::cur());
            let address_rlc = meta.query_advice(address_rlc, Rotation::cur());

            // Key RLC is to be checked to verify that the proper key is used.
            constraints.push((
                "Account address RLC",
                q_enable.clone() * (key_rlc_acc - key_rlc.clone()),
            ));

            constraints.push((
                "Computed account address RLC same as value in address_rlc column",
                q_enable * (key_rlc - address_rlc),
            ));

            constraints
        });

        range_lookups(
            meta,
            q_enable,
            s_advices.to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );
        // s_rlp1 is always 248 (checked above)
        range_lookups(
            meta,
            q_enable,
            [s_rlp2, c_rlp1, c_rlp2].to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );

        config
    }

    pub fn construct(config: AccountLeafKeyConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }
}

impl<F: FieldExt> Chip<F> for AccountLeafKeyChip<F> {
    type Config = AccountLeafKeyConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}
