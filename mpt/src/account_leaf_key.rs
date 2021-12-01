use halo2::{
    circuit::Chip,
    plonk::{Advice, Column, ConstraintSystem, Expression, VirtualCells},
    poly::Rotation,
};
use pasta_curves::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::param::HASH_WIDTH;

#[derive(Clone, Debug)]
pub(crate) struct AccountLeafKeyConfig {}

// Verifies the hash of a leaf is in the parent branch.
pub(crate) struct AccountLeafKeyChip<F> {
    config: AccountLeafKeyConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> AccountLeafKeyChip<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: impl FnOnce(&mut VirtualCells<'_, F>) -> Expression<F>,
        s_rlp1: Column<Advice>,
        s_rlp2: Column<Advice>,
        c_rlp1: Column<Advice>,
        s_advices: [Column<Advice>; HASH_WIDTH],
        acc_r: F,
        acc: Column<Advice>,
        acc_mult: Column<Advice>,
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

            // TODO: RLP properties

            let one = Expression::Constant(F::one());
            let mut r_table = vec![];
            let mut curr_r = Expression::Constant(F::one());
            r_table.push(curr_r.clone());
            let mut expr = meta.query_advice(s_rlp1, Rotation::cur());
            curr_r = curr_r * acc_r;
            r_table.push(curr_r.clone());
            expr = expr
                + meta.query_advice(s_rlp2, Rotation::cur()) * curr_r.clone();
            curr_r = curr_r * acc_r;
            r_table.push(curr_r.clone());

            // TODO: from key_len on there are 0s

            for col in s_advices.iter() {
                let s = meta.query_advice(*col, Rotation::cur());
                expr = expr + s * curr_r.clone();
                curr_r = curr_r * acc_r;
                r_table.push(curr_r.clone());
            }
            let c_rlp1 = meta.query_advice(c_rlp1, Rotation::cur());
            expr = expr + c_rlp1.clone() * curr_r.clone();
            curr_r = curr_r * acc_r;
            r_table.push(curr_r.clone());

            // Key can't go further than c_rlp1.

            let acc = meta.query_advice(acc, Rotation::cur());
            let acc_mult = meta.query_advice(acc_mult, Rotation::cur());

            constraints.push((
                "leaf key acc",
                q_enable.clone() * (expr.clone() - acc),
            ));

            // The curr_r above is being increased also in the columns where there is no key anymore, so
            // we cannot compare it to acc_mult.
            // Let's say we have a key of length 3, then: [248,112,131,59,158,160,0,0,0,...
            // 131 - 18 presents the key length.
            // key length is at s_advices[0], key is from s_advices[1] to s_advices[1+key_len] (at most c_rlp1)

            let c32 = Expression::Constant(F::from_u64(32));
            let c128 = Expression::Constant(F::from_u64(128));
            let key_len =
                meta.query_advice(s_advices[0], Rotation::cur()) - c128;

            // nonzero_table has some nonzero values at the positions where we still have key bytes
            // and zeros after key bytes end
            let mut nonzero_table = vec![];
            nonzero_table.push(one.clone()); // s_rlp1
            nonzero_table.push(one.clone()); // s_rlp2
            nonzero_table.push(one.clone()); // s_advices[0]
            let mut z_counter = key_len.clone();
            let mut z_expr = one.clone();
            for _ in 0..HASH_WIDTH {
                nonzero_table.push(z_expr.clone());
                z_counter = z_counter - one.clone();
                z_expr = z_expr * z_counter.clone();
            }

            let mut counter = c32.clone() - key_len.clone() + one.clone();
            let mut is_trailing_zero_or_last_key = one.clone();

            let check = (r_table[HASH_WIDTH + 2].clone() * acc_r
                - acc_mult.clone())
                * nonzero_table[HASH_WIDTH + 2].clone()
                * is_trailing_zero_or_last_key.clone();
            constraints
                .push(("leaf key acc mult c_rlp1", q_enable.clone() * check));

            for ind in (1..HASH_WIDTH).rev() {
                counter = counter - one.clone();
                is_trailing_zero_or_last_key =
                    is_trailing_zero_or_last_key * counter.clone();
                // Either is_trailing_zero_or_last key is 0 (bytes before the last key byte) or
                // nonzero_table[ind+2] is 0 (bytes after the last key byte).
                // Except at the position of last key byte - there neither of these two is zero.
                let check = (r_table[ind + 2].clone() * acc_r
                    - acc_mult.clone())
                    * nonzero_table[ind + 2].clone()
                    * is_trailing_zero_or_last_key.clone();

                constraints.push((
                    "leaf key acc mult s_advices",
                    q_enable.clone() * check,
                ));
            }

            // Now we need to ensure after key_len there are only 0s.
            let mut k_counter = c32 - key_len.clone();
            let mut is_not_key = k_counter.clone();

            constraints.push((
                "leaf key zeros c_rlp1",
                q_enable.clone() * c_rlp1 * is_not_key.clone(),
            ));

            // is_not_key becomes 0 in the positions where we have key
            for ind in (1..HASH_WIDTH).rev() {
                k_counter = k_counter - one.clone();
                is_not_key = is_not_key * k_counter.clone();
                let s = meta.query_advice(s_advices[ind], Rotation::cur());
                constraints.push((
                    "leaf key zeros",
                    q_enable.clone() * s * is_not_key.clone(),
                ));
            }

            constraints
        });

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
