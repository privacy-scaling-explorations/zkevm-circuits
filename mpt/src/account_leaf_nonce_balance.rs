use halo2::{
    circuit::Chip,
    plonk::{Advice, Column, ConstraintSystem, Expression, VirtualCells},
    poly::Rotation,
};
use pasta_curves::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::param::HASH_WIDTH;

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
        q_enable: impl FnOnce(&mut VirtualCells<'_, F>) -> Expression<F>,
        s_advices: [Column<Advice>; HASH_WIDTH],
        c_advices: [Column<Advice>; HASH_WIDTH],
        acc_r: F,
        acc: Column<Advice>,
        acc_mult_s: Column<Advice>,
        acc_mult_c: Column<Advice>,
        r_table: Vec<Expression<F>>,
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

            // We have nonce in s_advices and balance in c_advices.

            let one = Expression::Constant(F::one());
            let c128 = Expression::Constant(F::from_u64(128));
            let acc_prev = meta.query_advice(acc, Rotation::prev());
            let acc_mult_prev = meta.query_advice(acc_mult_s, Rotation::prev());
            let mut curr_r = acc_mult_prev.clone();
            let s_advices0 = meta.query_advice(s_advices[0], Rotation::cur());
            let nonce_len = s_advices0.clone() - c128.clone();

            let mut expr =
                acc_prev.clone() + s_advices0.clone() * curr_r.clone();
            curr_r = curr_r * acc_r;
            for ind in 1..HASH_WIDTH {
                let s = meta.query_advice(s_advices[ind], Rotation::cur());
                expr = expr + s * curr_r.clone();
                curr_r = curr_r * acc_r;
            }

            let acc_mult_tmp = meta.query_advice(acc_mult_c, Rotation::cur());
            curr_r = acc_mult_tmp.clone();

            let c_advices0 = meta.query_advice(c_advices[0], Rotation::cur());
            let balance_len = c_advices0.clone() - c128.clone();
            expr = expr + c_advices0 * curr_r.clone();
            curr_r = curr_r * acc_r;
            for ind in 1..HASH_WIDTH {
                let c = meta.query_advice(c_advices[ind], Rotation::cur());
                expr = expr + c * curr_r.clone();
                curr_r = curr_r * acc_r;
            }

            let acc = meta.query_advice(acc, Rotation::cur());
            constraints.push((
                "leaf nonce balance acc",
                q_enable.clone() * (expr.clone() - acc),
            ));

            // nonzero_table has some nonzero values at the positions where we still have nonce bytes
            // and zeros after nonce bytes end
            let mut nonzero_table = vec![];
            nonzero_table.push(one.clone()); // s_advices[0]
            let mut z_counter = nonce_len.clone();
            let mut z_expr = one.clone();
            for _ in 0..HASH_WIDTH {
                nonzero_table.push(z_expr.clone());
                z_counter = z_counter - one.clone();
                z_expr = z_expr * z_counter.clone();
            }

            let c32 = Expression::Constant(F::from_u64(32));
            let mut counter = c32.clone() - nonce_len.clone() + one.clone();
            let mut is_trailing_zero_or_last_key = one.clone();

            let acc_mult_final = meta.query_advice(acc_mult_s, Rotation::cur());

            for ind in (1..HASH_WIDTH).rev() {
                counter = counter - one.clone();
                is_trailing_zero_or_last_key =
                    is_trailing_zero_or_last_key * counter.clone();
                // Either is_trailing_zero_or_last nonce is 0 (bytes before the last nonce byte) or
                // nonzero_table[ind] is 0 (bytes after the last key byte).
                // Except at the position of last nonce byte - there neither of these two is zero.
                let check =
                    (r_table[ind].clone() * acc_mult_prev.clone() * acc_r
                        - acc_mult_tmp.clone())
                        * nonzero_table[ind].clone()
                        * is_trailing_zero_or_last_key.clone();

                constraints
                    .push(("leaf nonce acc mult", q_enable.clone() * check));
            }

            // Balance mult:

            nonzero_table = vec![];
            nonzero_table.push(one.clone()); // c_advices[0]
            z_counter = balance_len.clone();
            z_expr = one.clone();
            for _ in 0..HASH_WIDTH {
                nonzero_table.push(z_expr.clone());
                z_counter = z_counter - one.clone();
                z_expr = z_expr * z_counter.clone();
            }

            counter = c32.clone() - balance_len.clone() + one.clone();
            is_trailing_zero_or_last_key = one.clone();

            for ind in (1..HASH_WIDTH).rev() {
                counter = counter - one.clone();
                is_trailing_zero_or_last_key =
                    is_trailing_zero_or_last_key * counter.clone();
                let check =
                    (r_table[ind].clone() * acc_mult_tmp.clone() * acc_r
                        - acc_mult_final.clone())
                        * nonzero_table[ind].clone()
                        * is_trailing_zero_or_last_key.clone();

                constraints
                    .push(("leaf balance acc mult", q_enable.clone() * check));
            }

            // TODO: integrate this in for loops above with query_advices
            // Now we need to ensure after nonce there are only 0s in s_advices.
            let mut k_counter = c32.clone() - nonce_len.clone();
            let mut is_not_balance = k_counter.clone();
            // is_not_nonce becomes 0 in the positions where we have nonce
            for ind in (0..HASH_WIDTH).rev() {
                k_counter = k_counter - one.clone();
                is_not_balance = is_not_balance * k_counter.clone();
                let s = meta.query_advice(s_advices[ind], Rotation::cur());
                constraints.push((
                    "account leaf nonce zeros",
                    q_enable.clone() * s * is_not_balance.clone(),
                ));
            }
            k_counter = c32 - balance_len.clone();
            is_not_balance = k_counter.clone();
            // is_not_balance becomes 0 in the positions where we have balance
            for ind in (0..HASH_WIDTH).rev() {
                k_counter = k_counter - one.clone();
                is_not_balance = is_not_balance * k_counter.clone();
                let c = meta.query_advice(c_advices[ind], Rotation::cur());
                constraints.push((
                    "account leaf balance zeros",
                    q_enable.clone() * c * is_not_balance.clone(),
                ));
            }

            constraints
        });

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
