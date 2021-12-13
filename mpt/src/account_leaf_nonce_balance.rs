use halo2::{
    circuit::Chip,
    plonk::{Advice, Column, ConstraintSystem, Expression, VirtualCells},
    poly::Rotation,
};
use pasta_curves::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::param::{HASH_WIDTH, R_TABLE_LEN};

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
        s_rlp1: Column<Advice>,
        s_rlp2: Column<Advice>,
        c_rlp1: Column<Advice>,
        c_rlp2: Column<Advice>,
        s_advices: [Column<Advice>; HASH_WIDTH],
        c_advices: [Column<Advice>; HASH_WIDTH],
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

            // Nonce, balance, storage, codehash are string in RLP: s_rlp1 and s_rlp2
            // contains the length of this string, for example 184 80 means the second
            // part is of length 1 (183 + 1 = 184) and there are 80 bytes in this string.
            // Then there is a list rlp meta data 248 78 where (this is stored in c_rlp1 and c_rlp2)
            // 78 = 3 (nonce) + 9 (balance) + 33 (storage) + 33 (codehash).
            // We have nonce in s_advices and balance in c_advices.

            // TODO: nonce and balance compared to the input

            let one = Expression::Constant(F::one());
            let c128 = Expression::Constant(F::from_u64(128));
            let c248 = Expression::Constant(F::from_u64(248));
            let acc_prev = meta.query_advice(acc, Rotation::prev());
            let acc_mult_prev = meta.query_advice(acc_mult_s, Rotation::prev());
            let acc_mult_tmp = meta.query_advice(acc_mult_c, Rotation::cur());
            let s_advices0 = meta.query_advice(s_advices[0], Rotation::cur());
            let nonce_len = s_advices0.clone() - c128.clone();

            let mut expr = acc_prev.clone()
                + meta.query_advice(s_rlp1, Rotation::cur())
                    * acc_mult_prev.clone();
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
            expr =
                expr + c_rlp1 * acc_mult_prev.clone() * r_table[rind].clone();
            rind += 1;
            expr = expr
                + meta.query_advice(c_rlp2, Rotation::cur())
                    * acc_mult_prev.clone()
                    * r_table[rind].clone();
            rind += 1;

            expr = expr
                + s_advices0.clone()
                    * acc_mult_prev.clone()
                    * r_table[rind].clone();
            rind += 1;

            let mut r_wrapped = false;
            for ind in 1..HASH_WIDTH {
                let s = meta.query_advice(s_advices[ind], Rotation::cur());
                if !r_wrapped {
                    expr = expr
                        + s * acc_mult_prev.clone() * r_table[rind].clone();
                } else {
                    expr = expr
                        + s * acc_mult_prev.clone()
                            * r_table[rind].clone()
                            * r_table[R_TABLE_LEN - 1].clone();
                }
                if rind == R_TABLE_LEN - 1 {
                    rind = 0;
                    r_wrapped = true;
                } else {
                    rind += 1;
                }
            }

            let c_advices0 = meta.query_advice(c_advices[0], Rotation::cur());
            let balance_len = c_advices0.clone() - c128.clone();
            expr = expr + c_advices0 * acc_mult_tmp.clone();
            rind = 0;
            for ind in 1..HASH_WIDTH {
                let c = meta.query_advice(c_advices[ind], Rotation::cur());
                expr = expr + c * acc_mult_tmp.clone() * r_table[rind].clone();
                rind += 1;
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
            let mut z_expr = z_counter.clone(); // nonce_len can be 0 too
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
                let check = (r_table[ind-1].clone()
                    * acc_mult_prev.clone()
                    * r_table[3].clone() // s_rlp1, s_rlp2, c_rlp1, c_rlp2
                    * r_table[0].clone()
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
            z_expr = balance_len.clone(); // balance_len can be 0 too
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
                let check = (r_table[ind - 1].clone()
                    * acc_mult_tmp.clone()
                    * r_table[0].clone()
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
