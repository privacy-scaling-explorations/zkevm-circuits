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

            let mut curr_r = Expression::Constant(F::one());
            let mut expr = meta.query_advice(s_rlp1, Rotation::cur());
            curr_r = curr_r * acc_r;
            expr = expr
                + meta.query_advice(s_rlp2, Rotation::cur()) * curr_r.clone();
            curr_r = curr_r * acc_r;

            // TODO: from key_len on there are 0s
            // TODO: curr_r not increasing from key_len on

            for col in s_advices.iter() {
                let s = meta.query_advice(*col, Rotation::cur());
                expr = expr + s * curr_r.clone();
                curr_r = curr_r * acc_r;
            }
            let c_rlp1 = meta.query_advice(c_rlp1, Rotation::cur());
            expr = expr + c_rlp1 * curr_r.clone();
            // Key can't go further than c_rlp1.

            let acc = meta.query_advice(acc, Rotation::cur());
            let acc_mult = meta.query_advice(acc_mult, Rotation::cur());

            constraints.push((
                "leaf key acc",
                q_enable.clone() * (expr.clone() - acc),
            ));
            constraints.push((
                "leaf key acc mult",
                q_enable.clone() * (acc_mult.clone() - curr_r),
            ));

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
