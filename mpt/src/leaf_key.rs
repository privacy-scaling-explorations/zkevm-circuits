use halo2::{
    circuit::Chip,
    plonk::{Advice, Column, ConstraintSystem, Expression, VirtualCells},
    poly::Rotation,
};
use pasta_curves::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::param::HASH_WIDTH;

#[derive(Clone, Debug)]
pub(crate) struct LeafKeyConfig {}

// Verifies RLC of a leaf key.
pub(crate) struct LeafKeyChip<F> {
    config: LeafKeyConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> LeafKeyChip<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: impl Fn(&mut VirtualCells<'_, F>) -> Expression<F>,
        s_rlp1: Column<Advice>,
        s_rlp2: Column<Advice>,
        c_rlp1: Column<Advice>,
        s_advices: [Column<Advice>; HASH_WIDTH],
        s_keccak0: Column<Advice>, // to see whether it's long or short RLP
        s_keccak1: Column<Advice>, // to see whether it's long or short RLP
        acc: Column<Advice>,
        acc_mult: Column<Advice>,
        acc_r: F,
    ) -> LeafKeyConfig {
        let config = LeafKeyConfig {};

        meta.create_gate("Storage leaf key", |meta| {
            let q_enable = q_enable(meta);
            let mut constraints = vec![];

            let c248 = Expression::Constant(F::from_u64(248));
            let s_rlp1 = meta.query_advice(s_rlp1, Rotation::cur());
            let is_long = meta.query_advice(s_keccak0, Rotation::cur());
            // let is_short = meta.query_advice(acc_c, Rotation::cur());
            constraints.push((
                "is long",
                q_enable.clone() * is_long.clone() * (s_rlp1.clone() - c248),
            ));

            // TODO: is_long, is_short are booleans
            // TODO: is_long + is_short = 1

            let mut rlc = Expression::Constant(F::zero());
            let mut mult = Expression::Constant(F::one());

            // TODO: check that from some point on (depends on the rlp meta data)
            // the values are zero (as in key_compr) - but take into account it can be long or short RLP

            // TODO: check acc_mult as in key_compr

            // TODO: r_table

            rlc = rlc + s_rlp1 * mult.clone();
            mult = mult * acc_r;

            let s_rlp2 = meta.query_advice(s_rlp2, Rotation::cur());
            rlc = rlc + s_rlp2 * mult.clone();
            mult = mult * acc_r;

            for col in s_advices.iter() {
                let s = meta.query_advice(*col, Rotation::cur());
                rlc = rlc + s * mult.clone();
                mult = mult * acc_r;
            }

            let c_rlp1 = meta.query_advice(c_rlp1, Rotation::cur());
            rlc = rlc + c_rlp1 * mult.clone();

            // key is at most of length 32, so it doesn't go further than c_rlp1

            let acc = meta.query_advice(acc, Rotation::cur());
            constraints.push(("Leaf key acc", q_enable.clone() * (rlc - acc)));

            constraints
        });

        config
    }

    pub fn construct(config: LeafKeyConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }
}

impl<F: FieldExt> Chip<F> for LeafKeyChip<F> {
    type Config = LeafKeyConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}
