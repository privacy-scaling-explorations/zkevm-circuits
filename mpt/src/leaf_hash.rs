use halo2::{
    circuit::Chip,
    plonk::{
        Advice, Column, ConstraintSystem, Expression, Fixed, VirtualCells,
    },
    poly::Rotation,
};
use pasta_curves::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::param::{HASH_WIDTH, KECCAK_INPUT_WIDTH, KECCAK_OUTPUT_WIDTH};

#[derive(Clone, Debug)]
pub(crate) struct LeafHashConfig {}

// Verifies the hash of a leaf is in the parent branch.
pub(crate) struct LeafHashChip<F> {
    config: LeafHashConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> LeafHashChip<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: impl FnOnce(&mut VirtualCells<'_, F>) -> Expression<F>,
        s_rlp1: Column<Advice>,
        s_rlp2: Column<Advice>,
        c_rlp1: Column<Advice>,
        c_rlp2: Column<Advice>,
        s_advices: [Column<Advice>; HASH_WIDTH],
        c_advices: [Column<Advice>; HASH_WIDTH],
        branch_acc_r: F,
        sc_keccak: [Column<Advice>; KECCAK_OUTPUT_WIDTH],
        keccak_table: [Column<Fixed>; KECCAK_INPUT_WIDTH + KECCAK_OUTPUT_WIDTH],
    ) -> LeafHashConfig {
        let config = LeafHashConfig {};

        meta.lookup(|meta| {
            let q_enable = q_enable(meta);

            let mut rlc = Expression::Constant(F::zero());
            let mut mult = Expression::Constant(F::one());

            // TODO: check that from some point on (depends on the rlp meta data)
            // the values are zero (as in key_compr), could be a chip just for this check
            let s_rlp1 = meta.query_advice(s_rlp1, Rotation::cur());
            rlc = rlc + s_rlp1 * mult.clone();
            mult = mult * branch_acc_r;

            let s_rlp2 = meta.query_advice(s_rlp2, Rotation::cur());
            rlc = rlc + s_rlp2 * mult.clone();
            mult = mult * branch_acc_r;

            for col in s_advices.iter() {
                let s = meta.query_advice(*col, Rotation::cur());
                rlc = rlc + s * mult.clone();
                mult = mult * branch_acc_r;
            }

            let c_rlp1 = meta.query_advice(c_rlp1, Rotation::cur());
            rlc = rlc + c_rlp1 * mult.clone();
            mult = mult * branch_acc_r;

            let c_rlp2 = meta.query_advice(c_rlp2, Rotation::cur());
            rlc = rlc + c_rlp2 * mult.clone();
            mult = mult * branch_acc_r;

            for col in c_advices.iter() {
                let c = meta.query_advice(*col, Rotation::cur());
                rlc = rlc + c * mult.clone();
                mult = mult * branch_acc_r;
            }

            let mut constraints = vec![];
            constraints.push((
                q_enable.clone() * rlc,
                meta.query_fixed(keccak_table[0], Rotation::cur()),
            ));
            // NOTE: Rotation -2 can be used here (in S and C leaf), because
            // s_keccak and c_keccak have the same value in all branch rows (thus, the same
            // value in branch node_index: 15 and branch node_index: 14)
            for (ind, column) in sc_keccak.iter().enumerate() {
                let sc_keccak = meta.query_advice(*column, Rotation(-2));
                let keccak_table_i =
                    meta.query_fixed(keccak_table[ind + 1], Rotation::cur());
                constraints
                    .push((q_enable.clone() * sc_keccak, keccak_table_i));
            }

            constraints
        });

        config
    }

    pub fn construct(config: LeafHashConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }
}

impl<F: FieldExt> Chip<F> for LeafHashChip<F> {
    type Config = LeafHashConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}
