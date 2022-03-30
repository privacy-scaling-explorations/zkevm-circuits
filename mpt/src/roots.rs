use halo2_proofs::{
    circuit::Chip,
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, Selector, VirtualCells},
    poly::Rotation,
};
use pairing::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::helpers::get_bool_constraint;

#[derive(Clone, Debug)]
pub(crate) struct RootsConfig {}

// Ensures selectors are booleans. Ensures the proper order of rows.
pub(crate) struct RootsChip<F> {
    config: RootsConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> RootsChip<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_not_first: Column<Fixed>,
        switch_proof: Column<Advice>,
        inter_start_root: Column<Advice>,
        inter_final_root: Column<Advice>,
    ) -> RootsConfig {
        let config = RootsConfig {};

        meta.create_gate("roots", |meta| {
            let mut constraints = vec![];

            let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
            let switch_proof = meta.query_advice(switch_proof, Rotation::cur());

            let start_root_prev = meta.query_advice(inter_start_root, Rotation::prev());
            let start_root_cur = meta.query_advice(inter_start_root, Rotation::cur());
            let final_root_prev = meta.query_advice(inter_final_root, Rotation::prev());
            let final_root_cur = meta.query_advice(inter_final_root, Rotation::cur());

            let one = Expression::Constant(F::one());

            constraints.push((
                "start_root does not change when switch_proof = 0",
                q_not_first.clone()
                    * (one.clone() - switch_proof.clone())
                    * (start_root_cur.clone() - start_root_prev.clone()),
            ));

            constraints.push((
                "final_root does not change when switch_proof = 0",
                q_not_first.clone()
                    * (one - switch_proof.clone())
                    * (final_root_cur.clone() - final_root_prev.clone()),
            ));

            constraints.push((
                "final_root_prev = start_root_cur when switch_proof = 1",
                q_not_first.clone()
                    * switch_proof.clone()
                    * (final_root_prev.clone() - start_root_cur.clone()),
            ));

            constraints
        });

        config
    }

    pub fn construct(config: RootsConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }
}

impl<F: FieldExt> Chip<F> for RootsChip<F> {
    type Config = RootsConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}
