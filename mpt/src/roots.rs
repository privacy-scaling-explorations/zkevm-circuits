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
        not_first_level: Column<Advice>,
        is_branch_init: Column<Advice>,
        is_account_leaf_key_s: Column<Advice>,
        inter_start_root: Column<Advice>,
        inter_final_root: Column<Advice>,
    ) -> RootsConfig {
        let config = RootsConfig {};

        meta.create_gate("roots", |meta| {
            let mut constraints = vec![];

            let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
            let not_first_level_prev = meta.query_advice(not_first_level, Rotation::prev());
            let not_first_level_cur = meta.query_advice(not_first_level, Rotation::cur());
            let is_branch_init = meta.query_advice(is_branch_init, Rotation::cur());
            let is_account_leaf_key_s = meta.query_advice(is_account_leaf_key_s, Rotation::cur());

            let start_root_prev = meta.query_advice(inter_start_root, Rotation::prev());
            let start_root_cur = meta.query_advice(inter_start_root, Rotation::cur());
            let final_root_prev = meta.query_advice(inter_final_root, Rotation::prev());
            let final_root_cur = meta.query_advice(inter_final_root, Rotation::cur());

            let one = Expression::Constant(F::one());

            constraints.push((
                "start_root does not change when not in first level",
                q_not_first.clone()
                    * not_first_level_cur.clone()
                    * (start_root_cur.clone() - start_root_prev.clone()),
            ));

            constraints.push((
                "start_root does not change when in first level and (not in account leaf key || not in branch init)",
                q_not_first.clone()
                    * (one.clone() - not_first_level_cur.clone())
                    * (one.clone() - is_branch_init.clone())
                    * (one.clone() - is_account_leaf_key_s.clone())
                    * (start_root_cur.clone() - start_root_prev.clone()),
            ));

            constraints.push((
                "final_root does not change when not in first level",
                q_not_first.clone()
                    * not_first_level_cur.clone()
                    * (final_root_cur.clone() - final_root_prev.clone()),
            ));

            constraints.push((
                "final_root does not change when in first level and (not in account leaf key || not in branch init)",
                q_not_first.clone()
                    * (one.clone() - not_first_level_cur.clone())
                    * (one.clone() - is_branch_init.clone())
                    * (one.clone() - is_account_leaf_key_s.clone())
                    * (final_root_cur.clone() - final_root_prev.clone()),
            ));

            constraints.push((
                "final_root_prev = start_root_cur when not_first_level = 1 -> not_first_level = 0",
                q_not_first.clone()
                    * not_first_level_prev.clone()
                    * (one.clone() - not_first_level_cur.clone())
                    * (final_root_prev.clone() - start_root_cur.clone()),
            ));

            /*
            constraints.push((
                "not_first_level doesn't change except at is_branch_init or is_account_leaf",
                q_not_first.clone()
                    * (one.clone() - is_branch_init.clone())
                    * (one.clone() - is_account_leaf_key_s.clone())
                    * (not_first_level_cur.clone() - not_first_level_prev.clone()),
            ));
            */

            // TODO:
            // if !not_first_level: key_rlc = 0 ... -
            // proof variables have to be checked to be reset when a new proof starts

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
