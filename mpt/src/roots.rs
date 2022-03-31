use halo2_proofs::{
    circuit::Chip,
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed},
    poly::Rotation,
};
use pairing::arithmetic::FieldExt;
use std::marker::PhantomData;

#[derive(Clone, Debug)]
pub(crate) struct RootsConfig {}

// Constraints for roots and not_first_level selector.
pub(crate) struct RootsChip<F> {
    config: RootsConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> RootsChip<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: Column<Fixed>,
        q_not_first: Column<Fixed>,
        not_first_level: Column<Advice>,
        is_leaf_in_added_branch: Column<Advice>,
        is_branch_init: Column<Advice>,
        is_account_leaf_key_s: Column<Advice>,
        inter_start_root: Column<Advice>,
        inter_final_root: Column<Advice>,
    ) -> RootsConfig {
        let config = RootsConfig {};

        meta.create_gate("roots", |meta| {
            let mut constraints = vec![];

            let q_enable = meta.query_fixed(q_enable, Rotation::cur());
            let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
            let not_first_level_prev = meta.query_advice(not_first_level, Rotation::prev());
            let not_first_level_cur = meta.query_advice(not_first_level, Rotation::cur());
            let is_branch_init = meta.query_advice(is_branch_init, Rotation::cur());
            let is_account_leaf_key_s = meta.query_advice(is_account_leaf_key_s, Rotation::cur());
            let is_leaf_in_added_branch_prev = meta.query_advice(is_leaf_in_added_branch, Rotation::prev());

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

            constraints.push((
                "first row needs to have not_first_level = 0 if is_account_leaf_key",
                q_enable.clone() * is_account_leaf_key_s.clone() * (one.clone() - q_not_first.clone()) * not_first_level_cur.clone(),
            ));

            constraints.push((
                "first row needs to have not_first_level = 0 if is_branch_init",
                q_enable.clone() * (one.clone() - q_not_first.clone()) * is_branch_init.clone() * not_first_level_cur.clone(),
            ));

            // If not_first_level is 0 in a previous row (being in branch init),
            // it needs to be 1 in current row (preventing two consecutive blocks to
            // be not_first_level).
            constraints.push((
                "not_first_level 0 -> 1 in branch init",
                q_not_first.clone()
                    * is_branch_init.clone()
                    * (one.clone() - not_first_level_prev.clone())
                    * (not_first_level_cur.clone() - one.clone()),
            ));

            // Note that not_first_level can change in is_branch_init or is_account_leaf.
            // The attacker could thus insert more first levels, but there will be counter
            // for storage modifications which will prevent this. Still, the attacker
            // could potentially put first levels at wrong places, but then address/key
            // RLC constraints would fail.
            constraints.push((
                "not_first_level doesn't change except at is_branch_init or is_account_leaf",
                q_not_first.clone()
                    * (one.clone() - is_branch_init.clone())
                    * (one.clone() - is_account_leaf_key_s.clone())
                    * (not_first_level_cur.clone() - not_first_level_prev.clone()),
            )); 

            // If not_first_level is 0 in is_branch_init,
            // then is_leaf_in_added_branch_prev = 1.
            constraints.push((
                "not_first_level = 0 follows is_account_leaf_storage_codehash_c_prev = 1",
                q_not_first.clone() // for the first row, we already have a constraint for not_first_level = 0
                    * is_branch_init.clone()
                    * (one.clone() - not_first_level_cur.clone())
                    * (one.clone() - is_leaf_in_added_branch_prev.clone()),
            ));

            // If not_first_level is 0 in is_account_leaf,
            // then is_leaf_in_added_branch_prev = 1.
            constraints.push((
                "not_first_level = 0 follows is_account_leaf_storage_codehash_c_prev = 1",
                q_not_first.clone() // for the first row, we already have a constraint for not_first_level = 0
                    * is_account_leaf_key_s.clone()
                    * (one.clone() - not_first_level_cur)
                    * (one - is_leaf_in_added_branch_prev),
            ));

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
