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
        address_rlc: Column<Advice>,
        counter: Column<Advice>,
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

            let address_rlc_prev = meta.query_advice(address_rlc, Rotation::prev());
            let address_rlc_cur = meta.query_advice(address_rlc, Rotation::cur());

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
            // then not_first_level needs to be 1 in the current row (preventing two consecutive
            // blocks to be not_first_level = 0).
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
                    * (one.clone() - not_first_level_cur.clone())
                    * (one.clone() - is_leaf_in_added_branch_prev),
            ));
 
            // These two address_rlc constraints are to ensure there is account proof before the
            // storage proof.
            constraints.push((
                // First row of first level can be (besides branch_init) also is_account_leaf_key_s,
                // but in this case the constraint in account_leaf_key.rs is triggered.
                "address_rlc is 0 in first row of first level",
                q_not_first.clone()
                    * (one.clone() - not_first_level_cur.clone())
                    * is_branch_init.clone()
                    * address_rlc_cur.clone()
            ));
            constraints.push((
                "address_rlc does not change except at is_account_leaf_key_s or branch init in first level",
                q_not_first.clone()
                    * (one.clone() - is_account_leaf_key_s.clone())
                    * (is_branch_init.clone() - not_first_level_cur.clone() - one.clone()) // address_rlc goes back to 0 in branch init in first level
                    * (address_rlc_cur.clone() - address_rlc_prev.clone())
            ));

            // counter does not change except when a new modification proof starts
            let counter_prev = meta.query_advice(counter, Rotation::prev());
            let counter_cur = meta.query_advice(counter, Rotation::cur());
            constraints.push((
                "counter does not change outside first level",
                q_not_first.clone()
                    * not_first_level_cur.clone()
                    * (counter_cur.clone() - counter_prev.clone())
            ));
            constraints.push((
                "counter does not change inside first level except in the first row",
                q_not_first.clone()
                    * (one.clone() - not_first_level_cur.clone())
                    * (one.clone() - is_branch_init.clone())
                    * (one.clone() - is_account_leaf_key_s.clone())
                    * (counter_cur.clone() - counter_prev.clone())
            ));

            constraints.push((
                "counter increases by 1 in first row in first level (branch)",
                q_not_first.clone()
                    * (one.clone() - not_first_level_cur.clone())
                    * is_branch_init.clone()
                    * (counter_cur.clone() - counter_prev.clone() - one.clone())
            ));
            constraints.push((
                "counter increases by 1 in first row in first level (account leaf)",
                q_not_first.clone()
                    * (one.clone() - not_first_level_cur.clone())
                    * is_account_leaf_key_s.clone()
                    * (counter_cur.clone() - counter_prev.clone() - one)
            ));


            // TODO: check public roots to match with first and last inter roots

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
