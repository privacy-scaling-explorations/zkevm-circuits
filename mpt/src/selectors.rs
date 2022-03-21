use halo2_proofs::{
    circuit::Chip,
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, VirtualCells},
    poly::Rotation,
};
use pairing::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::helpers::get_bool_constraint;

#[derive(Clone, Debug)]
pub(crate) struct SelectorsConfig {}

// Ensures selectors are booleans. Ensures the proper order of rows.
pub(crate) struct SelectorsChip<F> {
    config: SelectorsConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> SelectorsChip<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: impl Fn(&mut VirtualCells<'_, F>) -> Expression<F>,
        is_branch_init: Column<Advice>,
        is_branch_child: Column<Advice>,
        is_last_branch_child: Column<Advice>,
        is_leaf_s_key: Column<Advice>,
        is_leaf_s_value: Column<Advice>,
        is_leaf_c_key: Column<Advice>,
        is_leaf_c_value: Column<Advice>,
        is_account_leaf_key_s: Column<Advice>,
        is_account_leaf_nonce_balance_s: Column<Advice>,
        is_account_leaf_nonce_balance_c: Column<Advice>,
        is_account_leaf_storage_codehash_s: Column<Advice>,
        is_account_leaf_storage_codehash_c: Column<Advice>,
        is_leaf_in_added_branch: Column<Advice>,
        is_extension_node_s: Column<Advice>,
        is_extension_node_c: Column<Advice>,
        sel1: Column<Advice>,
        sel2: Column<Advice>,
        is_modified: Column<Advice>,
        is_at_first_nibble: Column<Advice>,
    ) -> SelectorsConfig {
        let config = SelectorsConfig {};

        // TODO: q_not_first and not_first_level constraints

        meta.create_gate("selectors", |meta| {
            let q_enable = q_enable(meta);

            let one = Expression::Constant(F::one());

            let mut constraints = vec![];
            let is_branch_init_cur = meta.query_advice(is_branch_init, Rotation::cur());
            let is_branch_child_cur = meta.query_advice(is_branch_child, Rotation::cur());
            let is_last_branch_child_cur = meta.query_advice(is_last_branch_child, Rotation::cur());
            let is_leaf_s_key = meta.query_advice(is_leaf_s_key, Rotation::cur());
            let is_leaf_s_value = meta.query_advice(is_leaf_s_value, Rotation::cur());
            let is_leaf_c_key = meta.query_advice(is_leaf_c_key, Rotation::cur());
            let is_leaf_c_value = meta.query_advice(is_leaf_c_value, Rotation::cur());

            let is_account_leaf_key_s = meta.query_advice(is_account_leaf_key_s, Rotation::cur());
            let is_account_leaf_nonce_balance_s =
                meta.query_advice(is_account_leaf_nonce_balance_s, Rotation::cur());
            let is_account_leaf_nonce_balance_c =
                meta.query_advice(is_account_leaf_nonce_balance_c, Rotation::cur());
            let is_account_leaf_storage_codehash_s =
                meta.query_advice(is_account_leaf_storage_codehash_s, Rotation::cur());

            let is_account_leaf_storage_codehash_c =
                meta.query_advice(is_account_leaf_storage_codehash_c, Rotation::cur());
            let sel1 = meta.query_advice(sel1, Rotation::cur());
            let sel2 = meta.query_advice(sel2, Rotation::cur());

            constraints.push((
                "bool check is_branch_init",
                get_bool_constraint(q_enable.clone(), is_branch_init_cur.clone()),
            ));
            constraints.push((
                "bool check is_branch_child",
                get_bool_constraint(q_enable.clone(), is_branch_child_cur.clone()),
            ));
            constraints.push((
                "bool check is_last branch_child",
                get_bool_constraint(q_enable.clone(), is_last_branch_child_cur.clone()),
            ));
            constraints.push((
                "bool check is_leaf_s",
                get_bool_constraint(q_enable.clone(), is_leaf_s_key.clone()),
            ));
            constraints.push((
                "bool check is_leaf_c",
                get_bool_constraint(q_enable.clone(), is_leaf_c_key.clone()),
            ));
            constraints.push((
                "bool check is_leaf_s_value",
                get_bool_constraint(q_enable.clone(), is_leaf_s_value.clone()),
            ));
            constraints.push((
                "bool check is_leaf_c_value",
                get_bool_constraint(q_enable.clone(), is_leaf_c_value.clone()),
            ));
            constraints.push((
                "bool check is_account_leaf_key_s",
                get_bool_constraint(q_enable.clone(), is_account_leaf_key_s.clone()),
            ));
            constraints.push((
                "bool check is_account_nonce_balance_s",
                get_bool_constraint(q_enable.clone(), is_account_leaf_nonce_balance_s.clone()),
            ));
            constraints.push((
                "bool check is_account_nonce_balance_c",
                get_bool_constraint(q_enable.clone(), is_account_leaf_nonce_balance_c.clone()),
            ));
            constraints.push((
                "bool check is_account_storage_codehash_s",
                get_bool_constraint(q_enable.clone(), is_account_leaf_storage_codehash_s.clone()),
            ));
            constraints.push((
                "bool check is_account_storage_codehash_c",
                get_bool_constraint(q_enable.clone(), is_account_leaf_storage_codehash_c.clone()),
            ));
            constraints.push((
                "bool check branch sel1",
                get_bool_constraint(q_enable.clone() * is_branch_child_cur.clone(), sel1.clone()),
            ));
            constraints.push((
                "bool check branch sel2",
                get_bool_constraint(q_enable.clone() * is_branch_child_cur, sel2.clone()),
            ));

            // In branch children, it can be sel1 + sel2 = 0 too - this
            // case is checked separately.

            // TODO order: is_last_branch_child followed by is_leaf_s followed by is_leaf_c
            // followed by is_leaf_key_nibbles
            // is_leaf_s_value ..., is_extension_node_s, is_extension_node_c,
            // is_leaf_in_added_branch ...

            // TODO: account leaf constraints (order and also that account leaf selectors
            // are true only in account proof part & normal leaf selectors are true only
            // in storage part, for this we also need account proof selector and storage
            // proof selector - bool and strictly increasing for example. Also,
            // is_account_leaf_key_nibbles needs to be 1 in the previous row
            // when the account/storage selector changes.

            // TODO: constraints for s_advices[IS_ADD_BRANCH_S_POS - LAYOUT_OFFSET]
            // and s_advices[IS_ADD_BRANCH_C_POS - LAYOUT_OFFSET] in branch init

            let is_modified = meta.query_advice(is_modified, Rotation::cur());
            let is_at_first_nibble = meta.query_advice(is_at_first_nibble, Rotation::cur());
            let is_leaf_in_added_branch =
                meta.query_advice(is_leaf_in_added_branch, Rotation::cur());
            let is_extension_node_s = meta.query_advice(is_extension_node_s, Rotation::cur());
            let is_extension_node_c = meta.query_advice(is_extension_node_c, Rotation::cur());

            constraints.push((
                "bool check is_modified",
                get_bool_constraint(q_enable.clone(), is_modified.clone()),
            ));
            constraints.push((
                "bool check is_at_first_nibble",
                get_bool_constraint(q_enable.clone(), is_at_first_nibble.clone()),
            ));
            constraints.push((
                "bool check is_leaf_in_added_branch",
                get_bool_constraint(q_enable.clone(), is_leaf_in_added_branch.clone()),
            ));
            constraints.push((
                "bool check is_extension_node_s",
                get_bool_constraint(q_enable.clone(), is_extension_node_s.clone()),
            ));
            constraints.push((
                "bool check is_extension_node_c",
                get_bool_constraint(q_enable.clone(), is_extension_node_c.clone()),
            ));

            constraints
        });

        config
    }

    pub fn construct(config: SelectorsConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }
}

impl<F: FieldExt> Chip<F> for SelectorsChip<F> {
    type Config = SelectorsConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}
