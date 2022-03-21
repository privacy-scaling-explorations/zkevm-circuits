use halo2_proofs::{
    circuit::Chip,
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, Selector, VirtualCells},
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
        q_enable: Selector,
        q_not_first: Column<Fixed>,
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

        // TODO: not_first_level constraints

        meta.create_gate("selectors boolean", |meta| {
            let q_enable = meta.query_selector(q_enable);

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

        meta.create_gate("rows order", |meta| {
            let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());

            let mut constraints = vec![];
            let is_branch_init_cur = meta.query_advice(is_branch_init, Rotation::cur());
            let is_last_branch_child_prev =
                meta.query_advice(is_last_branch_child, Rotation::prev());
            let is_leaf_s_key_prev = meta.query_advice(is_leaf_s_key, Rotation::prev());
            let is_leaf_s_key_cur = meta.query_advice(is_leaf_s_key, Rotation::cur());
            let is_leaf_s_value_prev = meta.query_advice(is_leaf_s_value, Rotation::prev());
            let is_leaf_s_value_cur = meta.query_advice(is_leaf_s_value, Rotation::cur());
            let is_leaf_c_key_prev = meta.query_advice(is_leaf_c_key, Rotation::prev());
            let is_leaf_c_key_cur = meta.query_advice(is_leaf_c_key, Rotation::cur());
            let is_leaf_c_value_prev = meta.query_advice(is_leaf_c_value, Rotation::prev());
            let is_leaf_c_value_cur = meta.query_advice(is_leaf_c_value, Rotation::cur());
            let is_leaf_in_added_branch_prev =
                meta.query_advice(is_leaf_in_added_branch, Rotation::prev());
            let is_leaf_in_added_branch_cur =
                meta.query_advice(is_leaf_in_added_branch, Rotation::cur());

            let is_account_leaf_key_s_prev =
                meta.query_advice(is_account_leaf_key_s, Rotation::prev());
            let is_account_leaf_key_s_cur =
                meta.query_advice(is_account_leaf_key_s, Rotation::cur());
            let is_account_leaf_nonce_balance_s_prev =
                meta.query_advice(is_account_leaf_nonce_balance_s, Rotation::prev());
            let is_account_leaf_nonce_balance_s_cur =
                meta.query_advice(is_account_leaf_nonce_balance_s, Rotation::cur());
            let is_account_leaf_nonce_balance_c_prev =
                meta.query_advice(is_account_leaf_nonce_balance_c, Rotation::prev());
            let is_account_leaf_nonce_balance_c_cur =
                meta.query_advice(is_account_leaf_nonce_balance_c, Rotation::cur());
            let is_account_leaf_storage_codehash_s_prev =
                meta.query_advice(is_account_leaf_storage_codehash_s, Rotation::prev());
            let is_account_leaf_storage_codehash_s_cur =
                meta.query_advice(is_account_leaf_storage_codehash_s, Rotation::cur());
            let is_account_leaf_storage_codehash_c_prev =
                meta.query_advice(is_account_leaf_storage_codehash_c, Rotation::prev());
            let is_account_leaf_storage_codehash_c_cur =
                meta.query_advice(is_account_leaf_storage_codehash_c, Rotation::cur());

            let is_extension_node_s_prev = meta.query_advice(is_extension_node_s, Rotation::prev());
            let is_extension_node_s_cur = meta.query_advice(is_extension_node_s, Rotation::cur());
            let is_extension_node_c_prev = meta.query_advice(is_extension_node_c, Rotation::prev());
            let is_extension_node_c_cur = meta.query_advice(is_extension_node_c, Rotation::cur());

            // Branch init can start after another branch (means after extension node S)
            // or after account leaf storage codehash (account -> storage proof)
            // or after leaf in added branch (after key/value proof ends).
            // Also, it can be in the first row.
            constraints.push((
                "branch init after",
                q_not_first.clone()
                    * (is_branch_init_cur.clone() - is_extension_node_c_prev.clone())
                    * (is_branch_init_cur.clone()
                        - is_account_leaf_storage_codehash_c_prev.clone())
                    * (is_branch_init_cur.clone() - is_leaf_in_added_branch_prev.clone()),
            ));

            // Internal branch selectors are checked in branch.rs.

            // Extension node rows follow branch rows:
            constraints.push((
                "last branch -> extension node S",
                q_not_first.clone() * (is_last_branch_child_prev - is_extension_node_s_cur),
            ));
            constraints.push((
                "extension node S -> extension node C",
                q_not_first.clone() * (is_extension_node_s_prev - is_extension_node_c_cur),
            ));

            // Account leaf:
            constraints.push((
                "account leaf key follows extension node C",
                q_not_first.clone()
                // if this is in the first row (leaf without branch), the constraint is still ok
                    * (is_extension_node_c_prev.clone() - is_account_leaf_key_s_cur.clone())
                    * is_account_leaf_key_s_cur.clone(),
            ));
            constraints.push((
                "account leaf key -> account leaf nonce balance S",
                q_not_first.clone()
                    * (is_account_leaf_key_s_prev - is_account_leaf_nonce_balance_s_cur),
            ));
            constraints.push((
                "account leaf nonce balance S -> account leaf nonce balance C",
                q_not_first.clone()
                    * (is_account_leaf_nonce_balance_s_prev - is_account_leaf_nonce_balance_c_cur),
            ));
            constraints.push((
                "account leaf nonce balance C -> account leaf storage codehash S",
                q_not_first.clone()
                    * (is_account_leaf_nonce_balance_c_prev
                        - is_account_leaf_storage_codehash_s_cur),
            ));
            constraints.push((
                "account leaf storage codehash S -> account leaf storage codehash C",
                q_not_first.clone()
                    * (is_account_leaf_storage_codehash_s_prev
                        - is_account_leaf_storage_codehash_c_cur),
            ));

            // Storage leaf
            constraints.push((
                "storage leaf key follows extension node C or account leaf storage codehash c",
                q_not_first.clone()
                    * (is_extension_node_c_prev - is_leaf_s_key_cur.clone())
                    * (is_account_leaf_storage_codehash_c_prev - is_leaf_s_key_cur.clone()) // when storage leaf without branch
                    * is_leaf_s_key_cur,
            ));
            constraints.push((
                "leaf key S -> leaf value S",
                q_not_first.clone() * (is_leaf_s_key_prev - is_leaf_s_value_cur),
            ));
            constraints.push((
                "leaf value S -> leaf key C",
                q_not_first.clone() * (is_leaf_s_value_prev - is_leaf_c_key_cur),
            ));
            constraints.push((
                "leaf key C -> leaf value C",
                q_not_first.clone() * (is_leaf_c_key_prev - is_leaf_c_value_cur),
            ));
            constraints.push((
                "leaf value C -> leaf in added branch",
                q_not_first.clone() * (is_leaf_c_value_prev - is_leaf_in_added_branch_cur),
            ));

            // Note that these constraints do not prevent attacks like putting account leaf
            // rows more than once - however, doing this would lead into failure
            // of the constraints responsible for address (or storage if storage
            // rows are added) RLC.
            // However, we need to ensure the account leaf and storage leaf are added for
            // each storage modification. This is still to be implemented
            // (TODO), it could be this way: there will be a selector (probably set to 1
            // in an additional row right after the last storage leaf row)
            // needed to enable lookup for each storage modification - we could
            // add a boolean column where the sum of is_account_leaf_storage_codecash_c
            // would be computed and it would need to be 1 when the
            // above-mentioned selector would be enabled. In the row after this,
            // the sum would need to be set to 0 again. Similarly, the sum of
            // is_leaf_in_added_branch_cur would be checked to be 1.

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
