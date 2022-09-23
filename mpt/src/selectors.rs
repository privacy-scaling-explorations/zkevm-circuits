use halo2_proofs::{
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed},
    poly::Rotation,
};
use pairing::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::{
    account_leaf::AccountLeafCols,
    branch::BranchCols,
    columns::{DenoteCols, ProofTypeCols, PositionCols},
    helpers::get_bool_constraint,
    storage_leaf::StorageLeafCols,
};

/*
It needs to be ensured:
 - The selectors denoting the row type are boolean values.
 - For sets of selectors that are mutually exclusive, it needs to be ensured that
   their sum is 1 (for example the selector for the proof type).
 - The proper order of rows.
*/

#[derive(Clone, Debug)]
pub(crate) struct SelectorsConfig<F> {
    _marker: PhantomData<F>,
}

impl<F: FieldExt> SelectorsConfig<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        proof_type: ProofTypeCols<F>,
        position_cols: PositionCols<F>,
        branch: BranchCols<F>,
        account_leaf: AccountLeafCols<F>,
        storage_leaf: StorageLeafCols<F>,
        denoter: DenoteCols<F>,
    ) -> Self {
        let config = SelectorsConfig {
            _marker: PhantomData,
        };
        let one = Expression::Constant(F::one());

        meta.create_gate("selectors boolean", |meta| {
            let q_enable = meta.query_fixed(position_cols.q_enable, Rotation::cur());
            let mut constraints = vec![];

            let not_first_level = meta.query_advice(position_cols.not_first_level, Rotation::cur());
            let is_branch_init_cur = meta.query_advice(branch.is_init, Rotation::cur());
            let is_branch_child_cur = meta.query_advice(branch.is_child, Rotation::cur());
            let is_last_branch_child_cur = meta.query_advice(branch.is_last_child, Rotation::cur());
            let is_leaf_s_key = meta.query_advice(storage_leaf.is_s_key, Rotation::cur());
            let is_leaf_s_value = meta.query_advice(storage_leaf.is_s_value, Rotation::cur());
            let is_leaf_c_key = meta.query_advice(storage_leaf.is_c_key, Rotation::cur());
            let is_leaf_c_value = meta.query_advice(storage_leaf.is_c_value, Rotation::cur());

            let is_account_leaf_key_s = meta.query_advice(account_leaf.is_key_s, Rotation::cur());
            let is_account_leaf_key_c = meta.query_advice(account_leaf.is_key_c, Rotation::cur());
            let is_non_existing_account_row = meta.query_advice(account_leaf.is_non_existing_account_row, Rotation::cur());
            let is_account_leaf_nonce_balance_s =
                meta.query_advice(account_leaf.is_nonce_balance_s, Rotation::cur());
            let is_account_leaf_nonce_balance_c =
                meta.query_advice(account_leaf.is_nonce_balance_c, Rotation::cur());
            let is_account_leaf_storage_codehash_s =
                meta.query_advice(account_leaf.is_storage_codehash_s, Rotation::cur());
            let is_account_leaf_storage_codehash_c =
                meta.query_advice(account_leaf.is_storage_codehash_c, Rotation::cur());
            let is_account_leaf_in_added_branch =
                meta.query_advice(account_leaf.is_in_added_branch, Rotation::cur());

            let is_leaf_in_added_branch =
                meta.query_advice(storage_leaf.is_in_added_branch, Rotation::cur());
            let is_extension_node_s = meta.query_advice(branch.is_extension_node_s, Rotation::cur());
            let is_extension_node_c = meta.query_advice(branch.is_extension_node_c, Rotation::cur());

            let sel1 = meta.query_advice(denoter.sel1, Rotation::cur());
            let sel2 = meta.query_advice(denoter.sel2, Rotation::cur());

            let is_storage_mod = meta.query_advice(proof_type.is_storage_mod, Rotation::cur());
            let is_nonce_mod = meta.query_advice(proof_type.is_nonce_mod, Rotation::cur());
            let is_balance_mod = meta.query_advice(proof_type.is_balance_mod, Rotation::cur());
            let is_codehash_mod = meta.query_advice(proof_type.is_codehash_mod, Rotation::cur());
            let is_account_delete_mod = meta.query_advice(proof_type.is_account_delete_mod, Rotation::cur());
            let is_non_existing_account_proof = meta.query_advice(proof_type.is_non_existing_account_proof, Rotation::cur());

            let is_modified = meta.query_advice(branch.is_modified, Rotation::cur());
            let is_at_drifted_pos = meta.query_advice(branch.is_at_drifted_pos, Rotation::cur());

            /*
            The type of the row needs to be set (if all selectors would be 0 for a row, then all constraints
            would be switched off).
            */
            constraints.push((
                "Type of the row is set",
                q_enable.clone() 
                * (is_branch_init_cur.clone() + is_branch_child_cur.clone()
                    + is_extension_node_s.clone() + is_extension_node_c.clone()
                    + is_leaf_s_key.clone() + is_leaf_c_key.clone() + is_leaf_s_value.clone() + is_leaf_c_value.clone()
                    + is_leaf_in_added_branch.clone()
                    + is_account_leaf_key_s.clone() + is_account_leaf_key_c.clone()
                    + is_non_existing_account_row.clone()
                    + is_account_leaf_nonce_balance_s.clone() + is_account_leaf_nonce_balance_c.clone()
                    + is_account_leaf_storage_codehash_s.clone() + is_account_leaf_storage_codehash_c.clone()
                    + is_account_leaf_in_added_branch.clone()
                    - one.clone())
            ));

            /*
            It needs to be ensured that all selectors are boolean. To trigger the constraints for
            a specific row the selectors could be of any nonnegative value, but being booleans
            it makes it easier to write the constraints that ensure the subsets of constraints are
            mutually exclusive and the constraints to ensure the proper order of rows.
            */
            constraints.push((
                "bool check not_first_level",
                get_bool_constraint(q_enable.clone(), not_first_level),
            ));
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
                "bool check is_account_leaf_key_c",
                get_bool_constraint(q_enable.clone(), is_account_leaf_key_c.clone()),
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
                "bool check is_account_leaf_in_added_branch",
                get_bool_constraint(q_enable.clone(), is_account_leaf_in_added_branch.clone()),
            ));
            constraints.push((
                "bool check branch sel1",
                get_bool_constraint(q_enable.clone() * is_branch_child_cur.clone(), sel1.clone()),
            ));
            constraints.push((
                "bool check branch sel2",
                get_bool_constraint(q_enable.clone() * is_branch_child_cur, sel2.clone()),
            )); 
            constraints.push((
                "bool check is_modified",
                get_bool_constraint(q_enable.clone(), is_modified.clone()),
            ));
            constraints.push((
                "bool check is_at_drifted_pos",
                get_bool_constraint(q_enable.clone(), is_at_drifted_pos.clone()),
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

            constraints.push((
                "bool check is_storage_mod",
                get_bool_constraint(q_enable.clone(), is_storage_mod.clone()),
            ));
            constraints.push((
                "bool check is_nonce_mod",
                get_bool_constraint(q_enable.clone(), is_nonce_mod.clone()),
            ));
            constraints.push((
                "bool check is_balance_mod",
                get_bool_constraint(q_enable.clone(), is_balance_mod.clone()),
            ));
            constraints.push((
                "bool check is_codehash_mode",
                get_bool_constraint(q_enable.clone(), is_codehash_mod.clone()),
            ));
            constraints.push((
                "bool check is_account_delete_mod",
                get_bool_constraint(q_enable.clone(), is_account_delete_mod.clone()),
            ));
            constraints.push((
                "bool check is_non_existing_account_row",
                get_bool_constraint(q_enable.clone(), is_non_existing_account_row.clone()),
            ));
            constraints.push((
                "bool check is_non_existing_account_proof",
                get_bool_constraint(q_enable.clone(), is_non_existing_account_proof.clone()),
            )); 

            /*
            The type of the proof needs to be set.
            */
            constraints.push((
                "is_storage_mod + is_nonce_mod + is_balance_mod + is_account_delete_mod + is_non_existing_account + is_codehash_mod = 1",
                q_enable.clone()
                    * (is_storage_mod + is_nonce_mod + is_balance_mod + is_account_delete_mod + is_non_existing_account_proof + is_codehash_mod
                        - one.clone()),
            ));

            constraints
        });

        meta.create_gate(
            "Rows order ensured & proof type cannot change in rows corresponding to one modification",
            |meta| {
                let q_not_first = meta.query_fixed(position_cols.q_not_first, Rotation::cur());
                let mut constraints = vec![];

                let is_branch_init_cur = meta.query_advice(branch.is_init, Rotation::cur());
                let is_last_branch_child_prev =
                    meta.query_advice(branch.is_last_child, Rotation::prev());
                let is_leaf_s_key_prev = meta.query_advice(storage_leaf.is_s_key, Rotation::prev());
                let is_leaf_s_key_cur = meta.query_advice(storage_leaf.is_s_key, Rotation::cur());
                let is_leaf_s_value_prev = meta.query_advice(storage_leaf.is_s_value, Rotation::prev());
                let is_leaf_s_value_cur = meta.query_advice(storage_leaf.is_s_value, Rotation::cur());
                let is_leaf_c_key_prev = meta.query_advice(storage_leaf.is_c_key, Rotation::prev());
                let is_leaf_c_key_cur = meta.query_advice(storage_leaf.is_c_key, Rotation::cur());
                let is_leaf_c_value_prev = meta.query_advice(storage_leaf.is_c_value, Rotation::prev());
                let is_leaf_c_value_cur = meta.query_advice(storage_leaf.is_c_value, Rotation::cur());
                let is_leaf_in_added_branch_prev =
                    meta.query_advice(storage_leaf.is_in_added_branch, Rotation::prev());
                let is_leaf_in_added_branch_cur =
                    meta.query_advice(storage_leaf.is_in_added_branch, Rotation::cur());

                let is_account_leaf_key_s_prev =
                    meta.query_advice(account_leaf.is_key_s, Rotation::prev());
                let is_account_leaf_key_s_cur =
                    meta.query_advice(account_leaf.is_key_s, Rotation::cur());
                let is_account_leaf_key_c_prev =
                    meta.query_advice(account_leaf.is_key_c, Rotation::prev());
                let is_account_leaf_key_c_cur =
                    meta.query_advice(account_leaf.is_key_c, Rotation::cur());
                let is_account_leaf_nonce_balance_s_prev =
                    meta.query_advice(account_leaf.is_nonce_balance_s, Rotation::prev());
                let is_account_leaf_nonce_balance_s_cur =
                    meta.query_advice(account_leaf.is_nonce_balance_s, Rotation::cur());
                let is_account_leaf_nonce_balance_c_prev =
                    meta.query_advice(account_leaf.is_nonce_balance_c, Rotation::prev());
                let is_account_leaf_nonce_balance_c_cur =
                    meta.query_advice(account_leaf.is_nonce_balance_c, Rotation::cur());
                let is_account_leaf_storage_codehash_s_prev =
                    meta.query_advice(account_leaf.is_storage_codehash_s, Rotation::prev());
                let is_account_leaf_storage_codehash_s_cur =
                    meta.query_advice(account_leaf.is_storage_codehash_s, Rotation::cur());
                let is_account_leaf_storage_codehash_c_prev =
                    meta.query_advice(account_leaf.is_storage_codehash_c, Rotation::prev());
                let is_account_leaf_storage_codehash_c_cur =
                    meta.query_advice(account_leaf.is_storage_codehash_c, Rotation::cur());
                let is_account_leaf_in_added_branch_prev =
                    meta.query_advice(account_leaf.is_in_added_branch, Rotation::prev());
                let is_account_leaf_in_added_branch_cur =
                    meta.query_advice(account_leaf.is_in_added_branch, Rotation::cur());

                let is_extension_node_s_prev =
                    meta.query_advice(branch.is_extension_node_s, Rotation::prev());
                let is_extension_node_s_cur =
                    meta.query_advice(branch.is_extension_node_s, Rotation::cur());
                let is_extension_node_c_prev =
                    meta.query_advice(branch.is_extension_node_c, Rotation::prev());
                let is_extension_node_c_cur =
                    meta.query_advice(branch.is_extension_node_c, Rotation::cur());

                let is_non_existing_account_row_prev =
                    meta.query_advice(account_leaf.is_non_existing_account_row, Rotation::prev());
                let is_non_existing_account_row_cur =
                    meta.query_advice(account_leaf.is_non_existing_account_row, Rotation::cur());

                /*
                Branch init can start:
                 - after another branch (means after extension node C)
                 - after account leaf (account -> storage proof)
                 - after storage leaf (after storage mod proof ends)
                 - it can be in the first row.
                */
                constraints.push((
                    "Branch init can appear only after certain row types",
                    q_not_first.clone()
                        * (is_branch_init_cur.clone() - is_extension_node_c_prev.clone()) // after branch
                        * (is_branch_init_cur.clone()
                            - is_account_leaf_in_added_branch_prev.clone()) // after account leaf
                        * (is_branch_init_cur.clone() - is_leaf_in_added_branch_prev.clone()), // after storage leaf
                ));

                // Internal branch selectors (`is_init`, `is_last_child`) are checked in `branch.rs`.

                /*
                Extension node S row follows the last branch row.
                */
                constraints.push((
                    "Last branch row -> extension node S",
                    q_not_first.clone() * (is_last_branch_child_prev - is_extension_node_s_cur),
                ));

                /*
                Extension node C row follows the extension node S row.
                */
                constraints.push((
                    "Extension node S -> extension node C",
                    q_not_first.clone() * (is_extension_node_s_prev - is_extension_node_c_cur),
                ));

                /*
                Account leaf key S can appear after extension node C (last branch row) or after
                the last storage leaf row (if only one account in the trie).
                */
                constraints.push((
                    "Account leaf key S can appear only after certain row types",
                    q_not_first.clone()
                    * (is_leaf_in_added_branch_cur.clone() - is_account_leaf_key_s_cur.clone())
                    * (is_extension_node_c_prev.clone() - is_account_leaf_key_s_cur.clone())
                    * is_account_leaf_key_s_cur.clone(), // this is to check it only when we are in the account leaf key S
                ));

                /*
                Account leaf key C can appear only after account leaf key S.
                */
                constraints.push((
                    "Account leaf key S -> account leaf key C",
                    q_not_first.clone() * (is_account_leaf_key_s_prev - is_account_leaf_key_c_cur),
                ));

                /*
                Non existing account row can appear only after account leaf key C row.
                */
                constraints.push((
                    "Account leaf key C -> non existing account row",
                    q_not_first.clone()
                        * (is_account_leaf_key_c_prev - is_non_existing_account_row_cur),
                ));

                /*
                Account leaf nonce balance S row can appear only after non existing account row.
                */
                constraints.push((
                    "Non existing account row -> account leaf nonce balance S",
                    q_not_first.clone()
                        * (is_non_existing_account_row_prev - is_account_leaf_nonce_balance_s_cur),
                ));

                /*
                Account leaf nonce balance C row can appear only after account leaf nonce balance S row. 
                */
                constraints.push((
                    "Account leaf nonce balance S -> account leaf nonce balance C",
                    q_not_first.clone()
                        * (is_account_leaf_nonce_balance_s_prev
                            - is_account_leaf_nonce_balance_c_cur),
                ));

                /*
                Account leaf storage codehash S row can appear only after account leaf nonce balance C row. 
                */
                constraints.push((
                    "Account leaf nonce balance C -> account leaf storage codehash S",
                    q_not_first.clone()
                        * (is_account_leaf_nonce_balance_c_prev
                            - is_account_leaf_storage_codehash_s_cur),
                ));

                /*
                Account leaf storage codehash C row can appear only after account leaf storage codehash S row. 
                */
                constraints.push((
                    "Account leaf storage codehash S -> account leaf storage codehash C",
                    q_not_first.clone()
                        * (is_account_leaf_storage_codehash_s_prev
                            - is_account_leaf_storage_codehash_c_cur),
                ));

                /*
                Account leaf in added branch row can appear only after account leaf storage codehash C row. 
                */
                constraints.push((
                    "Account leaf storage codehash C -> account leaf added in branch",
                    q_not_first.clone()
                        * (is_account_leaf_storage_codehash_c_prev
                            - is_account_leaf_in_added_branch_cur),
                ));

                /*
                Storage leaf key S row can appear after extension node C row or after account leaf storage
                codehash C.
                */
                constraints.push((
                    "Storage leaf key S follows extension node C or account leaf storage codehash C",
                    q_not_first.clone()
                    * (is_extension_node_c_prev - is_leaf_s_key_cur.clone())
                    * (is_account_leaf_in_added_branch_prev - is_leaf_s_key_cur.clone()) // when storage leaf without branch
                    * is_leaf_s_key_cur,
                ));

                /*
                Storage leaf value S row can appear only after storage leaf key S row.
                */
                constraints.push((
                    "Storage leaf key S -> storage leaf value S",
                    q_not_first.clone() * (is_leaf_s_key_prev - is_leaf_s_value_cur),
                ));

                /*
                Storage leaf key C row can appear only after storage leaf value S row.
                */
                constraints.push((
                    "Storage leaf value S -> storage leaf key C",
                    q_not_first.clone() * (is_leaf_s_value_prev - is_leaf_c_key_cur),
                ));

                /*
                Storage leaf value C row can appear only after storage leaf key C row.
                */
                constraints.push((
                    "Storage leaf key C -> storage leaf value C",
                    q_not_first.clone() * (is_leaf_c_key_prev - is_leaf_c_value_cur),
                ));

                /*
                Storage leaf in added branch row can appear only after storage leaf value C row.
                */
                constraints.push((
                    "Storage leaf value C -> storage leaf in added branch",
                    q_not_first.clone() * (is_leaf_c_value_prev - is_leaf_in_added_branch_cur),
                ));

                let q_enable = meta.query_fixed(position_cols.q_enable, Rotation::cur());
                /*
                In the first row only account leaf key S row or branch init row can occur.
                */
                constraints.push((
                    "In the first row only certain row types can occur",
                    q_enable.clone() // without this (1 - q_not_first) = 1 after the proof ends
                    * (one.clone() - q_not_first.clone())
                    * (one.clone() - is_account_leaf_key_s_cur.clone())
                    * (one.clone() - is_branch_init_cur.clone()),
                ));

                /*
                Note that these constraints do not prevent attacks like putting account leaf
                rows more than once - however, doing this would lead into failure
                of the constraints responsible for address RLC (or key RLC if storage rows).
                Also, these constraints do not guarantee there is an account proof before
                storage proof - constraints for this are implemented using address_rlc column
                to be changed to the proper value only in the account leaf key row.
                */

                let is_storage_mod_prev = meta.query_advice(proof_type.is_storage_mod, Rotation::prev());
                let is_storage_mod_cur = meta.query_advice(proof_type.is_storage_mod, Rotation::cur());
                let is_nonce_mod_prev = meta.query_advice(proof_type.is_nonce_mod, Rotation::prev());
                let is_nonce_mod_cur = meta.query_advice(proof_type.is_nonce_mod, Rotation::cur());
                let is_balance_mod_prev = meta.query_advice(proof_type.is_balance_mod, Rotation::prev());
                let is_balance_mod_cur = meta.query_advice(proof_type.is_balance_mod, Rotation::cur());
                let is_codehash_mod_prev = meta.query_advice(proof_type.is_codehash_mod, Rotation::prev());
                let is_codehash_mod_cur = meta.query_advice(proof_type.is_codehash_mod, Rotation::cur());
                let is_account_delete_mod_prev = meta.query_advice(proof_type.is_account_delete_mod, Rotation::prev());
                let is_account_delete_mod_cur = meta.query_advice(proof_type.is_account_delete_mod, Rotation::cur());
                let is_non_existing_account_proof_cur = meta.query_advice(proof_type.is_non_existing_account_proof, Rotation::prev());
                let is_non_existing_account_proof_prev = meta.query_advice(proof_type.is_non_existing_account_proof, Rotation::cur());

                let not_first_level = meta.query_advice(position_cols.not_first_level, Rotation::cur());

                /*
                The following constraints ensure that the proof type does not change except in the first row
                of the first level.
                */
                constraints.push((
                    "is_storage_mod does not change outside first level",
                    q_not_first.clone()
                        * not_first_level.clone()
                        * (is_storage_mod_cur.clone() - is_storage_mod_prev.clone()),
                ));
                constraints.push((
                    "is_storage_mod does not change inside first level except in the first row",
                    q_not_first.clone()
                        * (one.clone() - not_first_level.clone())
                        * (one.clone() - is_branch_init_cur.clone())
                        * (one.clone() - is_account_leaf_key_s_cur.clone())
                        * (is_storage_mod_cur - is_storage_mod_prev),
                ));

                constraints.push((
                    "is_nonce_mod does not change outside first level",
                    q_not_first.clone()
                        * not_first_level.clone()
                        * (is_nonce_mod_cur.clone() - is_nonce_mod_prev.clone()),
                ));
                constraints.push((
                    "is_nonce_mod does not change inside first level except in the first row",
                    q_not_first.clone()
                        * (one.clone() - not_first_level.clone())
                        * (one.clone() - is_branch_init_cur.clone())
                        * (one.clone() - is_account_leaf_key_s_cur.clone())
                        * (is_nonce_mod_cur - is_nonce_mod_prev),
                ));

                constraints.push((
                    "is_balance_mod does not change outside first level",
                    q_not_first.clone()
                        * not_first_level.clone()
                        * (is_balance_mod_cur.clone() - is_balance_mod_prev.clone()),
                ));
                constraints.push((
                    "is_balance_mod does not change inside first level except in the first row",
                    q_not_first.clone()
                        * (one.clone() - not_first_level.clone())
                        * (one.clone() - is_branch_init_cur.clone())
                        * (one.clone() - is_account_leaf_key_s_cur.clone())
                        * (is_balance_mod_cur - is_balance_mod_prev),
                ));

                constraints.push((
                    "is_codehash_mod does not change outside first level",
                    q_not_first.clone()
                        * not_first_level.clone()
                        * (is_codehash_mod_cur.clone() - is_codehash_mod_prev.clone()),
                ));
                constraints.push((
                    "is_codehash_mod does not change inside first level except in the first row",
                    q_not_first.clone()
                        * (one.clone() - not_first_level.clone())
                        * (one.clone() - is_branch_init_cur.clone())
                        * (one.clone() - is_account_leaf_key_s_cur.clone())
                        * (is_codehash_mod_cur - is_codehash_mod_prev),
                ));

                constraints.push((
                    "is_account_delete_mod does not change outside first level",
                    q_not_first.clone()
                        * not_first_level.clone()
                        * (is_account_delete_mod_cur.clone() - is_account_delete_mod_prev.clone()),
                ));
                constraints.push((
                    "is_account_delete_mod does not change inside first level except in the first row",
                    q_not_first.clone()
                        * (one.clone() - not_first_level.clone())
                        * (one.clone() - is_branch_init_cur.clone())
                        * (one.clone() - is_account_leaf_key_s_cur.clone())
                        * (is_account_delete_mod_cur - is_account_delete_mod_prev),
                ));

                constraints.push((
                    "is_non_existing_account does not change outside first level",
                    q_not_first.clone()
                        * not_first_level.clone()
                        * (is_non_existing_account_proof_cur.clone() - is_non_existing_account_proof_prev.clone()),
                ));
                constraints.push((
                    "is_account_delete_mod does not change inside first level except in the first row",
                    q_not_first.clone()
                        * (one.clone() - not_first_level.clone())
                        * (one.clone() - is_branch_init_cur.clone())
                        * (one.clone() - is_account_leaf_key_s_cur.clone())
                        * (is_non_existing_account_proof_cur.clone() - is_non_existing_account_proof_prev.clone()),
                ));

                constraints
            },
        );

        config
    }
}
