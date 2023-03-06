use super::{helpers::MPTConstraintBuilder, MPTContext};
use crate::circuit;
use eth_types::Field;
use halo2_proofs::{plonk::VirtualCells, poly::Rotation};
use std::marker::PhantomData;

#[derive(Clone, Debug)]
pub(crate) struct SelectorsConfig<F> {
    _marker: PhantomData<F>,
}

impl<F: Field> SelectorsConfig<F> {
    pub fn configure(
        meta: &mut VirtualCells<'_, F>,
        cb: &mut MPTConstraintBuilder<F>,
        ctx: MPTContext<F>,
    ) -> Self {
        // It needs to be ensured that:
        // - The selectors denoting the row type are boolean values.
        // - For sets of selectors that are mutually exclusive, it needs to be ensured
        //   that their sum is 1 (for example the selector for the proof type).
        // - The proper order of rows.
        circuit!([meta, cb.base], {
            let q_enable = f!(ctx.q_enable);
            let q_not_first = f!(ctx.q_not_first);

            // Row type selectors
            let row_type_selectors = [
                0.expr(),
                /*is_branch_init.expr(),
                is_branch_child.expr(),
                is_extension_node_s.expr(),
                is_extension_node_c.expr(),
                is_leaf_s_key.expr(),
                is_leaf_c_key.expr(),
                is_leaf_s_value.expr(),
                is_leaf_c_value.expr(),
                is_leaf_in_added_branch.expr(),
                is_non_existing_storage_row.expr(),
                is_account_leaf_key_s.expr(),
                is_account_leaf_key_c.expr(),
                is_non_existing_account_row.expr(),
                is_account_leaf_nonce_balance_s.expr(),
                is_account_leaf_nonce_balance_c.expr(),
                is_account_leaf_storage_codehash_s.expr(),
                is_account_leaf_storage_codehash_c.expr(),
                is_account_leaf_in_added_branch.expr(),*/
            ];
            // Sanity checks on all rows
            ifx! {q_enable => {
                // It needs to be ensured that all selectors are boolean.
                for selector in row_type_selectors.iter()
                {
                    require!(selector => bool);
                }

                // The type of the row needs to be set (if all selectors would be 0 for a row,
                // then all constraints would be switched off).
                //require!(sum::expr(row_type_selectors.iter()) => 1);
            }};

            // First row
            /*ifx! {q_enable, not!(q_not_first) => {
                // In the first row only account leaf key S row or branch init row can occur
                require!(or::expr([is_account_leaf_key_s.cur(), is_branch_init.cur()]) => true);
            }};*/

            // All rows except the first row
            ifx! {q_not_first => {
                // State transitions
                /*let transitions = [
                    // Branch init can start:
                    // - after another branch (means after extension node C)
                    // - after account leaf (account -> storage proof)
                    // - after storage leaf (after storage mod proof ends)
                    // - in the first row
                    (
                        "Last branch row/last storage leaf/last account leaf -> branch init",
                        1.expr(),
                        vec![
                            is_extension_node_c.prev(),
                            is_account_leaf_in_added_branch.prev(),
                            is_leaf_non_existing.prev(),
                        ],
                        is_branch_init.cur(),
                    ),
                    // Account leaf key S can appear after
                    // - extension node C (last branch row)
                    // - the last storage leaf row (if only one account in the trie) and there is
                    //   another proof above it (having last storage leaf row as the last row)
                    (
                        "Last branch row/last storage leaf -> account leaf key S",
                        is_account_leaf_key_s.cur(),
                        vec![is_extension_node_c.prev(), is_leaf_non_existing.prev()],
                        is_account_leaf_key_s.cur(),
                    ),
                    // Storage leaf key S can appear after
                    // - extension node C (last branch row)
                    // - account leaf storage codehash C
                    (
                        "Last branch row/last storage leaf -> account leaf key S",
                        is_leaf_s_key.cur(),
                        vec![
                            is_extension_node_c.prev(),
                            is_account_leaf_in_added_branch.prev(),
                        ],
                        is_leaf_s_key.cur(),
                    ),
                    (
                        "Last branch row -> extension node S",
                        1.expr(),
                        vec![is_last_branch_child.prev()],
                        is_extension_node_s.cur(),
                    ),
                    (
                        "Extension node S -> extension node C",
                        1.expr(),
                        vec![is_extension_node_s.prev()],
                        is_extension_node_c.cur(),
                    ),
                    (
                        "Account leaf key S -> account leaf key C",
                        1.expr(),
                        vec![is_account_leaf_key_s.prev()],
                        is_account_leaf_key_c.cur(),
                    ),
                    (
                        "Account leaf key C -> non existing account row",
                        1.expr(),
                        vec![is_account_leaf_key_c.prev()],
                        is_non_existing_account_row.cur(),
                    ),
                    (
                        "Non existing account row -> account leaf nonce balance S",
                        1.expr(),
                        vec![is_non_existing_account_row.prev()],
                        is_account_leaf_nonce_balance_s.cur(),
                    ),
                    (
                        "Account leaf nonce balance S -> account leaf nonce balance C",
                        1.expr(),
                        vec![is_account_leaf_nonce_balance_s.prev()],
                        is_account_leaf_nonce_balance_c.cur(),
                    ),
                    (
                        "Account leaf nonce balance C -> account leaf storage codehash S",
                        1.expr(),
                        vec![is_account_leaf_nonce_balance_c.prev()],
                        is_account_leaf_storage_codehash_s.cur(),
                    ),
                    (
                        "Account leaf storage codehash S -> account leaf storage codehash C",
                        1.expr(),
                        vec![is_account_leaf_storage_codehash_s.prev()],
                        is_account_leaf_storage_codehash_c.cur(),
                    ),
                    (
                        "Account leaf storage codehash C -> account leaf added in branch",
                        1.expr(),
                        vec![is_account_leaf_storage_codehash_c.prev()],
                        is_account_leaf_in_added_branch.cur(),
                    ),
                    (
                        "Storage leaf key S -> storage leaf value S",
                        1.expr(),
                        vec![is_leaf_s_key.prev()],
                        is_leaf_s_value.cur(),
                    ),
                    (
                        "Storage leaf value S -> storage leaf key C",
                        1.expr(),
                        vec![is_leaf_s_value.prev()],
                        is_leaf_c_key.cur(),
                    ),
                    (
                        "Storage leaf key C -> storage leaf value C",
                        1.expr(),
                        vec![is_leaf_c_key.prev()],
                        is_leaf_c_value.cur(),
                    ),
                    (
                        "Storage leaf value C -> storage leaf in added branch",
                        1.expr(),
                        vec![is_leaf_c_value.prev()],
                        is_leaf_in_added_branch.cur(),
                    ),
                    (
                        "Storage leaf in added branch -> storage leaf non existing row",
                        1.expr(),
                        vec![is_leaf_in_added_branch.prev()],
                        is_leaf_non_existing.cur(),
                    ),
                ];*/
                /*for (name, condition, from, to) in transitions {
                    ifx!{condition => {
                        require!(name, to => from);
                    }}
                }*/
            }}
        });

        SelectorsConfig {
            _marker: PhantomData,
        }
    }
}
