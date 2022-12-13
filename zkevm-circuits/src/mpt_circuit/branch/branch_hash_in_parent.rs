use halo2_proofs::{
    arithmetic::FieldExt,
    plonk::{Advice, Column, ConstraintSystem, Expression},
    poly::Rotation,
};
use std::marker::PhantomData;

use crate::{
    cs,
    mpt_circuit::columns::{AccumulatorCols, MainCols, PositionCols},
    mpt_circuit::helpers::{bytes_expr_into_rlc, get_is_extension_node},
    mpt_circuit::{
        helpers::{get_branch_len, BaseConstraintBuilder},
        param::{
            ACCOUNT_LEAF_ROWS, ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND,
            ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND, IS_BRANCH_C_PLACEHOLDER_POS,
            IS_BRANCH_S_PLACEHOLDER_POS, IS_C_BRANCH_NON_HASHED_POS, IS_S_BRANCH_NON_HASHED_POS,
            RLP_NUM,
        },
    },
    table::KeccakTable,
};
use gadgets::util::{and, not, sum, Expr};

/*
A branch occupies 19 rows:
BRANCH.IS_INIT
BRANCH.IS_CHILD 0
...
BRANCH.IS_CHILD 15
BRANCH.IS_EXTENSION_NODE_S
BRANCH.IS_EXTENSION_NODE_C

Example:

[1 0 1 0 248 241 0 248 241 0 1 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0]
[0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1]
[0 160 164 92 78 34 81 137 173 236 78 208 145 118 128 60 46 5 176 8 229 165 42 222 110 4 252 228 93 243 26 160 241 85 0 160 95 174 59 239 229 74 221 53 227 115 207 137 94 29 119 126 56 209 55 198 212 179 38 213 219 36 111 62 46 43 176 168 1]
[0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1]
[0 160 60 157 212 182 167 69 206 32 151 2 14 23 149 67 58 187 84 249 195 159 106 68 203 199 199 65 194 33 215 102 71 138 0 160 60 157 212 182 167 69 206 32 151 2 14 23 149 67 58 187 84 249 195 159 106 68 203 199 199 65 194 33 215 102 71 138 1]
[0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1]
[0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1]
[0 160 21 230 18 20 253 84 192 151 178 53 157 0 9 105 229 121 222 71 120 109 159 109 9 218 254 1 50 139 117 216 194 252 0 160 21 230 18 20 253 84 192 151 178 53 157 0 9 105 229 121 222 71 120 109 159 109 9 218 254 1 50 139 117 216 194 252 1]
[0 160 229 29 220 149 183 173 68 40 11 103 39 76 251 20 162 242 21 49 103 245 160 99 143 218 74 196 2 61 51 34 105 123 0 160 229 29 220 149 183 173 68 40 11 103 39 76 251 20 162 242 21 49 103 245 160 99 143 218 74 196 2 61 51 34 105 123 1]
[0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1]
[0 160 0 140 67 252 58 164 68 143 34 163 138 133 54 27 218 38 80 20 142 115 221 100 73 161 165 75 83 53 8 58 236 1 0 160 0 140 67 252 58 164 68 143 34 163 138 133 54 27 218 38 80 20 142 115 221 100 73 161 165 75 83 53 8 58 236 1 1]
[0 160 149 169 206 0 129 86 168 48 42 127 100 73 109 90 171 56 216 28 132 44 167 14 46 189 224 213 37 0 234 165 140 236 0 160 149 169 206 0 129 86 168 48 42 127 100 73 109 90 171 56 216 28 132 44 167 14 46 189 224 213 37 0 234 165 140 236 1]
[0 160 42 63 45 28 165 209 201 220 231 99 153 208 48 174 250 66 196 18 123 250 55 107 64 178 159 49 190 84 159 179 138 235 0 160 42 63 45 28 165 209 201 220 231 99 153 208 48 174 250 66 196 18 123 250 55 107 64 178 159 49 190 84 159 179 138 235 1]
[0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1]
[0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1]
[0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1]
[0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1]
[0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 16]
[0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 17]

The constraints in this file check whether the RLC of the whole branch is in its parent node
at the proper position. The RLC is computed over the first 17 rows (the last 2 rows are reserved
for the cases when the parent of the branch is an extension node).

Let us say we have the following situation:

Branch1:
  node1_0       node3_0_RLC
  ...           node3_0_RLC
  node1_15      node3_0_RLC
Branch2
  node2_0
  ...
  node2_15

Let us say we are checking `Branch2` to be at the proper position in `Branch1`.
We compute `Branch2` RLC (the constraints for ensuring the proper RLC computation are in `branch_rlc.rs`).
Let us say the `modified_node = 3` in `Branch1`. That means there is `node3_0_RLC` stored in all 16
rows. We need to check that `(Branch2_RLC, node3_0_RLC)` is in the Keccak table which would mean
that `hash(Branch2) = node3_0`.
*/

#[derive(Clone, Debug)]
pub(crate) struct BranchHashInParentConfig<F> {
    _marker: PhantomData<F>,
}

impl<F: FieldExt> BranchHashInParentConfig<F> {
    #[allow(clippy::too_many_arguments)]
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        inter_root: Column<Advice>,
        position_cols: PositionCols<F>,
        is_account_leaf_in_added_branch: Column<Advice>,
        is_last_branch_child: Column<Advice>,
        s_main: MainCols<F>,
        accs: AccumulatorCols<F>,
        keccak_table: KeccakTable,
        randomness: Expression<F>,
        is_s: bool,
    ) -> Self {
        let rot_into_branch_init = -16;

        struct LookupData<F> {
            selector: Expression<F>,
            input_rlc: Expression<F>,
            length: Expression<F>,
            output_rlc: Expression<F>,
        }

        let mut lookups = Vec::new();
        meta.create_gate("Branch hash in parent", |meta| {
            let q_not_first = meta.query_fixed(position_cols.q_not_first, Rotation::cur());
            let not_first_level = meta.query_advice(position_cols.not_first_level, Rotation::cur());
            let is_last_branch_child = meta.query_advice(is_last_branch_child, Rotation::cur());
            // When placeholder branch, we don't check its hash in a parent.
            let is_branch_placeholder_pos = if is_s {IS_BRANCH_S_PLACEHOLDER_POS} else {IS_BRANCH_C_PLACEHOLDER_POS};
            let is_branch_placeholder = meta.query_advice(
                s_main.bytes[is_branch_placeholder_pos - RLP_NUM],
                Rotation(-16),
            );
            // Only check if there is an account above the leaf.
            // -17 because we are in the last branch child (-16 takes us to branch init).
            let is_account_leaf_in_added_branch = meta.query_advice(
                is_account_leaf_in_added_branch,
                Rotation(rot_into_branch_init - 1),
            );
            let is_branch_non_hashed_pos = if is_s {IS_S_BRANCH_NON_HASHED_POS} else {IS_C_BRANCH_NON_HASHED_POS};
            let is_branch_non_hashed = meta.query_advice(
                s_main.bytes[is_branch_non_hashed_pos - RLP_NUM],
                Rotation(-16),
            );
            let is_extension_node = get_is_extension_node(meta, s_main.bytes, -16);
            let branch_length = get_branch_len(meta, s_main.clone(), rot_into_branch_init, is_s);
            // TODO: acc currently doesn't have branch ValueNode info (which 128 if nil)
            let acc_pair = if is_s {accs.clone().acc_s} else {accs.clone().acc_c};
            let branch_acc = meta.query_advice(acc_pair.rlc, Rotation::cur()) + 128.expr() * meta.query_advice(acc_pair.mult, Rotation::cur());
            let mod_node_hash_rlc = if is_s { accs.clone().s_mod_node_rlc } else { accs.c_mod_node_rlc };
            // Any rotation that lands into branch can be used instead of -19.
            let mod_node_hash_rlc = meta.query_advice(mod_node_hash_rlc, Rotation(-19));

            let mut cb = BaseConstraintBuilder::default();
            cs!{[cb],
            ifx(and::expr([is_last_branch_child, not::expr(is_extension_node), not::expr(is_branch_placeholder)])) {
                cs!{[cb],
                ifx(not_first_level) {
                    // Whether to check this in the first storage level
                    cs!{[cb],
                    ifx(is_account_leaf_in_added_branch) {
                        /* Branch in first level of storage trie - hash compared to the storage root */
                        // When branch is in the first level of the storage trie, we need to check whether
                        // - `hash(branch) = storage_trie_root`. We do this by checking whether
                        // - `(branch_RLC, storage_trie_root_RLC)` is in the keccak table.
                        // Note: branch in the first level cannot be shorter than 32 bytes (it is always hashed).
                        let storage_index = if is_s {ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND} else {ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND};
                        let rot = Rotation(rot_into_branch_init - (ACCOUNT_LEAF_ROWS - storage_index));
                        // Note: storage root is always in s_main.bytes.
                        let sc_hash = s_main.bytes.iter().map(|c| meta.query_advice(*c, rot)).collect::<Vec<_>>();
                        lookups.push(LookupData {
                            selector: cb.get_condition(),
                            input_rlc: branch_acc.expr(),
                            length: branch_length.expr(),
                            output_rlc: bytes_expr_into_rlc(&sc_hash, randomness.expr()),
                        });
                    } elsex {
                        cs!{[cb],
                        ifx(is_branch_non_hashed) {
                            cs!{[cb],
                            ifx(q_not_first) {
                                /* NON-HASHED branch hash in parent branch */
                                // Similar as the gate above, but here the branch is not hashed.
                                // Instead of checking `hash(branch) = parent_branch_modified_node`, we check whether
                                // `branch_RLC = parent_branch_modified_node_RLC`.
                                cb.require_equal(
                                    "Non-hashed branch in branch",
                                    mod_node_hash_rlc.expr(),
                                    branch_acc.expr(),
                                );
                            }}
                        } elsex {
                            /* Branch hash in parent branch */
                            // This is the scenario described at the top of the file.
                            // When branch is in some other branch, we need to check whether
                            // - `hash(branch) = parent_branch_modified_node`. We do this by checking whether
                            // - `(branch_RLC, parent_branch_modified_node_RLC)` is in the Keccak table.
                            // When placeholder branch, we don't check its hash in a parent.
                            lookups.push(LookupData {
                                selector: cb.get_condition(),
                                input_rlc: branch_acc.expr(),
                                length: branch_length.expr(),
                                output_rlc: mod_node_hash_rlc.expr(),
                            });
                        }}
                    }}
                } elsex {
                    cs!{[cb],
                    ifx(q_not_first) {
                        /* Branch in first level of account trie - hash compared to root */
                        // When branch is in the first level of the account trie, we need to check whether
                        // `hash(branch) = account_trie_root`. We do this by checking whether
                        // `(branch_RLC, account_trie_root_RLC)` is in the keccak table.
                        // Note: branch in the first level cannot be shorter than 32 bytes (it is always hashed).
                        lookups.push(LookupData {
                            selector: cb.get_condition(),
                            input_rlc: branch_acc.expr(),
                            length: branch_length.expr(),
                            output_rlc: meta.query_advice(inter_root, Rotation::cur()),
                        });
                    }}
                }}
            }};

            cb.gate(1.expr())
        });

        // Hash lookups
        meta.lookup_any("Hash lookup", |meta| {
            let selector = sum::expr(lookups.iter().map(|lookup| lookup.selector.expr()));
            let input_rlc = sum::expr(
                lookups
                    .iter()
                    .map(|lookup| lookup.selector.expr() * lookup.input_rlc.expr()),
            );
            let length = sum::expr(
                lookups
                    .iter()
                    .map(|lookup| lookup.selector.expr() * lookup.length.expr()),
            );
            let output_rlc = sum::expr(
                lookups
                    .iter()
                    .map(|lookup| lookup.selector.expr() * lookup.output_rlc.expr()),
            );

            let mut table_map = Vec::new();
            let keccak_is_enabled = meta.query_advice(keccak_table.is_enabled, Rotation::cur());
            table_map.push((selector.clone(), keccak_is_enabled));

            let keccak_input_rlc = meta.query_advice(keccak_table.input_rlc, Rotation::cur());
            table_map.push((input_rlc, keccak_input_rlc));

            let keccak_input_len = meta.query_advice(keccak_table.input_len, Rotation::cur());
            table_map.push((length, keccak_input_len));

            let keccak_output_rlc = meta.query_advice(keccak_table.output_rlc, Rotation::cur());
            table_map.push((output_rlc, keccak_output_rlc));

            table_map
        });

        BranchHashInParentConfig {
            _marker: PhantomData,
        }
    }
}
