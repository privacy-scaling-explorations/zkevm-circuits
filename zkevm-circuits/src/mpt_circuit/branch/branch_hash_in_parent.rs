use halo2_proofs::{
    plonk::{Advice, Column, ConstraintSystem, Expression},
    poly::Rotation,
    arithmetic::FieldExt,
};
use std::marker::PhantomData;

use crate::{
    mpt_circuit::columns::{AccumulatorCols, MainCols, PositionCols},
    mpt_circuit::helpers::{bytes_expr_into_rlc, get_is_extension_node},
    mpt_circuit::{param::{
        ACCOUNT_LEAF_ROWS, ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND,
        ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND, IS_BRANCH_C_PLACEHOLDER_POS,
        IS_BRANCH_S_PLACEHOLDER_POS, IS_C_BRANCH_NON_HASHED_POS, IS_S_BRANCH_NON_HASHED_POS, RLP_NUM, BRANCH_0_S_START, BRANCH_0_C_START,
    }, helpers::get_branch_len}, table::KeccakTable,
};

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
        let config = BranchHashInParentConfig {
            _marker: PhantomData,
        };
        let one = Expression::Constant(F::from(1_u64));
        let rot_into_branch_init = -16;

        /*
        When branch is in the first level of the account trie, we need to check whether
        `hash(branch) = account_trie_root`. We do this by checking whether
        `(branch_RLC, account_trie_root_RLC)` is in the keccak table.

        Note: branch in the first level cannot be shorter than 32 bytes (it is always hashed).
        */
        meta.lookup_any(
            "Branch in first level of account trie - hash compared to root",
            |meta| {
                let q_not_first = meta.query_fixed(position_cols.q_not_first, Rotation::cur());
                let not_first_level = meta.query_advice(position_cols.not_first_level, Rotation::cur());

                let is_last_branch_child = meta.query_advice(is_last_branch_child, Rotation::cur());

                let mut is_branch_placeholder = meta.query_advice(
                    s_main.bytes[IS_BRANCH_S_PLACEHOLDER_POS - RLP_NUM],
                    Rotation(-16),
                );
                if !is_s {
                    is_branch_placeholder = meta.query_advice(
                        s_main.bytes[IS_BRANCH_C_PLACEHOLDER_POS - RLP_NUM],
                        Rotation(-16),
                    );
                }

                let is_extension_node = get_is_extension_node(meta, s_main.bytes, -16);

                let mut acc_pair = accs.clone().acc_s;
                if !is_s {
                    acc_pair = accs.clone().acc_c;
                }

                // TODO: acc currently doesn't have branch ValueNode info (which 128 if nil)
                let acc = meta.query_advice(acc_pair.rlc, Rotation::cur());
                let c128 = Expression::Constant(F::from(128));
                let mult = meta.query_advice(acc_pair.mult, Rotation::cur());
                let branch_acc = acc + c128 * mult;

                let root = meta.query_advice(inter_root, Rotation::cur());

                let selector = q_not_first.clone()
                    * is_last_branch_child.clone()
                    * (one.clone() - is_extension_node.clone())
                    * (one.clone() - not_first_level.clone())
                    * (one.clone() - is_branch_placeholder.clone());
                
                let branch_len = get_branch_len(meta, s_main.clone(), rot_into_branch_init, is_s);
                                
                let mut table_map = Vec::new();
                let keccak_is_enabled = meta.query_advice(keccak_table.is_enabled, Rotation::cur());
                table_map.push((selector.clone(), keccak_is_enabled));

                let keccak_input_rlc = meta.query_advice(keccak_table.input_rlc, Rotation::cur());
                table_map.push((selector.clone() * branch_acc, keccak_input_rlc));

                let keccak_input_len = meta.query_advice(keccak_table.input_len, Rotation::cur());
                table_map.push((selector.clone() * branch_len, keccak_input_len));

                let keccak_output_rlc = meta.query_advice(keccak_table.output_rlc, Rotation::cur());
                table_map.push((selector.clone() * root, keccak_output_rlc));

                table_map
            },
        );

        /*
        When branch is in the first level of the storage trie, we need to check whether
        `hash(branch) = storage_trie_root`. We do this by checking whether
        `(branch_RLC, storage_trie_root_RLC)` is in the keccak table.

        Note: branch in the first level cannot be shorter than 32 bytes (it is always hashed).
        */
        meta.lookup_any(
            "Branch in first level of storage trie - hash compared to the storage root",
            |meta| {
                // Note: we are in the same row (last branch child) for S and C.
                let not_first_level = meta.query_advice(position_cols.not_first_level, Rotation::cur());
                let mut is_branch_placeholder = meta.query_advice(
                    s_main.bytes[IS_BRANCH_S_PLACEHOLDER_POS - RLP_NUM],
                    Rotation(rot_into_branch_init),
                );
                if !is_s {
                    is_branch_placeholder = meta.query_advice(
                        s_main.bytes[IS_BRANCH_C_PLACEHOLDER_POS - RLP_NUM],
                        Rotation(rot_into_branch_init),
                    );
                }

                // Only check if there is an account above the leaf.
                let is_account_leaf_in_added_branch = meta.query_advice(
                    is_account_leaf_in_added_branch,
                    Rotation(rot_into_branch_init - 1),
                );

                let is_extension_node =
                    get_is_extension_node(meta, s_main.bytes, rot_into_branch_init);

                // We need to do the lookup only if we are in the last branch child.
                let is_last_branch_child = meta.query_advice(is_last_branch_child, Rotation::cur());

                let mut acc = meta.query_advice(accs.acc_s.rlc, Rotation::cur());
                if !is_s {
                    acc = meta.query_advice(accs.acc_c.rlc, Rotation::cur());
                }

                // TODO: acc currently doesn't have branch ValueNode info (which 128 if nil)
                let c128 = Expression::Constant(F::from(128));
                let mut mult = meta.query_advice(accs.acc_s.mult, Rotation::cur());
                if !is_s {
                    mult = meta.query_advice(accs.acc_c.mult, Rotation::cur());
                }
                let branch_acc = acc + c128 * mult; // TODO: replace with acc once ValueNode is added

                let mut sc_hash = vec![];
                // Note: storage root is always in s_main.bytes.
                for column in s_main.bytes.iter() {
                    if is_s {
                        sc_hash.push(meta.query_advice(
                            *column,
                            Rotation(
                                rot_into_branch_init
                                    - (ACCOUNT_LEAF_ROWS - ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND),
                            ),
                        ));
                    } else {
                        sc_hash.push(meta.query_advice(
                            *column,
                            Rotation(
                                rot_into_branch_init
                                    - (ACCOUNT_LEAF_ROWS - ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND),
                            ),
                        ));
                    }
                }
                let hash_rlc = bytes_expr_into_rlc(&sc_hash, randomness);

                let selector = not_first_level.clone()
                    * (one.clone() - is_extension_node.clone())
                    * is_last_branch_child.clone()
                    * is_account_leaf_in_added_branch.clone()
                    * (one.clone() - is_branch_placeholder.clone());

                let branch_len = get_branch_len(meta, s_main.clone(), rot_into_branch_init, is_s);

                let mut table_map = Vec::new();
                let keccak_is_enabled = meta.query_advice(keccak_table.is_enabled, Rotation::cur());
                table_map.push((selector.clone(), keccak_is_enabled));

                let keccak_input_rlc = meta.query_advice(keccak_table.input_rlc, Rotation::cur());
                table_map.push((selector.clone() * branch_acc, keccak_input_rlc));

                let keccak_input_len = meta.query_advice(keccak_table.input_len, Rotation::cur());
                table_map.push((selector.clone() * branch_len, keccak_input_len));

                let keccak_output_rlc = meta.query_advice(keccak_table.output_rlc, Rotation::cur());
                table_map.push((selector.clone() * hash_rlc, keccak_output_rlc));

                table_map
            },
        );

        /*
        This is the scenario described at the top of the file.
        When branch is in some other branch, we need to check whether
        `hash(branch) = parent_branch_modified_node`. We do this by checking whether
        `(branch_RLC, parent_branch_modified_node_RLC)` is in the Keccak table.
        */
        meta.lookup_any("Branch hash in parent branch", |meta| {
            let not_first_level = meta.query_advice(position_cols.not_first_level, Rotation::cur());

            // -17 because we are in the last branch child (-16 takes us to branch init)
            let is_account_leaf_in_added_branch_prev =
                meta.query_advice(is_account_leaf_in_added_branch, Rotation(-17));

            // We need to do the lookup only if we are in the last branch child.
            let is_last_branch_child = meta.query_advice(is_last_branch_child, Rotation::cur());

            // When placeholder branch, we don't check its hash in a parent.
            let mut is_branch_placeholder = meta.query_advice(
                s_main.bytes[IS_BRANCH_S_PLACEHOLDER_POS - RLP_NUM],
                Rotation(-16),
            );
            if !is_s {
                is_branch_placeholder = meta.query_advice(
                    s_main.bytes[IS_BRANCH_C_PLACEHOLDER_POS - RLP_NUM],
                    Rotation(-16),
                );
            }

            let mut is_branch_non_hashed = meta.query_advice(
                s_main.bytes[IS_S_BRANCH_NON_HASHED_POS - RLP_NUM],
                Rotation(-16),
            );
            if !is_s {
                is_branch_non_hashed = meta.query_advice(
                    s_main.bytes[IS_C_BRANCH_NON_HASHED_POS - RLP_NUM],
                    Rotation(-16),
                );
            }

            let is_extension_node = get_is_extension_node(meta, s_main.bytes, -16);

            let mut acc_pair = accs.clone().acc_s;
            if !is_s {
                acc_pair = accs.clone().acc_c;
            }

            // TODO: acc currently doesn't have branch ValueNode info (which 128 if nil)
            let acc = meta.query_advice(acc_pair.rlc, Rotation::cur());
            let c128 = Expression::Constant(F::from(128));
            let mult = meta.query_advice(acc_pair.mult, Rotation::cur());
            let branch_acc = acc + c128 * mult;

            let selector = not_first_level.clone()
                * is_last_branch_child.clone()
                * (one.clone() - is_account_leaf_in_added_branch_prev.clone()) // we don't check this in the first storage level
                * (one.clone() - is_branch_placeholder.clone())
                * (one.clone() - is_branch_non_hashed.clone())
                * (one.clone() - is_extension_node.clone());

            let mut mod_node_hash_rlc = accs.clone().s_mod_node_rlc;
            if !is_s {
                mod_node_hash_rlc = accs.c_mod_node_rlc;
            }

            // Any rotation that lands into branch can be used instead of -19.
            let mod_node_hash_rlc_cur = meta.query_advice(mod_node_hash_rlc, Rotation(-19));

            let branch_len = get_branch_len(meta, s_main.clone(), rot_into_branch_init, is_s);

            let mut table_map = Vec::new();
            let keccak_is_enabled = meta.query_advice(keccak_table.is_enabled, Rotation::cur());
            table_map.push((selector.clone(), keccak_is_enabled));

            let keccak_input_rlc = meta.query_advice(keccak_table.input_rlc, Rotation::cur());
            table_map.push((selector.clone() * branch_acc, keccak_input_rlc));

            let keccak_input_len = meta.query_advice(keccak_table.input_len, Rotation::cur());
            table_map.push((selector.clone() * branch_len, keccak_input_len));

            let keccak_output_rlc = meta.query_advice(keccak_table.output_rlc, Rotation::cur());
            table_map.push((selector.clone() * mod_node_hash_rlc_cur, keccak_output_rlc));

            table_map            
        });

        /*
        Similar as the gate above, but here the branch is not hashed.
        Instead of checking `hash(branch) = parent_branch_modified_node`, we check whether
        `branch_RLC = parent_branch_modified_node_RLC`.
        */
        meta.create_gate("NON-HASHED branch hash in parent branch", |meta| {
            let q_not_first = meta.query_fixed(position_cols.q_not_first, Rotation::cur());
            let not_first_level = meta.query_advice(position_cols.not_first_level, Rotation::cur());

            // -17 because we are in the last branch child (-16 takes us to branch init)
            let is_account_leaf_in_added_branch_prev =
                meta.query_advice(is_account_leaf_in_added_branch, Rotation(-17));

            // We need to do the lookup only if we are in the last branch child.
            let is_last_branch_child = meta.query_advice(is_last_branch_child, Rotation::cur());

            // When placeholder branch, we don't check its hash in a parent.
            let mut is_branch_placeholder = meta.query_advice(
                s_main.bytes[IS_BRANCH_S_PLACEHOLDER_POS - RLP_NUM],
                Rotation(-16),
            );
            if !is_s {
                is_branch_placeholder = meta.query_advice(
                    s_main.bytes[IS_BRANCH_C_PLACEHOLDER_POS - RLP_NUM],
                    Rotation(-16),
                );
            }

            let mut is_branch_non_hashed = meta.query_advice(
                s_main.bytes[IS_S_BRANCH_NON_HASHED_POS - RLP_NUM],
                Rotation(-16),
            );
            if !is_s {
                is_branch_non_hashed = meta.query_advice(
                    s_main.bytes[IS_C_BRANCH_NON_HASHED_POS - RLP_NUM],
                    Rotation(-16),
                );
            }

            let is_extension_node = get_is_extension_node(meta, s_main.bytes, -16);

            let mut acc_pair = accs.clone().acc_s;
            if !is_s {
                acc_pair = accs.clone().acc_c;
            }

            // TODO: acc currently doesn't have branch ValueNode info (which 128 if nil)
            let acc = meta.query_advice(acc_pair.rlc, Rotation::cur());
            let c128 = Expression::Constant(F::from(128));
            let mult = meta.query_advice(acc_pair.mult, Rotation::cur());
            let branch_acc = acc + c128 * mult;

            let mut constraints = vec![];

            let mut mod_node_hash_rlc = accs.s_mod_node_rlc;
            if !is_s {
                mod_node_hash_rlc = accs.c_mod_node_rlc;
            }

            let mod_node_hash_rlc_cur = meta.query_advice(mod_node_hash_rlc, Rotation(-19));
            constraints.push((
                "Non-hashed branch in branch",
                q_not_first
                    * not_first_level
                    * is_last_branch_child
                    * (one.clone()
                        - is_account_leaf_in_added_branch_prev) // we don't check this in the first storage level
                    * (one.clone() - is_branch_placeholder)
                    * is_branch_non_hashed
                    * (one - is_extension_node)
                    * (mod_node_hash_rlc_cur - branch_acc),
            ));

            constraints
        });

        config
    }
}
