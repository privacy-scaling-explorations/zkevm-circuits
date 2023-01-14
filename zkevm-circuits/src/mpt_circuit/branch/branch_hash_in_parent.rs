use halo2_proofs::{arithmetic::FieldExt, plonk::VirtualCells, poly::Rotation};
use std::marker::PhantomData;

use crate::{
    circuit,
    evm_circuit::util::rlc,
    mpt_circuit::param::{
        ACCOUNT_LEAF_ROWS, ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND,
        ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND, ARITY, EXTENSION_ROWS_NUM,
    },
    mpt_circuit::{
        helpers::{BranchNodeInfo, MPTConstraintBuilder},
        MPTContext,
    },
};
use gadgets::util::{not, Expr};

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
    pub fn configure(
        meta: &mut VirtualCells<'_, F>,
        cb: &mut MPTConstraintBuilder<F>,
        ctx: MPTContext<F>,
        is_s: bool,
    ) -> Self {
        let rot_branch_init = -(ARITY as i32);
        // Any rotation that lands into branch can be used
        let rot_branch_child_prev = rot_branch_init - EXTENSION_ROWS_NUM - 1;
        circuit!([meta, cb.base], {
            let branch = BranchNodeInfo::new(meta, ctx.s_main, is_s, rot_branch_init);
            // When placeholder branch, we don't check its hash in a parent.
            // Extension node is handled in `extension_node.rs`.
            ifx! {not!(branch.is_extension()), not!(branch.is_placeholder()) => {
                // TODO: acc currently doesn't have branch ValueNode info (which 128 if nil)
                let acc = ctx.accumulators.acc(is_s);
                let branch_rlc = rlc::expr(
                    &[a!(acc.rlc), 128.expr()],
                    &[a!(acc.mult)],
                );
                ifx!{a!(ctx.position_cols.not_first_level) => {
                    // Only check if there is an account above the leaf.
                    // rot_into_branch_init - 1 because we are in the last branch child
                    // (rot_into_branch_init takes us to branch init).
                    ifx!{a!(ctx.account_leaf.is_in_added_branch, rot_branch_init - 1) => {
                        /* Branch in first level of storage trie - hash compared to the storage root */
                        // When a branch is in the first level of the storage trie, we need to check whether
                        // the branch hash matches the storage root.
                        // Note: A branch in the first level cannot be shorter than 32 bytes (it is always hashed).
                        let storage_offset = if is_s {ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND} else {ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND};
                        let rot_into_storage_root = rot_branch_init - ACCOUNT_LEAF_ROWS + storage_offset;
                        // Note: storage root is always in s_main.bytes.
                        let storage_root_rlc = rlc::expr(
                            &ctx.s_main.bytes.iter().map(|&byte| a!(byte, rot_into_storage_root)).collect::<Vec<_>>(),
                            &ctx.r,
                        );
                        require!((1, branch_rlc, branch.len(), storage_root_rlc) => @"keccak");
                    } elsex {
                        // Here the branch is in some other branch
                        let mod_node_hash_rlc = a!(ctx.accumulators.mod_node_rlc(is_s), rot_branch_child_prev);
                        ifx!{branch.is_branch_non_hashed() => {
                            /* Non-hashed branch hash in parent branch */
                            // We need to check that `branch_RLC = parent_branch_modified_node_RLC`.
                            require!(branch_rlc => mod_node_hash_rlc);
                        } elsex {
                            /* Hashed branch hash in parent branch */
                            // We need to check that `hash(branch) = parent_branch_modified_node`.
                            require!((1, branch_rlc, branch.len(), mod_node_hash_rlc) => @"keccak");
                        }}
                    }}
                } elsex {
                    /* Branch in first level of account trie - hash compared to root */
                    // When branch is in the first level of the account trie, we need to check that
                    // `hash(branch) = account_trie_root`.
                    // Note: branch in the first level cannot be shorter than 32 bytes (it is always hashed).
                    require!((1, branch_rlc, branch.len(), a!(ctx.inter_root(is_s))) => @"keccak");
                }}
            }}
        });

        BranchHashInParentConfig {
            _marker: PhantomData,
        }
    }
}
