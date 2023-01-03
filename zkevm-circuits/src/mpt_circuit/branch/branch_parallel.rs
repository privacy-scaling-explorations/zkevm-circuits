use gadgets::util::{and, not, Expr};
use halo2_proofs::{
    arithmetic::FieldExt,
    plonk::{Expression, VirtualCells},
    poly::Rotation,
};
use std::marker::PhantomData;

use crate::{
    constraints,
    mpt_circuit::{
        helpers::{BaseConstraintBuilder, ColumnTransition},
        FixedTableTag, MPTContext,
    },
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

The constraints that are the same for `S` and `C` proofs are implemented in `branch_parallel.rs`.
For example, in a an empty row (nil branch child) like
[0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1]
we need to check that `rlp2 = 0`, `bytes[0] = 128`, and `bytes[i] = 0` for `i > 0`.

Also, we check that the RLC corresponding to the `modified_node` is stored in `mod_node_hash_rlc` column.
In the above example we have `modified_node = 2` which corresponds to the row:
[0 160 164 92 78 34 81 137 173 236 78 208 145 118 128 60 46 5 176 8 229 165 42 222 110 4 252 228 93 243 26 160 241 85 0 160 95 174 59 239 229 74 221 53 227 115 207 137 94 29 119 126 56 209 55 198 212 179 38 213 219 36 111 62 46 43 176 168 1]

So the `S` RLC of the `modified_node` is: `164 + 92 * r + 78 * r^2 + ... + 85 * r^31`
The `C` RLC is: `95 + 174*r + 59* r^2 + ... + 168 * r^31`

The `S` RLC is stored in `s_mod_node_hash_rlc` column, in all 16 branch children rows.
The `C` RLC is stored in `c_mod_node_hash_rlc` column, in all 16 branch children rows.

Having the values stored in all 16 rows makes it easier to check whether it is really the value that
corresponds to the `modified_node`. Otherwise, having this value stored for example only in branch init row
we would not know what rotation to use into branch init when in `modified_node` row.

Note that the constraints about having the RLC value corresponds to the `modified_node` row are
implemented in `branch.rs`. This is because we do not have full symmetry between `S` and `C` proofs
in the case of branch placeholders.

Finally, when there is a non-hashed branch child, we need to check that there are 0s after the last
branch child byte. The example is:
[0,0,198,132,48,0,0,0,1,...]
In this case the branch child is of length `6 = 198 - 192`: `[132, 48, 0, 0, 0, 1]`.
We need to make sure there are 0s after these 6 bytes.
*/

#[derive(Clone, Debug)]
pub(crate) struct BranchParallelConfig<F> {
    _marker: PhantomData<F>,
}

impl<F: FieldExt> BranchParallelConfig<F> {
    pub fn configure(
        meta: &mut VirtualCells<'_, F>,
        cb: &mut BaseConstraintBuilder<F>,
        ctx: MPTContext<F>,
        is_s: bool,
    ) -> Self {
        let branch = ctx.branch;
        let mod_node_hash_rlc = if is_s {
            ctx.accumulators.s_mod_node_rlc
        } else {
            ctx.accumulators.c_mod_node_rlc
        };
        let main = if is_s { ctx.s_main } else { ctx.c_main };
        let sel = if is_s {
            ctx.denoter.sel1
        } else {
            ctx.denoter.sel2
        };
        let is_node_hashed = if is_s {
            ctx.denoter.is_node_hashed_s
        } else {
            ctx.denoter.is_node_hashed_c
        };
        constraints! {[meta, cb], {
            // Empty and non-empty branch children
            // Empty nodes have 0 at `rlp2`, have `128` at `bytes[0]` and 0 everywhere else:
            // [0, 0, 128, 0, ..., 0].
            // While non-empty nodes have `160` at `rlp2` and then any byte at `bytes`:
            // [0, 160, a0, ..., a31].
            // Note: `s_rlp1` and `c_rlp1` store the number of RLP still left in the in the branch rows.
            // The constraints are in `branch.rs`, see `RLP length` gate.
            ifx!{not::expr(a!(is_node_hashed)) => {
                let rlp2 = a!(main.rlp2);
                // Empty nodes have `rlp2 = 0`. Non-empty nodes have: `rlp2 = 160`.
                require!(rlp2 => {[0.expr(), 160.expr()]});

                let c160inv = Expression::Constant(F::from(160).invert().unwrap());
                let is_empty = (rlp2.expr() - 160.expr()) * c160inv;
                // For empty nodes
                ifx!{is_empty => {
                    // TODO(Brecht): this conflicts with something else...
                    // When an empty node (0 at `rlp2`), `bytes[0] = 128`.
                    // Note that `rlp2` can be only be 0 or 128.
                    //require!(a!(main.bytes[0]) => 128);
                    // When an empty node (0 at `rlp2`), `bytes[i] = 0` for `i > 0`.
                    //cb.set_range_length_sc(is_s, 1.expr());
                    for (idx, byte) in main.bytes.iter().map(|&byte| a!(byte)).enumerate() {
                        if idx == 0 {
                            // When an empty node (0 at `rlp2`), `bytes[0] = 128`.
                            // Note that `rlp2` can be only be 0 or 128.
                            require!(byte => 128);
                        } else {
                            // When an empty node (0 at `rlp2`), `bytes[i] = 0` for `i > 0`.
                            require!(byte => 0);
                        }
                    }
                }}
                // No further constraints needed for non-empty nodes besides `rlp2 = 160`
                // and values to be bytes which is constrained by the byte range lookups
                // on `s_main.bytes` and `c_main.bytes`.
                // Note: The attacker could put 160 in an empty node (the constraints
                // above does not / cannot prevent this) and thus try to
                // modify the branch RLC (used for checking the hash of a branch), like:
                // [0, 160, 128, 0, ..., 0]
                // But then the constraints related to the branch RLP length would fail -
                // the length of RLP bytes in such a row would then be `32 + 1 = 160 - 128 + 1`
                // instead of `1` and the RLP length constraint would fail.
            }}

            // Branch child RLC & selector for specifying whether the modified node is empty
            // `mod_node_hash_rlc` is the same for all `is_branch_child` rows.
            // Having the values stored in all 16 rows makes it easier to check whether it is really the value that
            // corresponds to the `modified_node`. This is used in `branch.rs` constraints like:
            // ```
            // * is_modified.clone()
            // * (hash_rlc.clone() - mod_node_hash_rlc_cur.clone()
            // ```
            // `hash_rlc` is computed in each row as: `bytes[0] + bytes[1] * r + ... + bytes[31] * r^31`.
            // Note that `hash_rlc` is somehow misleading name because the branch child can be non-hashed too.
            ifx!{a!(branch.node_index) => { // ignore if node_index = 0 (there is no previous)
                // mod_node_hash_rlc the same for all branch children
                require!(a!(mod_node_hash_rlc) => a!(mod_node_hash_rlc, -1));
                // Selector for the modified child being empty the same for all branch children
                require!(a!(sel) => a!(sel, -1));
            }}
            // When a value is being added (and reverse situation when deleted) to the trie and
            // there is no other leaf at the position where it is to be added, we have empty branch child
            // in `S` proof and hash of a newly added leaf at the parallel position in `C` proof.
            // That means we have empty node in `S` proof at `modified_node`.
            // When this happens, we denote this situation by having `sel = 1`.
            // In this case we need to check that `main.bytes = [128, 0, ..., 0]`.
            ifx!{a!(branch.is_modified), a!(sel) => {
                // We check `bytes[0] = 128`.
                require!(a!(main.bytes[0]) => 128);
                // The remaining constraints for `main.bytes = [128, 0, ..., 0]` need to be `0`.
                cb.set_range_length_sc(is_s, 1.expr());
            }}
        }}

        BranchParallelConfig {
            _marker: PhantomData,
        }
    }
}
