use gadgets::util::{and, not, Expr};
use halo2_proofs::{
    arithmetic::FieldExt,
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, VirtualCells},
    poly::Rotation,
};
use std::marker::PhantomData;

use crate::{
    constraints, cs,
    mpt_circuit::{
        columns::{MainCols, PositionCols},
        helpers::{key_len_lookup, BaseConstraintBuilder, ColumnTransition},
        param::HASH_WIDTH,
    },
};

use super::BranchCols;

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
    #[allow(clippy::too_many_arguments)]
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        position_cols: PositionCols<F>,
        branch: BranchCols<F>,
        mod_node_hash_rlc: Column<Advice>,
        main: MainCols<F>,
        sel: Column<Advice>,
        is_node_hashed: Column<Advice>,
        fixed_table: [Column<Fixed>; 3],
        check_zeros: bool,
    ) -> Self {
        meta.create_gate("Empty and non-empty branch children", |meta| {
            let mut cb = BaseConstraintBuilder::default();
            constraints! {[meta, cb], {

            let q_enable = f!(position_cols.q_enable);
            let q_not_first = f!(position_cols.q_not_first);
            let is_branch_child = a!(branch.is_child);
            let rlp2 = a!(main.rlp2);
            let is_node_hashed = a!(is_node_hashed);
            let node_index = a!(branch.node_index);
            let is_modified = a!(branch.is_modified);

            let sel = ColumnTransition::new(meta, sel);
            let mod_node_hash_rlc = ColumnTransition::new(meta, mod_node_hash_rlc);

            ifx!{is_branch_child.expr() => {
                // Empty and non-empty branch children
                // Empty nodes have 0 at `rlp2`, have `128` at `bytes[0]` and 0 everywhere else:
                // [0, 0, 128, 0, ..., 0].
                // While non-empty nodes have `160` at `rlp2` and then any byte at `bytes`:
                // [0, 160, a0, ..., a31].
                // Note: `s_rlp1` and `c_rlp1` store the number of RLP still left in the in the branch rows.
                // The constraints are in `branch.rs`, see `RLP length` gate.
                ifx!{q_enable.expr(), not::expr(is_node_hashed.expr()) => {
                    // Empty nodes have `rlp2 = 0`. Non-empty nodes have: `rlp2 = 160`.
                    require!({rlp2.expr()} in {[0.expr(), 160.expr()]});

                    // For empty nodes
                    ifx!{rlp2.expr() - 160.expr() => {
                        for (idx, byte) in main.bytes.iter().map(|&byte| a!(byte)).enumerate() {
                            if idx == 0 {
                                // When an empty node (0 at `rlp2`), `bytes[0] = 128`.
                                // Note that `rlp2` can be only 0 or 128.
                                require!(byte => 128.expr());
                            } else {
                                // When an empty node (0 at `rlp2`), `bytes[i] = 0` for `i > 0`.
                                require!(byte => 0.expr());
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
                ifx!{q_not_first.expr() => {
                    // `mod_node_hash_rlc` is the same for all `is_branch_child` rows.
                    // Having the values stored in all 16 rows makes it easier to check whether it is really the value that
                    // corresponds to the `modified_node`. This is used in `branch.rs` constraints like:
                    // ```
                    // * is_modified.clone()
                    // * (hash_rlc.clone() - mod_node_hash_rlc_cur.clone()
                    // ```
                    // `hash_rlc` is computed in each row as: `bytes[0] + bytes[1] * r + ... + bytes[31] * r^31`.
                    // Note that `hash_rlc` is somehow misleading name because the branch child can be non-hashed too.
                    ifx!{node_index.expr() => { // ignore if node_index = 0 (there is no previous)
                        // mod_node_hash_rlc the same for all branch children
                        require!(mod_node_hash_rlc.cur() => mod_node_hash_rlc.prev());
                        // Selector for the modified child being empty the same for all branch children
                        require!(sel.cur() => sel.prev());
                    }}

                    // When a value is being added (and reverse situation when deleted) to the trie and
                    // there is no other leaf at the position where it is to be added, we have empty branch child
                    // in `S` proof and hash of a newly added leaf at the parallel position in `C` proof.
                    // That means we have empty node in `S` proof at `modified_node`.
                    // When this happens, we denote this situation by having `sel = 1`.
                    // In this case we need to check that `main.bytes = [128, 0, ..., 0]`.
                    ifx!{is_modified.expr(), sel.expr() => {
                        for (idx, byte) in main.bytes.iter().map(|&byte| a!(byte)).enumerate() {
                            if idx == 0 {
                                // We first check `bytes[0] = 128`.
                                require!(byte => 128.expr());
                            } else {
                                // The remaining constraints for `main.bytes = [128, 0, ..., 0]`:
                                // `bytes[i] = 0` for `i > 0`.
                                require!(byte => 0.expr());
                            }
                        }
                    }}
                }}
            }}
            }}

            cb.gate(1.expr())
        });

        let sel = |meta: &mut VirtualCells<F>| {
            let q_enable = meta.query_fixed(position_cols.q_enable, Rotation::cur());
            let is_branch_child_cur = meta.query_advice(branch.is_child, Rotation::cur());
            let is_node_hashed = meta.query_advice(is_node_hashed, Rotation::cur());

            q_enable * is_branch_child_cur * is_node_hashed
        };

        /*
        When branch child is shorter than 32 bytes it does not get hashed, that means some positions
        in `main.bytes` stay unused. But we need to ensure there are 0s at unused positions to avoid
        attacks on the RLC which is computed taking into account all `main.bytes`.
        */
        if check_zeros {
            for ind in 1..HASH_WIDTH {
                key_len_lookup(
                    meta,
                    sel,
                    ind,
                    main.bytes[0],
                    main.bytes[ind],
                    192,
                    fixed_table,
                )
            }
        }

        BranchParallelConfig {
            _marker: PhantomData,
        }
    }
}
