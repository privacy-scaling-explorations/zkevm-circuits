use halo2_proofs::{arithmetic::FieldExt, plonk::VirtualCells, poly::Rotation};
use std::marker::PhantomData;

use crate::{
    circuit,
    circuit_tools::{DataTransition, RLCChainable},
    mpt_circuit::{helpers::contains_placeholder_leaf, FixedTableTag},
    mpt_circuit::{
        helpers::{BranchChildInfo, MPTConstraintBuilder},
        MPTContext,
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

The constraints in `branch_rlc.rs` check whether the branch RLC is being properly computed row by row.
There are three type of branch children rows: empty children, non-empty hashed children,
non-empty non-hashed children. We need to take into account these three types when computing
the intermediate RLC of the current row.

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

Note that the RLC for branch init row is checked in `branch_init.rs`.
*/

#[derive(Clone, Debug)]
pub(crate) struct BranchRLCConfig<F> {
    _marker: PhantomData<F>,
}

impl<F: FieldExt> BranchRLCConfig<F> {
    pub fn configure(
        meta: &mut VirtualCells<'_, F>,
        cb: &mut MPTConstraintBuilder<F>,
        ctx: MPTContext<F>,
        is_s: bool,
    ) -> Self {
        let main = ctx.main(is_s);
        let branch = ctx.accumulators.acc(is_s);
        let mult_diff = ctx.accumulators.node_mult_diff(is_s);
        circuit!([meta, cb.base], {
            let child = BranchChildInfo::new(meta, ctx.clone(), is_s, 0);
            let branch_mult = DataTransition::new(meta, branch.mult);
            let branch_rlc = DataTransition::new(meta, branch.rlc);

            // Calculate the RLC
            let rlc = child.rlc(meta, &mut cb.base);
            require!(branch_rlc => (branch_rlc.prev(), branch_mult.prev()).rlc_chain(rlc));
            require!(branch_mult => branch_mult.prev() * a!(mult_diff));

            // RLC bytes zero check
            cb.set_length_sc(is_s, child.num_bytes_on_row(meta));
            // We need to check that the multiplier changes according to `num_bytes` and
            // update it.
            require!((FixedTableTag::RMult, child.num_bytes(meta), a!(mult_diff)) => @format!("mult{}", if is_s {""} else {"2"}));

            // When a value is being added (and reverse situation when deleted) to the trie
            // and there is no other leaf at the position where it is to be
            // added, we have empty branch child in `S` proof and hash of a
            // newly added leaf at the parallel position in `C` proof.
            // That means we have empty node in `S` proof at `modified_node`.
            // When this happens, we denote this situation by having a placeholder leaf.
            // In this case we need to make sure the node is seen as empty.
            ifx! {a!(ctx.branch.is_modified), contains_placeholder_leaf(meta, ctx.clone(), is_s, 0) => {
                require!(child.is_hashed(meta) => true);
                require!(a!(main.rlp2) => 0);
            }}
        });

        BranchRLCConfig {
            _marker: PhantomData,
        }
    }
}
