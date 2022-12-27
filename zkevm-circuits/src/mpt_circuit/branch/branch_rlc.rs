use gadgets::util::{and, not, Expr};
use halo2_proofs::{
    arithmetic::FieldExt,
    plonk::{Advice, Column, Expression, Fixed, VirtualCells},
    poly::Rotation,
};
use std::marker::PhantomData;

use crate::{
    constraints,
    evm_circuit::util::{dot, rlc},
    mpt_circuit::param::{HASH_WIDTH, POWER_OF_RANDOMNESS_LEN},
    mpt_circuit::{
        columns::{AccumulatorPair, MainCols},
        FixedTableTag,
    },
    mpt_circuit::{
        helpers::{BaseConstraintBuilder, ColumnTransition},
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

Note that the RLC for branch init row is checked in `branch_init.rs`.
*/

#[derive(Clone, Debug)]
pub(crate) struct BranchRLCConfig<F> {
    _marker: PhantomData<F>,
}

impl<F: FieldExt> BranchRLCConfig<F> {
    pub fn configure(
        meta: &mut VirtualCells<'_, F>,
        cb: &mut BaseConstraintBuilder<F>,
        ctx: MPTContext<F>,
        is_s: bool,
    ) -> Self {
        let main = if is_s { ctx.s_main } else { ctx.c_main };
        let branch_acc = if is_s {
            ctx.accumulators.acc_s
        } else {
            ctx.accumulators.acc_c
        };
        let is_node_hashed = if is_s {
            ctx.denoter.is_node_hashed_s
        } else {
            ctx.denoter.is_node_hashed_c
        };
        let node_mult_diff = if is_s {
            ctx.accumulators.node_mult_diff_s
        } else {
            ctx.accumulators.node_mult_diff_c
        };
        let r = ctx.r;
        constraints! {[meta, cb], {
            let rlp2 = a!(main.rlp2);
            let is_node_hashed = a!(is_node_hashed);
            let node_mult_diff = a!(node_mult_diff);
            let branch_mult = ColumnTransition::new(meta, branch_acc.mult);
            let branch_rlc = ColumnTransition::new(meta, branch_acc.rlc);

            // TODO(Brecht): comments hashed/non-hashed don't seem to match `is_node_hashed`.
            ifx!{is_node_hashed => {
                // When a branch child is non-hashed, we have `bytes[0] - 192` bytes in a row.
                // We need to add these bytes to the RLC. Note that we add all `bytes` to the RLC, but
                // we rely that there are 0s after the last non-hashed byte (see constraints in `branch.rs`).
                // For example we have 6 bytes in the following child: `[0,0,198,132,48,0,0,0,1,...]`.
                let rlc = branch_rlc.prev() + rlc::expr(
                    &main.bytes.iter().map(|&byte| branch_mult.prev() * a!(byte)).collect::<Vec<_>>(),
                    &r,
                );
                require!(branch_rlc.cur() => rlc.expr());

                // When a branch child is non-hashed, we have `f = bytes[0] - 192` bytes in a row.
                // The multiplier changes by factor `r^{f+1}`. `+1` is for the byte that specifies the length.
                // We do not know in advance the factor `f`, so we use the lookup table that it corresponds
                // to the length specified at `rlp2` position. See mult diff lookup constraint below.
                // We have to multiply with r[0] because of the first (length) byte.
                require!(branch_mult.cur() => branch_mult.prev() * r[0].expr() * node_mult_diff.expr());
            } elsex {
                ifx!{rlp2.expr() - 160.expr() => {
                    // When a branch child is empty, we only have one byte (128 at `bytes[0]`)
                    // that needs to be added to the RLC.
                    // `branch_mult_prev` is the value that is to be used when multiplying the byte to be added
                    // to the RLC. Note that `branch_mult_prev` is stored in the previous row.
                    require!(branch_rlc.cur() => branch_rlc.prev() + 128.expr() * branch_mult.prev());

                    // When a branch child is empty, we only have one byte in a row and the multiplier only
                    // changes by factor `r`.
                    require!(branch_mult.cur() => branch_mult.prev() * r[0].expr());
                }}

                ifx!{rlp2 => {
                    // When a branch child is non-empty and hashed, we have 33 bytes in a row.
                    // We need to add these 33 bytes to the RLC.
                    let rlc = 160.expr() * branch_mult.prev() + dot::expr(
                        &main.bytes.iter().map(|&byte| branch_mult.prev() * a!(byte)).collect::<Vec<_>>(),
                        &r,
                    );
                    require!(branch_rlc.cur() => branch_rlc.prev() + rlc.expr());

                    // When a branch child is non-empty and hashed, we have 33 bytes in a row.
                    // The multiplier changes by factor `r^33`.
                    require!(branch_mult.cur() => branch_mult.prev() * r[0].expr() * r[POWER_OF_RANDOMNESS_LEN - 1].expr());
                }}
            }}

            // We need to check that the multiplier in non-hashed nodes changes according to the non-hashed
            // node length.
            ifx!{is_node_hashed => {
                require!((FixedTableTag::RMult, a!(main.bytes[0]) - 192.expr(), node_mult_diff) => @fixed);
            }}
        }}

        // Note: the constraints for there being 0s after the non-hashed child last byte
        // are in branch_parallel.rs.

        BranchRLCConfig {
            _marker: PhantomData,
        }
    }
}
