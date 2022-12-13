use gadgets::util::{and, not, sum, Expr};
use halo2_proofs::{
    arithmetic::FieldExt,
    plonk::{Advice, Column, ConstraintSystem, Expression},
    poly::Rotation,
};
use std::marker::PhantomData;

use crate::{
    cs,
    mpt_circuit::{
        columns::{AccumulatorPair, MainCols, PositionCols},
        helpers::ColumnTransition,
    },
    mpt_circuit::{
        helpers::BaseConstraintBuilder,
        param::{
            IS_BRANCH_C16_POS, IS_BRANCH_C1_POS, IS_EXT_LONG_EVEN_C16_POS, IS_EXT_LONG_EVEN_C1_POS,
            IS_EXT_LONG_ODD_C16_POS, IS_EXT_LONG_ODD_C1_POS, IS_EXT_SHORT_C16_POS,
            IS_EXT_SHORT_C1_POS, RLP_NUM,
        },
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

The constraints in this `branch_key.rs` checks whether the key RLC is being properly
computed using `modified_node`. Note that `modified_node` presents the branch node
to be modified and is one of the nibbles of a key.

Let us have the following scenario:

```
Branch1:
  node1_0
  node1_1     <- modified_node
  ...
  node1_15
Branch2
  node2_0
  ...
  node2_7    <- modified_node
  ...
  node2_15
Branch3
  node3_0
  ...
  node3_5    <- modified_node
  ...
  node3_15
Branch4
  node4_0
  ...
  node4_11    <- modified_node
  ...
  node4_15
Leaf1
```

We have four branches and finally a leaf in the fourth branch. The modified nodes are: `1, 7, 5, 11`.
The modified nodes occupy two bytes, the remaining 30 bytes are stored in `Leaf1`:
`b_0, ..., b_29`.

The key at which the change occurs is thus: `1 * 16 + 7, 5 * 16 + 11, b_0, ..., b_29`.
The RLC of the key is: `(1 * 16 + 7) + (5 * 16 + 11) * r + b_0 * r^2 + b_29 * r^31`.

In each branch we check whether the intermediate RLC is computed correctly. The intermediate
values are stored in `accumulators.key`. There is always the actual RLC value and the multiplied
that is to be used when adding the next summand: `accumulators.key.rlc, accumulators.key.mult`.

For example, in `Branch1` we check whether the intermediate RLC is `1 * 16`.
In `Branch2`, we check whether the intermediate RLC is `rlc_prev_branch_init_row + 7`.
In `Branch3`, we check whether the intermediate RLC is `rlc_prev_branch_init_row + 5 * 16 * r`.
In `Branch4`, we check whether the intermediate RLC is `rlc_prev_branch_init_row + 11 * r`.

There are auxiliary columns `sel1` and `sel2` which specify whether we are in branch where
the nibble has to be multiplied by 16 or by 1. `sel1 = 1` means multiplying by 16,
`sel2 = 1` means multiplying by 1.
*/

#[derive(Clone, Debug)]
pub(crate) struct BranchKeyConfig<F> {
    _marker: PhantomData<F>,
}

impl<F: FieldExt> BranchKeyConfig<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        position_cols: PositionCols<F>,
        /* `not_first_level` to avoid rotating back when in the first branch (for key rlc) */
        branch: BranchCols<F>,
        is_account_leaf_in_added_branch: Column<Advice>,
        s_main: MainCols<F>,
        acc_pair: AccumulatorPair<F>, // used first for account address, then for storage key
        randomness: Expression<F>,
    ) -> Self {
        meta.create_gate("Branch key RLC", |meta| {
            // For the first branch node (node_index = 0), the key rlc needs to be:
            // key_rlc = key_rlc::Rotation(-19) + modified_node * key_rlc_mult
            // Note: we check this in the first branch node (after branch init),
            // Rotation(-19) lands into the previous first branch node, that's because
            //  branch has 1 (init) + 16 (children) + 2 (extension nodes for S and C) rows
            let rot_prev = -19;

            // We need to check whether we are in the first storage level, we can do this
            // by checking whether is_account_leaf_storage_codehash_c is true in the
            // previous row.
            let q_not_first = meta.query_fixed(position_cols.q_not_first, Rotation::cur());
            let not_first_level = meta.query_advice(position_cols.not_first_level, Rotation::cur());
            let is_branch_init_prev = meta.query_advice(branch.is_init, Rotation::prev());
            let modified_node = meta.query_advice(branch.modified_node, Rotation::cur());

            // Get extension node selectors
            let is_ext_short_c16 =
                meta.query_advice(s_main.bytes[IS_EXT_SHORT_C16_POS - RLP_NUM], Rotation(-1));
            let is_ext_short_c1 =
                meta.query_advice(s_main.bytes[IS_EXT_SHORT_C1_POS - RLP_NUM], Rotation(-1));
            let is_ext_long_even_c16 = meta.query_advice(
                s_main.bytes[IS_EXT_LONG_EVEN_C16_POS - RLP_NUM],
                Rotation(-1),
            );
            let is_ext_long_even_c1 = meta.query_advice(
                s_main.bytes[IS_EXT_LONG_EVEN_C1_POS - RLP_NUM],
                Rotation(-1),
            );
            let is_ext_long_odd_c16 = meta.query_advice(
                s_main.bytes[IS_EXT_LONG_ODD_C16_POS - RLP_NUM],
                Rotation(-1),
            );
            let is_ext_long_odd_c1 =
                meta.query_advice(s_main.bytes[IS_EXT_LONG_ODD_C1_POS - RLP_NUM], Rotation(-1));

            let is_extension_key_even = is_ext_long_even_c16 + is_ext_long_even_c1;
            let is_extension_key_odd =
                is_ext_long_odd_c16 + is_ext_long_odd_c1 + is_ext_short_c16 + is_ext_short_c1;
            let is_extension_node = is_extension_key_even.clone() + is_extension_key_odd.clone();

            // -2 because we are in the first branch child and -1 is branch init row, -2 is
            // account leaf storage codehash when we are in the first storage proof level
            let is_account_leaf_in_added_branch_prev =
                meta.query_advice(is_account_leaf_in_added_branch, Rotation(-2));

            // If sel1 = 1, then modified_node is multiplied by 16.
            // If sel2 = 1, then modified_node is multiplied by 1.
            // NOTE: modified_node presents nibbles: n0, n1, ...
            // key_rlc = (n0 * 16 + n1) + (n2 * 16 + n3) * r + (n4 * 16 + n5) * r^2 + ...

            // Rotation(-20) lands into previous branch init.
            let sel1 = ColumnTransition::new_with_rot(
                meta, s_main.bytes[IS_BRANCH_C16_POS - RLP_NUM], Rotation(-1 + rot_prev), Rotation(-1)
            );
            let sel2 = ColumnTransition::new_with_rot(
                meta, s_main.bytes[IS_BRANCH_C1_POS - RLP_NUM], Rotation(-1 + rot_prev), Rotation(-1)
            );
            let key_rlc = ColumnTransition::new_with_rot(
                meta, acc_pair.rlc, Rotation(rot_prev), Rotation::cur()
            );
            let key_rlc_mult = ColumnTransition::new_with_rot(
                meta, acc_pair.mult, Rotation(rot_prev), Rotation::cur()
            );

            let mut cb = BaseConstraintBuilder::default();

            cs!{[cb],
            ifx(and::expr([q_not_first.expr(), is_branch_init_prev.expr()])) {
                let selectors = [sel1.expr(), sel2.expr()];
                // Selectors need to be boolean.
                for selector in selectors.iter() {
                    cb.require_boolean("selector boolean", selector.expr());
                }
                // One selector needs to be enabled.
                cb.require_equal("One selector needs to be enabled", sum::expr(&selectors), 1.expr());

                 // `sel1/sel2` present with what multiplier (16 or 1) is to be multiplied
                // the `modified_node` in a branch, so when we have an extension node as a parent of
                // a branch, we need to take account the nibbles of the extension node.

                // If extension node, `sel1` and `sel2` in the first level depend on the extension key
                // (whether it is even or odd). If key is even, the constraints stay the same. If key
                // is odd, the constraints get turned around. Note that even/odd
                // presents the number of key nibbles (what we actually need here) and
                // not key byte length (how many bytes key occupies in RLP).

                cs!{[cb],
                ifx(and::expr([not_first_level.expr(), not::expr(is_account_leaf_in_added_branch_prev.expr())])) {
                    cs!{[cb],
                    ifx(not::expr(is_extension_node.expr())) {
                        cs!{[cb],
                        ifx(sel1.expr()) {
                            // When we are not in the first level and when sel1, the intermediate key RLC needs to be
                            // computed by adding `modified_node * 16 * mult_prev` to the previous intermediate key RLC.
                            cb.require_equal(
                                "Key RLC sel1 not first level",
                                key_rlc.cur(),
                                key_rlc.prev() + modified_node.clone() * 16.expr() * key_rlc_mult.prev(),
                            );
                            // When we are not in the first level and when sel1, the intermediate key RLC mult needs to
                            // stay the same - `modified_node` in the next branch will be multiplied by the same mult
                            // when computing the intermediate key RLC.
                            cb.require_equal(
                                "Key RLC sel1 not first level mult",
                                key_rlc_mult.cur(),
                                key_rlc_mult.prev(),
                            );
                        }}
                        cs!{[cb],
                        ifx(sel2.expr()) {
                            // When we are not in the first level and when sel2, the intermediate key RLC needs to be
                            // computed by adding `modified_node * mult_prev` to the previous intermediate key RLC.
                            cb.require_equal(
                                "Key RLC sel2 not first level",
                                key_rlc.cur(),
                                key_rlc.prev() + modified_node.clone() * key_rlc_mult.prev()
                            );
                            // When we are not in the first level and when sel1, the intermediate key RLC mult needs to
                            // be multiplied by `r` - `modified_node` in the next branch will be multiplied
                            // by `mult * r`.
                            cb.require_equal(
                                "Key RLC sel2 not first level mult",
                                key_rlc_mult.cur(),
                                key_rlc_mult.prev() * randomness.clone(),
                            );
                        }}
                    }}

                    // `sel1` alernates between 0 and 1 for regular branches.
                    // Note that `sel2` alternates implicitly because of `sel1 + sel2 = 1`.
                    cs!{[cb],
                    ifx(not::expr(is_extension_node.expr())) {
                        cb.require_equal(
                            "sel1 0->1->0->...",
                            sel1.cur(),
                            not::expr(sel1.prev()),
                        );
                    }}
                    // `sel1` alernates between 0 and 1 for extension nodes with even number of nibbles.
                    cs!{[cb],
                    ifx(is_extension_key_even) {
                        cb.require_equal(
                            "sel1 0->1->0->... (extension node even key)",
                            sel1.cur(),
                            not::expr(sel1.prev()),
                        );
                    }}
                    // `sel1` stays the same for extension nodes with odd number of nibbles.
                    cs!{[cb],
                    ifx(is_extension_key_odd) {
                        cb.require_equal(
                            "sel1 stays the same (extension odd key)",
                            sel1.cur(),
                            sel1.prev(),
                        );
                    }}
                }}

                let is_account = not::expr(not_first_level.expr());
                let is_storage = is_account_leaf_in_added_branch_prev.expr();
                // TODO(Brecht): are the above mutually exclusive? is so can just do is_account + is_storage
                for (pre_condition, condition) in [
                    (not::expr(not_first_level.expr()), is_account.expr()),
                    (not_first_level.expr(), is_storage.expr()),
                    ] {
                    cs!{[cb],
                    ifx(and::expr([pre_condition.expr(), condition.expr(), not::expr(is_extension_node.expr())])) {
                        // In the first level, address RLC is simply `modified_node * 16`.
                        cb.require_equal(
                            "Account/Storage address RLC first level",
                            key_rlc.expr(),
                            modified_node.clone() * 16.expr(),
                        );
                        // In the first level, address RLC mult is simply 1.
                        cb.require_equal(
                            "Account/Storage address RLC mult first level",
                            key_rlc_mult.expr(),
                            1.expr(),
                        );

                        // Key RLC for extension node is checked in `extension_node.rs`,
                        // however, `sel1` & `sel2` being properly set are checked here
                        // to avoid additional rotations.
                    }}

                    // `sel1` in the first level is 1.
                    cs!{[cb],
                    ifx(condition) {
                        cs!{[cb],
                        ifx(not::expr(is_extension_node.expr())) {
                            cb.require_true("Account/Storage first level sel1 (regular branch)", sel1.expr());
                        }}
                        cs!{[cb],
                        ifx(is_extension_key_even) {
                            cb.require_true("Account/Storage first level sel1 = 1 (extension node even key)", sel1.expr());
                        }}
                        cs!{[cb],
                        ifx(is_extension_key_odd) {
                            // `sel1/sel2` get turned around when odd number of nibbles.
                            cb.require_false("Account/Storage first level sel1 = 0 (extension node odd key)", sel1.expr());
                        }}
                    }}
                }
            }}

            cb.gate(1.expr())
        });

        BranchKeyConfig {
            _marker: PhantomData,
        }
    }
}
