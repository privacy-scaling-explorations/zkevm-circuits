use halo2_proofs::{
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed},
    poly::Rotation,
};
use pairing::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::{param::{
    IS_EXT_LONG_EVEN_C16_POS, IS_EXT_LONG_EVEN_C1_POS, IS_EXT_LONG_ODD_C16_POS,
    IS_EXT_LONG_ODD_C1_POS, IS_EXT_SHORT_C16_POS, IS_EXT_SHORT_C1_POS, RLP_NUM, IS_BRANCH_C16_POS, IS_BRANCH_C1_POS,
}, columns::{MainCols, AccumulatorPair}};

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

The constraints in this file check whether the key is being properly build using modified_node -
modified_node presents a nibble in a key. Storage key is composed of
(modified_node_prev * 16 + modified_node) bytes and key bytes in a leaf.
*/

#[derive(Clone, Debug)]
pub(crate) struct BranchKeyConfig<F> {
    _marker: PhantomData<F>,
}

impl<F: FieldExt> BranchKeyConfig<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_not_first: Column<Fixed>,
        not_first_level: Column<Advice>, /* to avoid rotating back when in the first branch (for
                                          * key rlc) */
        branch: BranchCols<F>,
        is_account_leaf_in_added_branch: Column<Advice>,
        s_main: MainCols<F>,
        acc_pair: AccumulatorPair<F>, // used first for account address, then for storage key
        acc_r: F,
    ) -> Self {
        let config = BranchKeyConfig { _marker: PhantomData };
        let one = Expression::Constant(F::one());

        meta.create_gate("branch key", |meta| {
            // For the first branch node (node_index = 0), the key rlc needs to be:
            // key_rlc = key_rlc::Rotation(-19) + modified_node * key_rlc_mult
            // Note: we check this in the first branch node (after branch init),
            // Rotation(-19) lands into the previous first branch node, that's because
            // branch has 1 (init) + 16 (children) + 2 (extension nodes for S and C) rows

            // We need to check whether we are in the first storage level, we can do this
            // by checking whether is_account_leaf_storage_codehash_c is true in the
            // previous row.

            let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
            let not_first_level = meta.query_advice(not_first_level, Rotation::cur());

            let mut constraints = vec![];

            let is_branch_init_prev = meta.query_advice(branch.is_init, Rotation::prev());
            let modified_node_cur = meta.query_advice(branch.modified_node, Rotation::cur());

            let is_ext_short_c16 = meta.query_advice(
                s_main.bytes[IS_EXT_SHORT_C16_POS - RLP_NUM],
                Rotation(-1),
            );
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
            let is_ext_long_odd_c1 = meta.query_advice(
                s_main.bytes[IS_EXT_LONG_ODD_C1_POS - RLP_NUM],
                Rotation(-1),
            );

            let is_extension_key_even = is_ext_long_even_c16.clone() + is_ext_long_even_c1.clone();
            let is_extension_key_odd = is_ext_long_odd_c16.clone()
                + is_ext_long_odd_c1.clone()
                + is_ext_short_c16.clone()
                + is_ext_short_c1.clone();

            let is_extension_node = is_extension_key_even.clone() + is_extension_key_odd.clone();

            // -2 because we are in the first branch child and -1 is branch init row, -2 is
            // account leaf storage codehash when we are in the first storage proof level
            let is_account_leaf_in_added_branch_prev =
                meta.query_advice(is_account_leaf_in_added_branch, Rotation(-2));

            let c16 = Expression::Constant(F::from(16));
            // If sel1 = 1, then modified_node is multiplied by 16.
            // If sel2 = 1, then modified_node is multiplied by 1.
            // NOTE: modified_node presents nibbles: n0, n1, ...
            // key_rlc = (n0 * 16 + n1) + (n2 * 16 + n3) * r + (n4 * 16 + n5) * r^2 + ...
            let sel1_prev = meta.query_advice(s_main.bytes[IS_BRANCH_C16_POS - RLP_NUM], Rotation(-20));
            // Rotation(-20) lands into previous branch init.
            let sel1_cur = meta.query_advice(s_main.bytes[IS_BRANCH_C16_POS - RLP_NUM], Rotation::prev());
            let sel2_cur = meta.query_advice(s_main.bytes[IS_BRANCH_C1_POS - RLP_NUM], Rotation::prev());

            let key_rlc_prev = meta.query_advice(acc_pair.rlc, Rotation(-19));
            let key_rlc_cur = meta.query_advice(acc_pair.rlc, Rotation::cur());
            let key_rlc_mult_prev = meta.query_advice(acc_pair.mult, Rotation(-19));
            let key_rlc_mult_cur = meta.query_advice(acc_pair.mult, Rotation::cur());
            constraints.push((
                "key_rlc sel1",
                q_not_first.clone()
                    * not_first_level.clone()
                    * is_branch_init_prev.clone()
                    * (one.clone() - is_account_leaf_in_added_branch_prev.clone()) // When this is 0, we check as for the first level key rlc.
                    * (one.clone() - is_extension_node.clone())
                    * sel1_cur.clone()
                    * (key_rlc_cur.clone()
                        - key_rlc_prev.clone()
                        - modified_node_cur.clone() * c16.clone()
                            * key_rlc_mult_prev.clone()),
            ));
            constraints.push((
                "key_rlc sel2",
                q_not_first.clone()
                    * not_first_level.clone()
                    * is_branch_init_prev.clone()
                    * (one.clone() - is_account_leaf_in_added_branch_prev.clone()) // When this is 0, we check as for the first level key rlc.
                    * (one.clone() - is_extension_node.clone())
                    * sel2_cur.clone()
                    * (key_rlc_cur.clone()
                        - key_rlc_prev
                        - modified_node_cur.clone()
                            * key_rlc_mult_prev.clone()),
            ));

            constraints.push((
                "key_rlc_mult sel1",
                q_not_first.clone()
                    * not_first_level.clone()
                    * is_branch_init_prev.clone()
                    * (one.clone() - is_account_leaf_in_added_branch_prev.clone()) // When this is 0, we check as for the first level key rlc.
                    * (one.clone() - is_extension_node.clone())
                    * sel1_cur.clone()
                    * (key_rlc_mult_cur.clone() - key_rlc_mult_prev.clone()),
            ));
            constraints.push((
                "key_rlc_mult sel2",
                q_not_first.clone()
                    * not_first_level.clone()
                    * is_branch_init_prev.clone()
                    * (one.clone() - is_account_leaf_in_added_branch_prev.clone()) // When this is 0, we check as for the first level key rlc.
                    * (one.clone() - is_extension_node.clone())
                    * sel2_cur.clone()
                    * (key_rlc_mult_cur.clone() - key_rlc_mult_prev * acc_r),
            ));

            // Key (which actually means account address) in first level in account proof.
            constraints.push((
                "account first level key_rlc",
                q_not_first.clone()
                    * (one.clone() - not_first_level.clone())
                    * (one.clone() - is_extension_node.clone())
                    * is_branch_init_prev.clone()
                    * (key_rlc_cur.clone() - modified_node_cur.clone() * c16.clone()),
            ));
            constraints.push((
                "account first level key_rlc_mult",
                q_not_first.clone()
                    * (one.clone() - not_first_level.clone())
                    * (one.clone() - is_extension_node.clone())
                    * is_branch_init_prev.clone()
                    * (key_rlc_mult_cur.clone() - one.clone()),
            ));

            // First storage level.
            constraints.push((
                "storage first level key_rlc",
                q_not_first.clone()
                    * is_account_leaf_in_added_branch_prev.clone()
                    * (one.clone() - is_extension_node.clone())
                    * is_branch_init_prev.clone()
                    * (key_rlc_cur - modified_node_cur * c16),
            ));
            constraints.push((
                "storage first level key_rlc_mult",
                q_not_first.clone()
                    * is_account_leaf_in_added_branch_prev.clone()
                    * (one.clone() - is_extension_node.clone())
                    * is_branch_init_prev.clone()
                    * (key_rlc_mult_cur - one.clone()),
            ));

            // Selector constraints (sel1, sel2)

            constraints.push((
                "sel1 is bool",
                q_not_first.clone()
                    * is_branch_init_prev.clone()
                    * sel1_cur.clone()
                    * (sel1_cur.clone() - one.clone()),
            ));
            constraints.push((
                "sel2 is bool",
                q_not_first.clone()
                    * is_branch_init_prev.clone()
                    * sel2_cur.clone()
                    * (sel2_cur.clone() - one.clone()),
            ));
            constraints.push((
                "sel1 + sel2 = 1",
                q_not_first.clone()
                    * is_branch_init_prev.clone()
                    * (sel1_cur.clone() + sel2_cur.clone() - one.clone()),
            ));

            // Key RLC for extension node is checked in extension_node,
            // however, sel1 & sel2 are checked here (to avoid additional rotations).

            // First sel1 in account proof (implicitly constrains sel2 because of the
            // bool & sum constraints above).
            constraints.push((
                "account first level key_rlc sel1",
                q_not_first.clone()
                    * (one.clone() - not_first_level.clone())
                    * (one.clone() - is_extension_node.clone())
                    * is_branch_init_prev.clone()
                    * (sel1_cur.clone() - one.clone()),
            ));
            // If extension node, sel1 and sel2 in first level depend on the extension key
            // (even/odd). If key is even, the constraints stay the same. If key
            // is odd, the constraints get turned around. Note that even/odd
            // means for key nibbles (what we actually need here) and
            // not for key length in RLP (how many bytes key occupies in RLP).
            constraints.push((
                "account first level key_rlc sel1 = 1 (extension node even key)",
                q_not_first.clone()
                    * (one.clone() - not_first_level.clone())
                    * is_branch_init_prev.clone()
                    * is_extension_key_even.clone()
                    * (sel1_cur.clone() - one.clone()),
            ));
            constraints.push((
                "account first level key_rlc sel1 = 0 (extension node odd key)",
                q_not_first.clone()
                    * (one.clone() - not_first_level.clone())
                    * is_branch_init_prev.clone()
                    * is_extension_key_odd.clone()
                    * sel1_cur.clone(),
            ));

            // First sel1 in storage proof (sel2 implicitly)
            constraints.push((
                "storage first level key_rlc sel1 = 1",
                q_not_first.clone()
                    * is_account_leaf_in_added_branch_prev.clone()
                    * (one.clone() - is_extension_node.clone())
                    * is_branch_init_prev.clone()
                    * (sel1_cur.clone() - one.clone()),
            ));
            constraints.push((
                "storage first level key_rlc sel1 = 1 (extension node even key)",
                q_not_first.clone()
                    * is_account_leaf_in_added_branch_prev.clone()
                    * is_branch_init_prev.clone()
                    * is_extension_key_even.clone()
                    * (sel1_cur.clone() - one.clone()),
            ));
            constraints.push((
                "storage first level key_rlc sel1 = 0 (extension node odd key)",
                q_not_first.clone()
                    * is_account_leaf_in_added_branch_prev.clone()
                    * is_branch_init_prev.clone()
                    * is_extension_key_odd.clone()
                    * sel1_cur.clone(),
            ));

            // sel1 alernates between 0 and 1 (sel2 alternates implicitly)
            constraints.push((
                "sel1 0->1->0->...",
                q_not_first.clone()
                    * not_first_level.clone()
                    * is_branch_init_prev.clone()
                    * (one.clone() - is_account_leaf_in_added_branch_prev.clone()) // When this is 0, we check as for the first level key rlc.
                    * (one.clone() - is_extension_node.clone())
                    * (sel1_cur.clone() + sel1_prev.clone() - one.clone()),
            ));
            constraints.push((
                "sel1 0->1->0->... (extension node even key)",
                q_not_first.clone()
                    * not_first_level.clone()
                    * is_branch_init_prev.clone()
                    * (one.clone() - is_account_leaf_in_added_branch_prev.clone()) // When this is 0, we check as for the first level key rlc.
                    * is_extension_key_even.clone()
                    * (sel1_cur.clone() + sel1_prev.clone() - one.clone()),
            ));
            constraints.push((
                "extension node odd key stays the same",
                q_not_first.clone()
                    * not_first_level.clone()
                    * is_branch_init_prev.clone()
                    * (one.clone() - is_account_leaf_in_added_branch_prev.clone()) // When this is 0, we check as for the first level key rlc.
                    * is_extension_key_odd.clone()
                    * (sel1_cur.clone() - sel1_prev.clone()),
            ));

            constraints
        });

        config
    }
}
