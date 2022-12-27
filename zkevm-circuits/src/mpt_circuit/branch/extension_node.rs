use gadgets::util::{and, not, sum, Expr};
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Region, Value},
    plonk::{Advice, Column, Expression, Fixed, VirtualCells},
    poly::Rotation,
};
use std::marker::PhantomData;

use crate::{
    constraints,
    evm_circuit::util::rlc,
    mpt_circuit::columns::{AccumulatorCols, MainCols, PositionCols},
    mpt_circuit::helpers::{
        get_is_extension_node, get_is_extension_node_even_nibbles,
        get_is_extension_node_long_odd_nibbles, get_is_extension_node_one_nibble,
    },
    mpt_circuit::{helpers::extend_rand, witness_row::MptWitnessRow, MPTContext},
    mpt_circuit::{
        helpers::{get_branch_len, key_len_lookup, BaseConstraintBuilder},
        param::{
            ACCOUNT_LEAF_ROWS, ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND,
            ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND, BRANCH_ROWS_NUM, C_RLP_START, C_START, HASH_WIDTH,
            IS_BRANCH_C16_POS, IS_BRANCH_C1_POS, IS_BRANCH_C_PLACEHOLDER_POS,
            IS_BRANCH_S_PLACEHOLDER_POS, IS_C_EXT_LONGER_THAN_55_POS, IS_C_EXT_NODE_NON_HASHED_POS,
            IS_EXT_LONG_EVEN_C16_POS, IS_EXT_LONG_EVEN_C1_POS, IS_EXT_LONG_ODD_C16_POS,
            IS_EXT_LONG_ODD_C1_POS, IS_EXT_SHORT_C16_POS, IS_EXT_SHORT_C1_POS,
            IS_S_EXT_LONGER_THAN_55_POS, IS_S_EXT_NODE_NON_HASHED_POS, NIBBLES_COUNTER_POS,
            RLP_NUM,
        },
    },
    mpt_circuit::{MPTConfig, ProofValues},
    table::KeccakTable,
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

[1 0 1 0 248 81 0 248 81 0 14 1 0 6 1 0 0 0 0 1 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0]
[0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1]
[0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1]
[0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1]
[0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1]
[0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1]
[0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1]
[0 160 29 143 36 49 6 106 55 88 195 10 34 208 147 134 155 181 100 142 66 21 255 171 228 168 85 11 239 170 233 241 171 242 0 160 29 143 36 49 6 106 55 88 195 10 34 208 147 134 155 181 100 142 66 21 255 171 228 168 85 11 239 170 233 241 171 242 1]
[0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1]
[0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1]
[0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1]
[0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1]
[0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1]
[0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1]
[0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1]
[0 160 135 117 154 48 1 221 143 224 133 179 90 254 130 41 47 5 101 84 204 111 220 62 215 253 155 107 212 69 138 221 91 174 0 160 135 117 154 48 1 221 143 224 133 179 90 254 130 41 47 5 101 84 204 111 220 62 215 253 155 107 212 69 138 221 91 174 1]
[0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1]
[226 30 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 160 30 252 7 160 150 158 68 221 229 48 73 181 91 223 120 156 43 93 5 199 95 184 42 20 87 178 65 243 228 156 123 174 0 16]
[0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 160 30 252 7 160 150 158 68 221 229 48 73 181 91 223 120 156 43 93 5 199 95 184 42 20 87 178 65 243 228 156 123 174 0 17]

The last two rows present the extension node. This might be a bit misleading, because the extension
node appears in the trie above the branch (the first 17 rows).

The constraints in `extension_node.rs` check:
 - RLP of the node
 - that the branch hash is in the extension node (the bytes `[30 252 ... 174]` in extension node rows present the hash
of the underlying branch)
 - that the hash of the extension is in the parent node.
*/

#[derive(Clone, Debug, Default)]
pub(crate) struct ExtensionNodeConfig<F> {
    _marker: PhantomData<F>,
}

/*
Let's say we have branch1 and branch2 below it.

branch1 S row 0 || branch1 C row 0
...
branch1 S row 15 || branch1 C row 15

branch2 S row 0 || branch2 C row 0
...
branch2 S row 15 || branch2 C row 15

Hash of branch2 S is in one of the branch1 rows (in S columns).
Hash of branch2 C is in one of the branch1 rows (in C columns).

In what follows, we write branch without S and C - it is the same for both cases.

Key key1 determines the position of branch2 hash in branch1 (0-15).
To check this, branch2 RLC (over all RLP bytes - all 1+16 rows, 1 is for branch init row)
is checked to have a hash in branch1, at modified_node index
(modified_node depends on key key1).

However, with extension node it's a bit different.

branch1 S row 0 || branch1 C row 0
...
branch1 S row 15 || branch1 C row 15
extension1 S
extension1 C

branch2 S row 0 || branch2 C row 0
...
branch2 S row 15 || branch2 C row 15
extension2 S
extension2 C

There are additional rows immediately after branch 16 rows - one row for
extension node S and one row for extension node C. These rows are empty when
we have a regular branch.

Let's say branch2 is extension node. In this case, extension2 row contains:
  - key bytes that present the extension
  - hash of branch2

---
Example 1:

Key extension of length 2:
[228, 130, 0,          149,        160, 114,                    253,                     150,133,18,192,156,19,241,162,51,210,24,1,151,16,48,7,177,42,60,49,34,230,254,242,79,132,165,90,75,249]
[rlp, rlp, key byte 1, key byte 2, rlp, hash of branch2 byte 0, hash of branch2 byte 1, ...]
[0, 149] presents key extension:
  - 0 because it's even length (in branch it would be 16, see terminator)
  - 149 = 9*16 + 5
Key extension is [9, 5].

Two constraints are needed:
  - the hash of extension node (extension node RLC is needed) needs to be
    checked whether it's in branch1
  - the hash of branch2 is in extension node.

Also, it needs to be checked that key extension corresponds to key1 (not in this chip).

---
Example 2:

Key extension of length 1:
[226, 16,        160,172,105,12...
[rlp, key byte1, ...
[16] presents key extension:
  - 16 = 0 + 16
Key extension is [0].

*/

impl<F: FieldExt> ExtensionNodeConfig<F> {
    pub fn configure(
        meta: &mut VirtualCells<'_, F>,
        cb: &mut BaseConstraintBuilder<F>,
        ctx: MPTContext<F>,
        is_s: bool,
    ) -> Self {
        let position_cols = ctx.position_cols;
        let branch = ctx.branch;
        let s_main = ctx.s_main;
        let c_main = ctx.c_main;
        let accs = ctx.accumulators;
        let r = ctx.r;

        let c160_inv = Expression::Constant(F::from(160_u64).invert().unwrap());
        let inter_root = if is_s {
            ctx.inter_start_root
        } else {
            ctx.inter_final_root
        };
        constraints! {[meta, cb], {
            let rot_into_branch_init = if is_s {-17} else {-18};
            let rot = if is_s { 0 } else { -1 };

            let q_not_first = f!(position_cols.q_not_first);
            let not_first_level = a!(position_cols.not_first_level);
            let s_rlp2 = a!(s_main.rlp2);
            let c_rlp2 = a!(c_main.rlp2);
            let is_branch_init_prev = a!(branch.is_init, -1);
            let acc_s = a!(accs.acc_s.rlc, rot);

            // c_rlp2 = 160 when branch is hashed (longer than 31) and c_rlp2 = 0 otherwise
            let is_branch_hashed = c_rlp2.expr() * c160_inv.expr();

            // Note: hashed branch has 160 at c_rlp2 and hash in c_advices,
            // non-hashed branch has 0 at c_rlp2 and all the bytes in c_advices

            // Extension node RLC
            ifx!{q_not_first.expr() => {
                ifx!{not::expr(is_branch_init_prev.expr()) => {
                    // s_rlp1, s_rlp2, s_bytes need to be the same in both extension rows.
                    // However, to make space for nibble witnesses, we put nibbles in
                    // extension row C s_bytes. So we use s_bytes from S row.
                    let rlc = rlc::expr(
                        &s_main.rlp_bytes().iter().map(|&byte| a!(byte, rot)).collect::<Vec<_>>(),
                        &extend_rand(&r),
                    );
                    // The intermediate RLC after `s_main` bytes needs to be properly computed.
                    require!(rlc.expr() => acc_s.expr());

                    let acc_c = a!(accs.acc_c.rlc);
                    let acc_mult_s = a!(accs.acc_s.mult);
                    ifx!{is_branch_hashed.expr() => {
                        // Check whether the extension node RLC is properly computed.
                        // The RLC is used to check whether the extension node is a node at the appropriate position
                        // in the parent node. That means, it is used in a lookup to check whether
                        // `(extension_node_RLC, node_hash_RLC)` is in the keccak table.
                        let rlc_2 = acc_s.expr() + rlc::expr(
                            &c_main.rlp_bytes()[1..].iter().map(|&byte| acc_mult_s.expr() * a!(byte)).collect::<Vec<_>>(),
                            &r,
                        );
                        require!(acc_c.expr() => rlc_2.expr());
                    } elsex {
                        // Check whether the extension node (non-hashed) RLC is properly computed.
                        // The RLC is used to check whether the non-hashed extension node is a node at the appropriate position
                        // in the parent node. That means, there is a constraint to ensure that
                        // `extension_node_RLC = node_hash_RLC` for some `node` in parent branch.
                        let rlc_non_hashed_branch = acc_s.expr() + rlc::expr(
                            &c_main.rlp_bytes()[2..].iter().map(|&byte| acc_mult_s.expr() * a!(byte)).collect::<Vec<_>>(),
                            &r,
                        );
                        require!(acc_c.expr() => rlc_non_hashed_branch.expr());
                    }}
                }}
                ifx!{is_branch_hashed.expr() => {
                    // When the branch is hashed, we have `c_rlp2 = 160` because it specifies the length of the
                    // hash: `32 = 160 - 128`.
                    require!(c_rlp2.expr() => 160.expr());
                }}
            }}

            // Extension node selectors & RLP

            // NOTE: even and odd is for number of nibbles that are compactly encoded.

            // To reduce the expression degree, we pack together multiple information.
            let is_ext_short_c16 = meta.query_advice(
                s_main.bytes[IS_EXT_SHORT_C16_POS - RLP_NUM],
                Rotation(rot_into_branch_init),
            );
            let is_ext_short_c1 = meta.query_advice(
                s_main.bytes[IS_EXT_SHORT_C1_POS - RLP_NUM],
                Rotation(rot_into_branch_init),
            );
            let is_ext_long_even_c16 = meta.query_advice(
                s_main.bytes[IS_EXT_LONG_EVEN_C16_POS - RLP_NUM],
                Rotation(rot_into_branch_init),
            );
            let is_ext_long_even_c1 = meta.query_advice(
                s_main.bytes[IS_EXT_LONG_EVEN_C1_POS - RLP_NUM],
                Rotation(rot_into_branch_init),
            );
            let is_ext_long_odd_c16 = meta.query_advice(
                s_main.bytes[IS_EXT_LONG_ODD_C16_POS - RLP_NUM],
                Rotation(rot_into_branch_init),
            );
            let is_ext_long_odd_c1 = meta.query_advice(
                s_main.bytes[IS_EXT_LONG_ODD_C1_POS - RLP_NUM],
                Rotation(rot_into_branch_init),
            );
            let mut is_ext_longer_than_55 = meta.query_advice(
                s_main.bytes[IS_S_EXT_LONGER_THAN_55_POS - RLP_NUM],
                Rotation(rot_into_branch_init),
            );
            if !is_s {
                is_ext_longer_than_55 = meta.query_advice(
                    s_main.bytes[IS_C_EXT_LONGER_THAN_55_POS - RLP_NUM],
                    Rotation(rot_into_branch_init),
                );
            }
            let mut is_ext_node_non_hashed = s_main.bytes[IS_S_EXT_NODE_NON_HASHED_POS - RLP_NUM];
            if !is_s {
                is_ext_node_non_hashed = s_main.bytes[IS_C_EXT_NODE_NON_HASHED_POS - RLP_NUM];
            }
            let is_ext_node_non_hashed =
                meta.query_advice(is_ext_node_non_hashed, Rotation(rot_into_branch_init));

            let is_branch_init_prev = meta.query_advice(branch.is_init, Rotation::prev());

            // `short` means there is only one nibble in the extension node, `long` means there
            // are at least two. `even` means the number of nibbles is even, `odd` means the number
            // of nibbles is odd. `c16` means that above the branch there are even number of
            // nibbles (the same as saying that `modified_node` of the branch needs to be
            // multiplied by 16 in the computation of the key RLC), `c1` means
            // that above the branch there are odd number of
            // nibbles (the same as saying that `modified_node` of the branch needs to be
            // multiplied by 1 in the computation of the key RLC).
            let type_selectors = [
                is_ext_short_c16.expr(),
                is_ext_short_c1.expr(),
                is_ext_long_even_c16.expr(),
                is_ext_long_even_c1.expr(),
                is_ext_long_odd_c16.expr(),
                is_ext_long_odd_c1.expr(),
            ];

            let misc_selectors = [
                is_ext_longer_than_55.expr(),
                is_ext_node_non_hashed.expr(),
            ];

            ifx!{q_not_first.expr() => {
                ifx!{not::expr(is_branch_init_prev.expr()) => {
                    // We first check that the selectors in branch init row are boolean.
                    for selector in type_selectors.iter().chain(misc_selectors.iter()) {
                        require!(selector.expr() => bool);
                    }

                    // Only one of the six options can appear. When we have an extension node it holds:
                    // `is_ext_short_c16 + is_ext_short_c1 + is_ext_long_even_c16 + is_ext_long_even_c1 + is_ext_long_odd_c16 + is_ext_long_odd_c1 = 1`.
                    // And when it is a regular branch:
                    // `is_ext_short_c16 + is_ext_short_c1 + is_ext_long_even_c16 + is_ext_long_even_c1 + is_ext_long_odd_c16 + is_ext_long_odd_c1 = 0`.
                    // Note that if the attacker sets `is_extension_node = 1`
                    // for a regular branch (or `is_extension_node = 0` for the extension node),
                    // the final key RLC check fails because key RLC is computed differently
                    // for extension nodes and regular branches - a regular branch occupies only one
                    // key nibble (`modified_node`), while extension node occupies at least one additional
                    // nibble (the actual extension of the extension node).
                    // TODO(Brecht): not also misc_selectors?
                    require!(sum::expr(type_selectors.clone()) => 1.expr());

                    let is_branch_c16 = meta.query_advice(
                        s_main.bytes[IS_BRANCH_C16_POS - RLP_NUM],
                        Rotation(rot_into_branch_init),
                    );
                    let is_branch_c1 = meta.query_advice(
                        s_main.bytes[IS_BRANCH_C1_POS - RLP_NUM],
                        Rotation(rot_into_branch_init),
                    );

                    // TODO(Brecht): verify logic
                    // `is_branch_c16` and `is_branch_c1` information is duplicated with
                    // extension node selectors when we have an extension node (while in case of a regular
                    // branch the extension node selectors do not hold this information).
                    // That means when we have an extension node and `is_branch_c16 = 1`,
                    // there is `is_ext_short_c16 = 1` or
                    // `is_ext_long_even_c16 = 1` or `is_ext_long_odd_c16 = 1`.
                    // We have such a duplication to reduce the expression degree - for example instead of
                    // using `is_ext_long_even * is_branch_c16` we just use `is_ext_long_even_c16`.
                    // But we need to check that `is_branch_c16` and `is_branch_c1` are consistent
                    // with extension node selectors.
                    for (branch_selector, selectors) in [
                        (is_branch_c16.expr(), [is_ext_short_c16.expr(), is_ext_long_even_c16.expr(), is_ext_long_odd_c16.expr()]),
                        (is_branch_c1.expr(), [is_ext_short_c1.expr(), is_ext_long_even_c1.expr(), is_ext_long_odd_c1.expr()]),
                    ] {
                        for selector in selectors {
                            ifx!{selector.expr() => {
                                require!(selector.expr() => branch_selector.expr());
                            }
                        }}
                    }
                }}

                // In C we have nibbles, we check below only for S.
                if is_s {
                    let s_rlp1 = meta.query_advice(s_main.rlp1, Rotation::cur());
                    let s_bytes0 = meta.query_advice(s_main.bytes[0], Rotation::cur());

                    let is_short = is_ext_short_c16 + is_ext_short_c1;
                    let is_even_nibbles = is_ext_long_even_c16 + is_ext_long_even_c1;
                    let is_long_odd_nibbles = is_ext_long_odd_c16 + is_ext_long_odd_c1;

                    /*
                    This constraint prevents the attacker to set the number of nibbles to be even
                    when it is not even.
                    Note that when it is not even it holds `s_bytes0 != 0` (hexToCompact adds 16).

                    If the number of nibbles is 1, like in
                    `[226,16,160,172,105,12...`
                    there is no byte specifying the length.
                    If the number of nibbles is bigger than 1 and it is even, like in
                    `[228,130,0,149,160,114,253,150,133,18,192,156,19,241,162,51,210,24,1,151,16,48,7,177,42,60,49,34,230,254,242,79,132,165,90,75,249]`
                    the second byte (`s_main.rlp2`) specifies the length (we need to subract 128 to get it),
                    the third byte (`s_main.bytes[0]`) is 0.
                    */

                    ifx!{is_even_nibbles.expr() => {
                        // Long & even implies s_bytes0 = 0
                        require!(s_bytes0.expr() => 0.expr());
                    }}

                    let is_branch_hashed = c_rlp2 * c160_inv.clone();

                    let c_bytes0 = meta.query_advice(c_main.bytes[0], Rotation::cur());

                    ifx!{is_short.expr() => {
                        ifx!{is_branch_hashed.expr() => {
                            // We need to check that the length specified in `s_main.rlp1` corresponds to the actual
                            // length of the extension node.
                            // For example, in
                            // `[226,16,160,172,105,12...`
                            // we check that `226 - 192 = 1 + 32 + 1`.
                            // 1 is for `s_main.rlp2`, 32 is for 32 bytes of the branch hash,
                            // 1 is for the byte 160 which denotes the length
                            // of the hash (128 + 32).
                            require!(s_rlp1.expr() => 192.expr() + 33.expr() + 1.expr());
                        } elsex {
                            // We need to check that the length specified in `s_main.rlp1` corresponds to the actual
                            // length of the extension node.
                            // For example, in
                            // `[223,16,221,198,132,32,0,0,0,1,198,132,32,0,0,0,1,128,128,128,128,128,128,128,128,128,128,128,128,128,128,128]`
                            // we check that `223 - 192 = 1 + 29 + 1`.
                            // 1 is for `s_main.rlp2`,
                            // 29 is for the branch RLP (which is not hashed because it is shorter than 32 bytes),
                            // 1 is for `c_main.bytes[0]` which denotes the length of the branch RLP.
                            // TODO: prepare test
                            require!(s_rlp1.expr() => 192.expr() + 1.expr() + (c_bytes0.expr() - 192.expr() - 1.expr()));
                        }}
                    }}

                    ifx!{not::expr(is_ext_longer_than_55.expr()) => {
                        ifx!{is_even_nibbles.expr() + is_long_odd_nibbles.expr() => {
                            ifx!{is_branch_hashed.expr() => {
                                // We need to check that the length specified in `s_main.rlp1` corresponds to the actual
                                // length of the extension node.
                                // For example, in
                                // `[228,130,0,149,160,114,253...`
                                // we check that `228 - 192 = (130 - 128) + 1 + 32 + 1`.
                                // 1 is for `s_main.rlp2` which specifies the length of the nibbles part,
                                // 32 is for the branch hash,
                                // 1 is for the byte 160 which denotes the length
                                // of the hash (128 + 32).
                                require!(s_rlp1.expr() - 192.expr() => (s_rlp2.expr() - 128.expr()) + 1.expr() + 32.expr() + 1.expr());
                            } elsex {
                                // We need to check that the length specified in `s_main.rlp1` corresponds to the actual
                                // length of the extension node.
                                // We check that `s_main.rlp1 - 192` = `s_main.rlp2 - 128 + 1 + c_main.bytes[0] - 192 + 1`.
                                require!(s_rlp1.expr() - 192.expr() =>  s_rlp2.expr() - 128.expr() + 1.expr() + c_bytes0.expr() - 192.expr() + 1.expr());
                            }}
                        }}
                    } elsex {
                        // Note: ext longer than 55 RLP cannot appear when there is only one nibble because in this case
                        // we would have 1 byte for a nibble and at most 32 bytes for branch.

                        // When extension node RLP is longer than 55 bytes, the RLP has an additional byte
                        // at second position and the first byte specifies the length of the substream
                        // that specifies the length of the RLP. The substream is always just one byte: `s_main.rlp2`.
                        // And `s_main.rlp1 = 248` where `248 = 247 + 1` means the length of 1 byte.
                        // Example:
                        // `[248,67,160,59,138,106,70,105,186,37,13,38,205,122,69,158,202,157,33,95,131,7,227,58,235,229,3,121,188,90,54,23,236,52,68,161,160,...`
                        require!(s_rlp1.expr() => 248.expr());

                        ifx!{is_branch_hashed.expr() => {
                            // We need to check that the length specified in `s_main.rlp2` corresponds to the actual
                            // length of the extension node.
                            // Example:
                            // `[248,67,160,59,138,106,70,105,186,37,13,38,205,122,69,158,202,157,33,95,131,7,227,58,235,229,3,121,188,90,54,23,236,52,68,161,160,...`
                            // We check that `s_main.rlp2 = (s_main.bytes[0] - 128) + 1 + 32 + 1`.
                            // `s_main.bytes[0] - 128` specifies the extension node nibbles part,
                            // 1 is for `s_main.rlp2` which specifies the length of the RLP stream,
                            // 32 is for the branch hash,
                            // 1 is for the byte 160 which denotes the length of the hash (128 + 32).
                            // TODO: test
                            require!(s_rlp2.expr() => (s_bytes0.expr() - 248.expr()) + 1.expr() + 32.expr() + 1.expr());
                        } elsex {
                            // We need to check that the length specified in `s_main.rlp2` corresponds to the actual
                            // length of the extension node.
                            // We check that `s_main.rlp2 = (s_main.bytes[0] - 128) + 1 + c_main.bytes[0] - 192 + 1`.
                            // `s_main.bytes[0] - 128` specifies the extension node nibbles part,
                            // 1 is for `s_main.rlp2` which specifies the length of the RLP stream,
                            // `c_main.bytes[0] - 192` is for the branch RLP (which is not hashed because it is shorter than 32 bytes),
                            // 1 is for the byte 160 which denotes the length of the hash (128 + 32).
                            // TODO: test
                            // TODO(Brecht): changed from s_rlp1
                            require!(s_rlp2.expr() => (s_bytes0.expr() - 128.expr()) + 1.expr() + (c_bytes0.expr() + 192.expr() - 1.expr()));
                        }}
                    }}
                }

                // Some observations:

                // [228,130,0,149,160,114,253,150,133,18,192,156,19,241,162,51,210,24,1,151,16,48,7,177,42,60,49,34,230,254,242,79,132,165,90,75,249]
                // Note that the first element (228 in this case) can go much higher - for example, if there
                // are 40 nibbles, this would take 20 bytes which would make the first element 248.

                // If only one byte in key:
                // [226,16,160,172,105,12...

                // Extension node with non-hashed branch:
                // List contains up to 55 bytes (192 + 55)
                // [247,160,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,213,128,194,32,1,128,194,32,1,128,128,128,128,128,128,128,128,128,128,128,128,128]

                // List contains more than 55 bytes
                // [248,58,159,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,217,128,196,130,32,0,1,128,196,130,32,0,1,128,128,128,128,128,128,128,128,128,128,128,128,128]

                // Note that the extension node can be much shorter than the one above - in case when
                // there are less nibbles, so we cannot say that 226 appears as the first byte only
                // when there are hashed nodes in the branch and there is only one nibble.
                // Branch with two non-hashed nodes (that's the shortest possible branch):
                // [217,128,196,130,32,0,1,128,196,130,32,0,1,128,128,128,128,128,128,128,128,128,128,128,128,128]
                // Note: branch contains at least 26 bytes. 192 + 26 = 218

                // If proofEl[0] <= 247 (length at most 55, so proofEl[1] doesn't specify the length of the whole
                //     remaining stream, only of the next substream)
                // If proofEl[1] <= 128:
                //     There is only 1 byte for nibbles (keyLen = 1) and this is proofEl[1].
                // Else:
                //     Nibbles are stored in more than 1 byte, proofEl[1] specifies the length of bytes.
                // Else:
                // proofEl[1] contains the length of the remaining stream.
                // proofEl[2] specifies the length of the bytes (for storing nibbles).
                // Note that we can't have only one nibble in this case.
            }}

            // Note: acc_mult is checked in `extension_node_key.rs`.

            ifx!{q_not_first.expr() => {
                let acc_pair = if is_s {accs.clone().acc_s} else {accs.clone().acc_c};
                let acc_rot = if is_s {-1} else {-2};
                // TODO: acc currently doesn't have branch ValueNode info (which 128 if nil)
                let branch_acc = a!(acc_pair.rlc, acc_rot) + 128.expr() * a!(acc_pair.mult, acc_rot);
                let branch_len = get_branch_len(meta, s_main.clone(), rot_into_branch_init, is_s);
                let hash_rlc = rlc::expr(
                    &c_main.bytes.iter().map(|&byte| a!(byte)).collect::<Vec<_>>(),
                    &r,
                );

                ifx!{is_branch_hashed.expr() => {
                    ifx!{not::expr(is_branch_init_prev.expr()) => {
                        /* Extension node branch hash in extension row */
                        // Check whether branch hash is in the extension node row - we check that the branch hash RLC
                        // (computed over the first 17 rows) corresponds to the extension node hash stored in
                        // the extension node row. That means `(branch_RLC, extension_node_hash_RLC`) needs to
                        // be in a keccak table.
                        require!((branch_acc.expr(), branch_len.expr(), hash_rlc.expr()) => @keccak);
                    }}
                } elsex {
                    /* Extension node branch hash in extension row (non-hashed branch) */
                    // Check whether branch is in extension node row (non-hashed branch) -
                    // we check that the branch RLC is the same as the extension node branch part RLC
                    // (RLC computed over `c_main.bytes`).
                    // Note: there need to be 0s after branch ends in the extension node `c_main.bytes`
                    // (see below).
                    require!(branch_acc.expr() => hash_rlc.expr());
                }}

                // Note: Correspondence between nibbles in C and bytes in S is checked in
                // extension_node_key.

                let mut rot_into_branch_init = -17;
                let mut rot_into_last_branch_child = -1;
                let mut is_branch_placeholder = meta.query_advice(
                    s_main.bytes[IS_BRANCH_S_PLACEHOLDER_POS - RLP_NUM],
                    Rotation(rot_into_branch_init),
                );
                if !is_s {
                    rot_into_branch_init = -18;
                    rot_into_last_branch_child = -2;
                    is_branch_placeholder = meta.query_advice(
                        s_main.bytes[IS_BRANCH_C_PLACEHOLDER_POS - RLP_NUM],
                        Rotation(rot_into_branch_init),
                    );
                }

                // Only check if there is an account above the leaf.
                let is_account_leaf_in_added_branch = meta.query_advice(
                    ctx.account_leaf.is_in_added_branch,
                    Rotation(rot_into_branch_init - 1),
                );

                let is_extension_node =
                    get_is_extension_node(meta, s_main.bytes, rot_into_branch_init);

                // We need to do the lookup only if we are in the last branch child.
                let is_after_last_branch_child =
                    meta.query_advice(branch.is_last_child, Rotation(rot_into_last_branch_child));


                // TODO(Brecht): COPIED(branch_hash_in_parent)
                // Modified -19 -> -21
                let mod_node_hash_rlc = if is_s { accs.clone().s_mod_node_rlc } else { accs.c_mod_node_rlc };
                // Any rotation that lands into branch can be used instead of -21.
                let mod_node_hash_rlc = a!(mod_node_hash_rlc, -21);

                // Note: acc_c in both cases.
                let ext_acc = a!(accs.acc_c.rlc);
                // Length
                let rot = if is_s {0} else {-1};
                let ext_len = a!(s_main.rlp1, rot) - 192.expr() + 1.expr();

                ifx!{not_first_level.expr() => {
                    ifx!{not::expr(is_branch_placeholder.expr()) => {
                        ifx!{is_account_leaf_in_added_branch.expr() => {
                            ifx!{is_extension_node.expr(), is_after_last_branch_child.expr() => {
                                // TODO(Brecht): Should not be in q_not_first?
                                /* Extension node in first level of storage trie - hash compared to the storage root */
                                // When extension node is in the first level of the storage trie, we need to check whether
                                // `hash(ext_node) = storage_trie_root`. We do this by checking whether
                                // `(ext_node_RLC, storage_trie_root_RLC)` is in the keccak table.
                                // Note: extension node in the first level cannot be shorter than 32 bytes (it is always hashed).
                                // TODO(Brecht): COPIED(branch_hash_in_parent)
                                let storage_index = if is_s {ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND} else {ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND};
                                let rot = rot_into_branch_init - (ACCOUNT_LEAF_ROWS - storage_index);
                                // Note: storage root is always in s_main.bytes.
                                let hash_rlc = rlc::expr(
                                    &s_main.bytes.iter().map(|&byte| a!(byte, rot)).collect::<Vec<_>>(),
                                    &r,
                                );
                                require!((ext_acc.expr(), ext_len.expr(), hash_rlc.expr()) => @keccak);
                            }}
                        } elsex {
                            ifx!{is_ext_node_non_hashed.expr() => {
                                /* Extension node in parent branch (non-hashed extension node) */
                                // When an extension node is not hashed, we do not check whether it is in a parent
                                // branch using a lookup (see above), instead we need to check whether the branch child
                                // at `modified_node` position is exactly the same as the extension node.
                                require!(branch_acc.expr() => mod_node_hash_rlc.expr());
                            } elsex {
                                // TODO(Brecht): Should not be in q_not_first?
                                /* Extension node hash in parent branch */
                                // Check whether the extension node hash is in the parent branch.
                                // That means we check whether
                                // `(extension_node_RLC, node_hash_RLC)` is in the keccak table where `node` is a parent
                                // branch child at `modified_node` position.
                                // Note: do not check if it is in the first storage level (see `storage_root_in_account_leaf.rs`).
                                require!((ext_acc.expr(), ext_len.expr(), mod_node_hash_rlc.expr()) => @keccak);
                            }}
                        }}
                    }}
                } elsex {
                    /* Account first level extension node hash - compared to root */
                    // When we have an extension node in the first level of the account trie,
                    // its hash needs to be compared to the root of the trie.
                    // Note: the branch counterpart is implemented in `branch_hash_in_parent.rs`.
                    require!((ext_acc.expr(), ext_len.expr(), a!(inter_root)) => @keccak);
                }}
            }}

            // We need to make sure the total number of nibbles is 64. This constraint ensures the number
            // of nibbles used (stored in branch init) is correctly computed - nibbles up until this
            // extension node + nibbles in this extension node.
            // Once in a leaf, the remaining nibbles stored in a leaf need to be added to the count.
            // The final count needs to be 64.
            if is_s {
                ifx!{q_not_first.expr() => {
                    let is_ext_longer_than_55 = meta.query_advice(
                        s_main.bytes[IS_S_EXT_LONGER_THAN_55_POS - RLP_NUM],
                        Rotation(rot_into_branch_init),
                    );
                    let is_short =
                        get_is_extension_node_one_nibble(meta, s_main.bytes, rot_into_branch_init);
                    let is_even_nibbles =
                        get_is_extension_node_even_nibbles(meta, s_main.bytes, rot_into_branch_init);
                    let is_long_odd_nibbles = get_is_extension_node_long_odd_nibbles(
                        meta,
                        s_main.bytes,
                        rot_into_branch_init,
                    );

                    // Note: for regular branches, the constraint that `nibbles_count` increases
                    // by 1 is in `branch.rs`.

                    let nibbles_count_cur = meta.query_advice(
                        s_main.bytes[NIBBLES_COUNTER_POS - RLP_NUM],
                        Rotation(rot_into_branch_init),
                    );
                    // nibbles_count_prev needs to be 0 when in first account level or
                    // in first storage level
                    let is_first_storage_level = meta.query_advice(
                        ctx.account_leaf.is_in_added_branch,
                        Rotation(rot_into_branch_init - 1),
                    );
                    let nibbles_count_prev = not::expr(is_first_storage_level) * not_first_level * meta.query_advice(
                        s_main.bytes[NIBBLES_COUNTER_POS - RLP_NUM],
                        Rotation(rot_into_branch_init - BRANCH_ROWS_NUM),
                    );

                    // When there is only one nibble in the extension node, `nibbles_count` changes
                    // for 2: one nibble and `modified_node` in a branch.
                    ifx!{is_short.expr() => {
                        // +1 for nibble, +1 is for branch position
                        require!(nibbles_count_cur.expr() => nibbles_count_prev.clone() + 1.expr() + 1.expr());
                    }}

                    ifx!{is_even_nibbles.expr() => {
                        ifx!{is_ext_longer_than_55.expr() => {
                            // When there is an even number of nibbles in the extension node and the extension
                            // node is longer than 55 bytes, the number of bytes containing the nibbles
                            // is given by `s_main.bytes[0]`.
                            // We compute the number of nibbles as: `(s_bytes0 - 128 - 1) * 2`.
                            // By `s_bytes0 - 128` we get the number of bytes where nibbles are compressed, but
                            // then we need to subtract 1 because `s_main.bytes[1]` does not contain any nibbles
                            // (it is just 0 when even number of nibbles).
                            let num_nibbles = (a!(s_main.bytes[0]) - 128.expr() - 1.expr()) * 2.expr();
                            // +1 is for branch position
                            require!(nibbles_count_cur.expr() => nibbles_count_prev.clone() + num_nibbles.expr() + 1.expr());
                        } elsex {
                            // When there is an even number of nibbles in the extension node,
                            // we compute the number of nibbles as: `(s_rlp2 - 128 - 1) * 2`.
                            // By `s_rlp2 - 128` we get the number of bytes where nibbles are compressed, but
                            // then we need to subtract 1 because `s_main.bytes[0]` does not contain any nibbles
                            // (it is just 0 when even number of nibbles).
                            // In the example below it is: `(130 - 128 - 1) * 2`.
                            // `[228,130,0,149,160,114,253...`
                            let num_nibbles = (s_rlp2.expr() - 128.expr() - 1.expr()) * 2.expr();
                            // +1 is for branch position
                            require!(nibbles_count_cur.expr() => nibbles_count_prev.clone() + num_nibbles.expr() + 1.expr());
                        }}
                    }}

                    ifx!{is_long_odd_nibbles.expr() => {
                        ifx!{is_ext_longer_than_55.expr() => {
                            // When there is an odd number of nibbles in the extension node and the extension,
                            // node is longer than 55 bytes, the number of bytes containing the nibbles
                            // is given by `s_main.bytes[0]`.
                            // We compute the number of nibbles as: `(s_main.bytes[0] - 128) * 2`.
                            // By `s_main.bytes[0] - 128` we get the number of bytes where nibbles are compressed. We
                            // multiply by 2 to get the nibbles, but then subtract 1 because in
                            // `s_main.bytes[1]` there is only 1 nibble.
                            // Example:
                            // `[248,58,159,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,217,128,196,130,32,0,1,128,196,130,32,0,1,128,128,128,128,128,128,128,128,128,128,128,128,128]`
                            let num_nibbles = (a!(s_main.bytes[0]) - 128.expr()) * 2.expr() - 1.expr();
                            // +1 is for branch position
                            require!(nibbles_count_cur.expr() => nibbles_count_prev.clone() + num_nibbles.expr() + 1.expr());
                        } elsex {
                            // When there is an odd number of nibbles in the extension node,
                            // we compute the number of nibbles as: `(s_rlp2 - 128) * 2`.
                            // By `s_rlp2 - 128` we get the number of bytes where nibbles are compressed. We
                            // multiply by 2 to get the nibbles, but then subtract 1 because in
                            // `s_main.bytes[0]` there is only 1 nibble.
                            let num_nibbles = (s_rlp2.expr() - 128.expr()) * 2.expr() - 1.expr();
                            // +1 is for branch position
                            require!(nibbles_count_cur.expr() => nibbles_count_prev.clone() + num_nibbles.expr() + 1.expr());
                        }}
                    }}
                }}
            }

            /*let sel_branch_non_hashed = |meta: &mut VirtualCells<F>| {
                let q_not_first = meta.query_fixed(position_cols.q_not_first, Rotation::cur());
                let q_enable = q_enable(meta);

                let c_rlp2 = meta.query_advice(c_main.rlp2, Rotation::cur());
                // c_rlp2 = 160 when branch is hashed (longer than 31) and c_rlp2 = 0 otherwise
                let is_branch_hashed = c_rlp2 * c160_inv.clone();

                q_not_first * q_enable * (1.expr() - is_branch_hashed)
            };

            // There are 0s after non-hashed branch ends in `c_main.bytes`.
            if check_zeros {
                for ind in 1..HASH_WIDTH {
                    key_len_lookup(
                        meta,
                        sel_branch_non_hashed,
                        ind,
                        c_main.bytes[0],
                        c_main.bytes[ind],
                        192,
                        fixed_table,
                    )
                }
            }*/
        }}

        ExtensionNodeConfig {
            _marker: PhantomData,
        }
    }

    pub fn assign(
        &self,
        region: &mut Region<'_, F>,
        mpt_config: &MPTConfig<F>,
        pv: &mut ProofValues<F>,
        row: &MptWitnessRow<F>,
        offset: usize,
        is_s: bool,
    ) {
        if pv.is_extension_node {
            if is_s {
                // [228,130,0,149,160,114,253,150,133,18,192,156,19,241,162,51,210,24,1,151,16,
                // 48,7,177,42,60,49,34,230,254,242,79,132,165,90,75,249]

                // One nibble:
                // [226,16,160,172,105,12...
                // Could also be non-hashed branch:
                // [223,16,221,198,132,32,0,0,0,1,198,132,32,0,0,0,1,128,128,128,128,128,128,
                // 128,128,128,128,128,128,128,128,128]

                // [247,160,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
                // 213,128,194,32,1,128,194,32,1,128,128,128,128,128,128,128,128,128,128,128,
                // 128,128] [248,58,159,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
                // 0,0,0,0,0,0,0,0,0,0,0,0,217,128,196,130,32,0,1,128,196,130,32,0,1,128,128,
                // 128,128,128,128,128,128,128,128,128,128,128]

                // Intermediate RLC value and mult (after key)
                // to know which mult we need to use in c_advices.
                pv.acc_s = F::zero();
                pv.acc_mult_s = F::one();
                let len: usize;
                if row.get_byte(1) <= 32 {
                    // key length is 1
                    len = 2 // [length byte, key]
                } else if row.get_byte(0) < 248 {
                    len = (row.get_byte(1) - 128) as usize + 2;
                } else {
                    len = (row.get_byte(2) - 128) as usize + 3;
                }
                mpt_config.compute_acc_and_mult(
                    &row.bytes,
                    &mut pv.acc_s,
                    &mut pv.acc_mult_s,
                    0,
                    len,
                );

                // Final RLC value.
                pv.acc_c = pv.acc_s;
                pv.acc_mult_c = pv.acc_mult_s;
                let mut start = C_RLP_START + 1;
                let mut len = HASH_WIDTH + 1;
                if row.get_byte(C_RLP_START + 1) == 0 {
                    // non-hashed branch in extension node
                    start = C_START;
                    len = HASH_WIDTH;
                }
                mpt_config.compute_acc_and_mult(
                    &row.bytes,
                    &mut pv.acc_c,
                    &mut pv.acc_mult_c,
                    start,
                    len,
                );

                mpt_config
                    .assign_acc(region, pv.acc_s, pv.acc_mult_s, pv.acc_c, F::zero(), offset)
                    .ok();
            } else {
                // We use intermediate value from previous row (because
                // up to acc_s it's about key and this is the same
                // for both S and C).
                pv.acc_c = pv.acc_s;
                pv.acc_mult_c = pv.acc_mult_s;
                let mut start = C_RLP_START + 1;
                let mut len = HASH_WIDTH + 1;
                if row.get_byte(C_RLP_START + 1) == 0 {
                    // non-hashed branch in extension node
                    start = C_START;
                    len = HASH_WIDTH;
                }
                mpt_config.compute_acc_and_mult(
                    &row.bytes,
                    &mut pv.acc_c,
                    &mut pv.acc_mult_c,
                    start,
                    len,
                );

                mpt_config
                    .assign_acc(region, pv.acc_s, pv.acc_mult_s, pv.acc_c, F::zero(), offset)
                    .ok();
            }
            region
                .assign_advice(
                    || "assign key_rlc".to_string(),
                    mpt_config.accumulators.key.rlc,
                    offset,
                    || Value::known(pv.extension_node_rlc),
                )
                .ok();
        }
    }
}
