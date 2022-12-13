use halo2_proofs::{
    arithmetic::FieldExt,
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, VirtualCells},
    poly::Rotation,
};
use itertools::Itertools;
use std::marker::PhantomData;

use crate::{
    mpt_circuit::columns::{AccumulatorCols, MainCols, PositionCols},
    mpt_circuit::helpers::{compute_rlc, get_is_extension_node, key_len_lookup, range_lookups},
    mpt_circuit::param::{
        BRANCH_ROWS_NUM, EXTENSION_ROWS_NUM, HASH_WIDTH, IS_BRANCH_C16_POS, IS_BRANCH_C1_POS,
        IS_EXT_LONG_EVEN_C16_POS, IS_EXT_LONG_EVEN_C1_POS, IS_EXT_LONG_ODD_C16_POS,
        IS_EXT_LONG_ODD_C1_POS, IS_EXT_SHORT_C16_POS, IS_EXT_SHORT_C1_POS, RLP_NUM,
    },
    mpt_circuit::FixedTableTag,
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

The constraints in `extension_node_key.rs` check the intermediate
key RLC (address RLC) in the extension node is properly computed. Here, we need to take into
account the extension node nibbles and the branch `modified_node`.

Other constraints for extension nodes, like checking that the branch hash
is in the extension node (the bytes `[30 252 ... 174]` in extension node rows present the hash
of the underlying branch) or checking the hash of the extension is in the parent node are
checking in `extension_node.rs`.
*/

#[derive(Clone, Debug)]
pub(crate) struct ExtensionNodeKeyConfig<F> {
    _marker: PhantomData<F>,
}

/*
TODO: extension node longer than 55 bytes - we leave this for now as it is very unlikely to happen.

ExtensionNodeConfig supports extension nodes longer than 55 bytes, however ExtensionNodeKeyConfig
currently does not. See below.

Currently, we do not store key for the C extension node - it is always the same as key for
the S extension node. However, it can happen that one extension node is longer than 55 bytes and one not
(being longer than 55 bytes is very unlikely because that would mean the extension need to be at least
22 bytes long - adding 32 for branch hash and 2 RLP bytes would give us 56).
In this case the longer than 55 bytes extension node starts as: [248, remaining_length, extension_bytes_length, ...],
while the shorter than 55 bytes extension node starts as: [247, extension_bytes_length, ...].

We do not have space to store C RLP & key into extension node C row as we already store key nibbles there (same
for both extension nodes).

The best seems to be to handle four different cases:
 - s_short, c_short (not to be confused with short/long meaning nibbles, here it means the whole ext. node longer or shorter than 55 bytes)
 - s_short, c_long
 - s_long, c_short
 - s_long, c_long

Using this approach we do not need to store C RLP & key, but it will increase the degree
(unless we pack this info together with short/long nibbles & c1/c16).
*/

impl<F: FieldExt> ExtensionNodeKeyConfig<F> {
    #[allow(clippy::too_many_arguments)]
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        position_cols: PositionCols<F>, /* `not_first_level` to avoid rotating back when in the
                                         * first branch (for
                                         * key rlc) */
        branch: BranchCols<F>,
        is_account_leaf_in_added_branch: Column<Advice>,
        s_main: MainCols<F>,
        c_main: MainCols<F>,
        accs: AccumulatorCols<F>, // accs.key used first for account address, then for storage key
        fixed_table: [Column<Fixed>; 3],
        power_of_randomness: [Expression<F>; HASH_WIDTH],
        check_zeros: bool,
    ) -> Self {
        let config = ExtensionNodeKeyConfig {
            _marker: PhantomData,
        };
        let one = Expression::Constant(F::one());
        let c128 = Expression::Constant(F::from(128));
        let c16 = Expression::Constant(F::from(16));
        let c16inv = Expression::Constant(F::from(16).invert().unwrap());
        let rot_into_branch_init = -BRANCH_ROWS_NUM + 1;

        /*
        When we have a regular branch (not in extension node), the key RLC is simple to compute:
        key_rlc = key_rlc_prev + modified_node * key_rlc_mult_prev * selMult

        The multiplier `selMult` being 16 or 1 depending on the number (even or odd) number
        of nibbles used in the levels above.

        Extension node makes it more complicated because we need to take into account its nibbles
        too. If there are for example two nibbles in the extension node `n1` and `n2` and if we
        assume that there have been even nibbles in the levels above, then:
        key_rlc = key_rlc_prev + n1 * key_rlc_mult_prev * 16 + n2 * key_rlc_mult_prev * 1 +
            modified_node * key_rlc_mult_prev * r * 16
        */
        meta.create_gate("Extension node key RLC", |meta| {
            let q_not_first = meta.query_fixed(position_cols.q_not_first, Rotation::cur());
            let not_first_level =
                meta.query_advice(position_cols.not_first_level, Rotation::cur());

            let mut constraints = vec![];

            let rot_into_prev_branch = rot_into_branch_init - EXTENSION_ROWS_NUM - 1;

            /*
            To reduce the expression degree, we pack together multiple information.
            Constraints on the selectors (like being boolean) are in extension_node.rs.

            Note: even and odd refers to the number of nibbles that are compactly encoded.
            */
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

            let is_extension_c_row =
                meta.query_advice(branch.is_extension_node_c, Rotation::cur());

            let is_extension_node = get_is_extension_node(meta, s_main.bytes, rot_into_branch_init);

            /*
            sel1 and sel2 gives the information whether the branch modified_node needs to be
            multiplied by 16 or not. However, implicitly, sel1 and sel2 determines
            also (together with the extension node key length) whether the extension
            node key nibble needs to be multiplied by 16 or not.

            For example if modified_node of the branch needs be multiplied by 16, that means
            there are even number of nibbles used above this branch. Now, if the extension node
            has even number of nibbles, that means there are even number of nibbles used above
            the extension node and we know we have to use the multiplier 16 for the first nibble
            of the extension node.
            */
            let sel1 =
                meta.query_advice( s_main.bytes[IS_BRANCH_C16_POS - RLP_NUM], Rotation(rot_into_branch_init));
            let sel2 =
                meta.query_advice(s_main.bytes[IS_BRANCH_C1_POS - RLP_NUM], Rotation(rot_into_branch_init));

            /*
            We are in extension row C, -18 brings us in the branch init row.
            -19 is account leaf storage codehash when we are in the first storage proof level.
            */
            let is_first_storage_level = meta.query_advice(
                is_account_leaf_in_added_branch,
                Rotation(rot_into_branch_init-1),
            );

            // Any rotation that lands into branch children can be used:
            let modified_node_cur =
                meta.query_advice(branch.modified_node, Rotation(-2));

            let key_rlc_ext_node_prev = meta.query_advice(accs.key.rlc, Rotation::prev());
            let key_rlc_prev_branch = meta.query_advice(accs.key.rlc, Rotation(rot_into_prev_branch));
            let key_rlc_ext_node_cur = meta.query_advice(accs.key.rlc, Rotation::cur());

            let key_rlc_mult_prev_branch = meta.query_advice(accs.key.mult, Rotation(rot_into_prev_branch));

            /*
            Note: `ext_node_key_mult` is not set, we always compute it by taking `branch_key_mult` from the branch above and multiplying it
            by `mult_diff` which reflects how many nibbles are in the extension node.
            */

            // Any rotation into branch children can be used:
            let key_rlc_branch = meta.query_advice(accs.key.rlc, Rotation(rot_into_branch_init+1));
            let key_rlc_mult_branch = meta.query_advice(accs.key.mult, Rotation(rot_into_branch_init+1));
            let mult_diff = meta.query_advice(accs.mult_diff, Rotation(rot_into_branch_init+1));

            /*
            Currently, the extension node S and extension node C both have the same key RLC -
            however, sometimes extension node can be replaced by a shorter extension node
            (in terms of nibbles), this is still to be implemented.
            */
            constraints.push((
                "Extension node row S and C key RLC are the same",
                q_not_first.clone()
                    * is_extension_c_row.clone()
                    * is_extension_node.clone()
                    * (key_rlc_ext_node_cur.clone() - key_rlc_ext_node_prev),
            ));

            let s_rlp2 = meta.query_advice(s_main.rlp2, Rotation::prev());
            let s_bytes0 = meta.query_advice(s_main.bytes[0], Rotation::prev());
            let s_bytes1 = meta.query_advice(s_main.bytes[1], Rotation::prev());

            let after_first_level = not_first_level.clone()
                    * (one.clone() - is_first_storage_level.clone())
                    * is_extension_node
                    * is_extension_c_row.clone();

            /*
            mult_prev is the multiplier to be used for the first nibble of the extension node.

            mult_prev = 1 if first level
            mult_prev = key_rlc_mult_prev_level if not first level
            */
            let mult_prev = after_first_level.clone() * key_rlc_mult_prev_branch +
                one.clone() - after_first_level.clone();

            /*
            rlc_prev is the RLC from the previous level. For example, if the extension node
            is an a branch, then rlc_prev is the intermediate key RLC computed in this branch.

            rlc_prev = 0 if first level
            rlc_prev = key_rlc_prev_level if not first level
            */
            let rlc_prev = after_first_level.clone() * key_rlc_prev_branch.clone();

            /*
            We first compute the intermediate RLC for the case when we have
            long even nibbles (meaning there is an even number of nibbles and this number is
            bigger than 1) and sel1 (branch modified_node needs to be multiplied by 16).

            sel1 means there are even number of nibbles above the branch, long even
            means there are even number of nibbles in the extension node, so there are even
            number of nibbles above the extension node.
            The example could be:
            [228,130,0,149,160,114,253,150,133,18,192,156,19,241,162,51,210,24,1,151,16,48,7,177,42,60,49,34,230,254,242,79,132,165,90,75,249]

            There is 0 at `s_main.bytes[0]` because there are even number of nibbles in the
            extension node (that is how EVM's `hexToCompact` function works).
            There are two nibbles `n1`, `n2` in this example and it holds:
            `s_main.bytes[1] = 149 = n1 * 16 + n2`.

            So, we first compute `rlc_prev + s_main.bytes[1] * mult_prev`.
            */
            let mut long_even_sel1_rlc = rlc_prev.clone() +
                s_bytes1 * mult_prev.clone();

            /*
            We then add the remaining nibbles - if there are more than two. Note that if there
            are only two, we will have 0s for `s_main.bytes[i]` for `i > 1`. Having 0s after the
            last nibble is checked by `key_len_lookup` constraints below.

            Skip one because s_main.bytes[0] is 0 and does not contain any key info, and skip another
            one because `s_main.bytes[1]` is not to be multiplied by any `r_table` element
            (how `compute_rlc` works).
            */
            long_even_sel1_rlc = long_even_sel1_rlc.clone() + compute_rlc(
                meta,
                s_main.bytes.iter().skip(2).copied().collect_vec(),
                0,
                mult_prev.clone(),
                -1,
                power_of_randomness.clone(),
            );

            /*
            We check the extension node intermediate RLC for the case when we have
            long even nibbles (meaning there is an even number of nibbles > 1)
            and sel1 (branch modified_node needs to be multiplied by 16).
            */
            constraints.push((
                "Long even sel1 extension node key RLC",
                    q_not_first.clone()
                    * is_ext_long_even_c16.clone()
                    * is_extension_c_row.clone()
                    * (key_rlc_ext_node_cur.clone() - long_even_sel1_rlc)
            ));

            /*
            Once we have extension node key RLC computed we need to take into account also the nibble
            corresponding to the branch (this nibble is `modified_node`):
            `key_rlc_branch = key_rlc_ext_node + modified_node * mult_prev * mult_diff * 16`

            Note that the multiplier used is `mult_prev * mult_diff`. This is because `mult_prev`
            is the multiplier to be used for the first extension node nibble, but we then
            need to take into account the number of nibbles in the extension node to have
            the proper multiplier for the `modified_node`. `mult_diff` stores the power or `r`
            such that the desired multiplier is `mult_prev * mult_diff`.
            However, `mult_diff` needs to be checked to correspond to the length of the nibbles
            (see `mult_diff` lookups below).

            We check branch key RLC in `IS_EXTENSION_NODE_C` row (and not in branch rows),
            otherwise +rotation would be needed
            because we first have branch rows and then extension rows.
            */
            constraints.push((
                "Long even sel1 extension node > branch key RLC",
                    q_not_first.clone()
                    * is_ext_long_even_c16.clone()
                    * is_extension_c_row.clone()
                    * (key_rlc_branch.clone() - key_rlc_ext_node_cur.clone() -
                        c16.clone() * modified_node_cur.clone() * mult_prev.clone() * mult_diff.clone())
            ));

            /*
            We need to check that the multiplier stored in a branch is:
            `key_rlc_mult_branch = mult_prev * mult_diff`.

            While we can use the expression `mult_prev * mult_diff` in the constraints in this file,
            we need to have `key_rlc_mult_branch` properly stored because it is accessed from the
            child nodes when computing the key RLC in child nodes.
            */
            constraints.push((
                "Long even sel1 extension node > branch key RLC mult",
                    q_not_first.clone()
                    * is_ext_long_even_c16
                    * is_extension_c_row.clone()
                    * (key_rlc_mult_branch.clone() - mult_prev.clone() * mult_diff.clone())
                    // mult_diff is checked in a lookup below
            ));

            /* 
            Long odd sel2 means there are odd number of nibbles and this number is bigger than 1.

            sel2 means there are odd number of nibbles above the branch, long odd
            means there are odd number of nibbles in the extension node, so there are even
            number of nibbles above the extension node:
            `nibbles_above_branch = nibbles_above_ext_node + ext_node_nibbles`.

            The example could be:
            [228, 130, 16 + 3, 9*16 + 5, 0, ...]

            In this example, we have three nibbles: `[3, 9, 5]`. Note that because the number of nibbles
            is odd, we have the first nibble already at position `s_main.bytes[0]` (16 is added to the
            first nibble in `hexToCompact` function). As opposed, in the above example where we had
            two nibbles, we had 0 at `s_main.bytes[0]`:
            [228,130,0,149,160,114,253,150,133,18,192,156,19,241,162,51,210,24,1,151,16,48,7,177,42,60,49,34,230,254,242,79,132,165,90,75,249]

            To get the first nibble we need to compute `s_main.bytes[0] - 16`.
            */
            let mut long_odd_sel2_rlc = rlc_prev.clone() +
                c16.clone() * (s_bytes0.clone() - c16.clone()) * mult_prev.clone();
            let mut mult = one.clone();

            /*
            When there are odd number of nibbles in the extension node, we need to know each
            nibble individually. When even number of nibbles this is not needed, because all we need
            is `n1 * 16 + n2`, `n3 * 16 + n4`, ... and we already have nibbles stored in that format
            in the extension node.
            When odd number, we have `n1 + 16`, `n2 * 16 + n3`, `n4 * 16 + n5`,...,
            but we need `n1 * 16 + n2`, `n3 * 16 + n4`,... (actually we need this only if there
            are also even number of nibbles above the extension node as is the case in long odd sel2).

            To get `n1 * 16 + n2`, `n3 * 16 + n4`,...
            from
            `n1 + 16`, `n2 * 16 + n3`, `n4 * 16 + n5`,...
            we store the nibbles `n3`, `n5`,... in
            `BRANCH.IS_EXTENSION_NODE_C` row.
            
            `BRANCH.IS_EXTENSION_NODE_S` and `BRANCH.IS_EXTENSION_NODE_C` rows of our example are thus:
            [228, 130, 16 + 3, 9*16 + 5, 0, ...]
            [5, 0, ...]

            We name the values in `BRANCH.IS_EXTENSION_NODE_C` as `second_nibbles`.
            Using the knowledge of `second_nibble` of the pair, we can compute `first_nibble`.
            Having a list of `first_nibble` and `second_nibble`, we can compute the key RLC.

            However, we need to check that the list of `second_nibbles` is correct. For example having
            `first_nibble = 9 = ((9*16 + 5) - 5) / 16`
            we check:
            `first_nibble * 16 + 5 = s_main.bytes[1]`.
            */
            for ind in 0..HASH_WIDTH-1 {
                let s = meta.query_advice(s_main.bytes[1+ind], Rotation::prev());
                let second_nibble = meta.query_advice(s_main.bytes[ind], Rotation::cur());
                let first_nibble = (s.clone() - second_nibble.clone()) * c16inv.clone();
                /*
                Note that first_nibble and second_nibble need to be between 0 and 15 - this
                is checked in a lookup below.
                */
                constraints.push((
                    "Long odd sel2 first_nibble second_nibble",
                    q_not_first.clone()
                        * is_ext_long_odd_c1.clone()
                        * is_extension_c_row.clone()
                        * (s - first_nibble.clone() * c16.clone() - second_nibble.clone())
                ));

                long_odd_sel2_rlc = long_odd_sel2_rlc +
                    first_nibble.clone() * mult_prev.clone() * mult.clone();
                mult = mult * power_of_randomness[0].clone();

                long_odd_sel2_rlc = long_odd_sel2_rlc +
                    second_nibble.clone() * c16.clone() * mult_prev.clone() * mult.clone();
            }

            /*
            We check the extension node intermediate RLC for the case when we have
            long odd nibbles (meaning there is an odd number of nibbles and this number is bigger than 1)
            and sel2 (branch `modified_node` needs to be multiplied by 1).

            Note that for the computation of the intermediate RLC we need `first_nibbles` and
            `second_nibbles` mentioned in the constraint above.
            */
            constraints.push((
                "Long odd sel2 extension node key RLC",
                    q_not_first.clone()
                        * is_ext_long_odd_c1.clone()
                        * is_extension_c_row.clone()
                        * (key_rlc_ext_node_cur.clone() - long_odd_sel2_rlc)
            ));

            /*
            Once we have extension node key RLC computed we need to take into account also the nibble
            corresponding to the branch (this nibble is `modified_node`):
            `key_rlc_branch = key_rlc_ext_node + modified_node * mult_prev * mult_diff * 1`.
            */
            constraints.push((
                "Long odd sel2 extension node > branch key RLC",
                    q_not_first.clone()
                        * is_ext_long_odd_c1.clone()
                        * is_extension_c_row.clone()
                        * (key_rlc_branch.clone() - key_rlc_ext_node_cur.clone() -
                            modified_node_cur.clone() * mult_prev.clone() * mult_diff.clone())
            ));

            /*
            We need to check that the multiplier stored in a branch is:
            `key_rlc_mult_branch = mult_prev * mult_diff * r_table[0]`.

            Note that compared to `Long even sel1` case, we have an additional factor
            `r` here. This is because we have even number of nibbles above the extension node
            and then we have odd number of nibbles in the extension node: this means the multiplier
            for `n1` (which is stored in `s_main.bytes[0]`) will need a multiplier  `key_rlc_mult_branch * r`.
            For `n3` we will need a multiplier  `key_rlc_mult_branch * r^2`,...
            The difference with `Long even sel1` is that here we have an additional nibble in
            `s_main.bytes[0]` which requires an increased multiplier.
            */
            constraints.push((
                "Long odd sel2 extension node > branch key RLC mult",
                    q_not_first.clone()
                        * is_ext_long_odd_c1.clone()
                        * is_extension_c_row.clone()
                        * (key_rlc_mult_branch.clone() - mult_prev.clone() * mult_diff.clone() * power_of_randomness[0].clone())
                        // mult_diff is checked in a lookup below
            ));

            let short_sel1_rlc = rlc_prev +
                (s_rlp2.clone() - c16.clone()) * mult_prev.clone(); // -16 because of hexToCompact

            /*
            Short means there is one nibble in the extension node
            sel1 means there are even number of nibbles above the branch,
            so there are odd number of nibbles above the extension node in this case:
            `nibbles_above_branch = nibbles_above_ext_node + 1`.

            We check the extension node intermediate RLC for the case when we have
            one nibble and sel1 (branch `modified_node` needs to be multiplied by 16).
            */
            constraints.push((
                "Short sel1 extension node key RLC",
                    q_not_first.clone()
                        * is_ext_short_c16.clone()
                        * is_extension_c_row.clone()
                        * (key_rlc_ext_node_cur.clone() - short_sel1_rlc)
            ));

            /*
            Once we have extension node key RLC computed we need to take into account also the nibble
            corresponding to the branch (this nibble is `modified_node`):
            `key_rlc_branch = key_rlc_ext_node + modified_node * mult_prev * mult_diff * 16`.

            Note: `mult_diff = r` because we only have one nibble in the extension node.
            */
            constraints.push((
                "Short sel1 extension node > branch key RLC",
                    q_not_first.clone()
                        * is_ext_short_c16.clone()
                        * is_extension_c_row.clone()
                        * (key_rlc_branch.clone() - key_rlc_ext_node_cur.clone() -
                            c16.clone() * modified_node_cur.clone() * mult_prev.clone() * power_of_randomness[0].clone())
            ));

            /*
            We need to check that the multiplier stored in a branch is:
            `key_rlc_mult_branch = mult_prev * r_table[0]`.
            */
            constraints.push((
                "Short sel1 extension node > branch key RLC mult",
                    q_not_first.clone()
                        * is_ext_short_c16.clone()
                        * is_extension_c_row.clone()
                        * (key_rlc_mult_branch.clone() - mult_prev.clone() * power_of_randomness[0].clone())
            ));

            /* 
            `Long even sel2` case is similar to `Long odd sel1` case above - similar in a way
            that we need helper values for `first_nibbles`.

            Here we have an even number of nibbles in the extension node and this number is bigger than 1.
            And `sel2` means branch `modified_node` needs to be multiplied by 1, which is the same as
            saying there are odd number of nibbles above the branch.
            It holds: `nibbles_above_branch = nibbles_above_ext_node + ext_node_nibbles`.
            That means we have an odd number of nibbles above extension node.

            Example:
            `[228, 130, 0, 9*16 + 5, 0, ...]` // we only have two nibbles here (`even`)
            `[5, 0, ...]`

            We cannot use directly `n1 * 16 + n2` (`9*16 + 5` in the example) when computing the key RLC
            because there is an odd number of nibbles above the extension node.
            So we first need to compute: `key_rlc_prev_branch + n1 * key_rlc_mult_prev_branch`.
            Which is the same as:
            `key_rlc_prev_branch + (s_main.bytes[1] - second_nibble)/16 * key_rlc_mult_prev_branch`.

            We then continue adding the rest of the nibbles.
            In our example there is only one more nibble, so the extension node key RLC is:
            `key_rlc_prev_branch + (s_main.bytes[1] - second_nibble)/16 * key_rlc_mult_prev_branch + first_nibble * key_rlc_mult_prev_branch * r * 16`.
            Note that we added a factor `r` because we moved to a new pair of nibbles (a new byte).
            */
            let mut long_even_sel2_rlc = key_rlc_prev_branch.clone();
            // Note: this cannot appear in the first level because it is sel2.

            let mut mult = one.clone();
            for ind in 0..HASH_WIDTH-1 {
                /*
                Note that there can be at max 31 key bytes because 32 same bytes would mean
                the two keys being the same - update operation, not splitting into extension node.
                So, we do not need to look further than `s_main.bytes` even if `s_main.bytes[0]`
                is not used (when even number of nibbles).
                */
                let s = meta.query_advice(s_main.bytes[1+ind], Rotation::prev());
                let second_nibble = meta.query_advice(s_main.bytes[ind], Rotation::cur());
                let first_nibble = (s.clone() - second_nibble.clone()) * c16inv.clone();

                /*
                With these constraints we ensure that the list of `second_nibbles` is correct.

                Note that first_nibble and second_nibble need to be between 0 and 15 - this
                is checked in a lookup below.
                */
                constraints.push((
                    "Long even sel2 first_nibble second_nibble",
                        q_not_first.clone()
                        * after_first_level.clone() // no need for check_extension here
                        * is_ext_long_even_c1.clone()
                        * (s - first_nibble.clone() * c16.clone() - second_nibble.clone())
                ));

                long_even_sel2_rlc = long_even_sel2_rlc +
                    first_nibble.clone() * mult_prev.clone() * mult.clone();
                mult = mult * power_of_randomness[0].clone();

                long_even_sel2_rlc = long_even_sel2_rlc +
                    second_nibble.clone() * c16.clone() * mult_prev.clone() * mult.clone();
            }

            /*
            We check the extension node intermediate RLC for the case when we have
            long even nibbles (meaning there is an even number of nibbles and this number is bigger than 1)
            and `sel2` (branch `modified_node` needs to be multiplied by 1).
            */
            constraints.push((
                "Long even sel2 extension node key RLC",
                        q_not_first.clone()
                        * after_first_level.clone()
                        * is_ext_long_even_c1.clone()
                        * (key_rlc_ext_node_cur.clone() - long_even_sel2_rlc)
            ));

            /*
            Once we have extension node key RLC computed we need to take into account also the nibble
            corresponding to the branch (this nibble is `modified_node`):
            `key_rlc_branch = key_rlc_ext_node + modified_node * key_rlc_mult_prev_branch * mult_diff * 1`
            */
            constraints.push((
                "Long even sel2 extension node > branch key RLC",
                        q_not_first.clone()
                        * after_first_level.clone()
                        * is_ext_long_even_c1.clone()
                        * (key_rlc_branch.clone() - key_rlc_ext_node_cur.clone() -
                            modified_node_cur.clone() * mult_prev.clone() * mult_diff.clone())
            ));

            /*
            We need to check that the multiplier stored in a branch is:
            `key_rlc_mult_branch = key_rlc_mult_prev_branch * mult_diff * r_table[0]`.
            */
            constraints.push((
                "Long even sel2 extension node > branch key RLC mult",
                        q_not_first.clone()
                        * after_first_level
                        * is_ext_long_even_c1
                        * (key_rlc_mult_branch.clone() - mult_prev.clone() * mult_diff.clone() * power_of_randomness[0].clone())
                        // mult_diff is checked in a lookup below
            ));

            // long odd not first level selector:
            let long_odd = q_not_first.clone()
                    * not_first_level.clone()
                    * (one.clone() - is_first_storage_level.clone())
                    * is_extension_c_row.clone()
                    * (is_ext_long_odd_c16 + is_ext_long_odd_c1);

            let mut long_odd_sel1_rlc = key_rlc_prev_branch.clone() +
                (s_bytes0 - c16.clone()) * mult_prev.clone();
            // skip 1 because s_main.bytes[0] has already been taken into account
            long_odd_sel1_rlc = long_odd_sel1_rlc.clone() + compute_rlc(
                meta,
                s_main.bytes.iter().skip(1).copied().collect_vec(),
                0,
                mult_prev.clone(),
                -1,
                power_of_randomness.clone(),
            );

            /*
            `Long odd` means there is an odd number of nibbles and the number is bigger than 1.
            `sel1` means there is an even number of nibbles above the branch.
            Thus, there is an odd number of nibbles above the extension node.
            Because of an odd number of nibbles in the extension node, we have the first
            nibble `n1` stored in `s_main.bytes[0]` (actually `n1 + 16`). We multiply it with 
            `key_rlc_mult_prev_branch`. Further nibbles are already paired in `s_main.bytes[i]`
            for `i > 0` and we do not need information about `second_nibbles`.
            */
            constraints.push((
                "Long odd sel1 extension node key RLC",
                    long_odd.clone() // no need for check_extension here
                    * sel1.clone()
                    * (key_rlc_ext_node_cur.clone() - long_odd_sel1_rlc)
            ));

            /*
            corresponding to the branch (this nibble is `modified_node`):
            `key_rlc_branch = key_rlc_ext_node + modified_node * key_rlc_mult_prev_branch * mult_diff * 16`
            */
            constraints.push((
                "Long odd sel1 extension node > branch key RLC",
                    long_odd.clone()
                    * sel1.clone()
                    * (key_rlc_branch.clone() - key_rlc_ext_node_cur.clone() -
                        c16.clone() * modified_node_cur.clone() * mult_prev.clone() * mult_diff.clone())
            ));

            /*
            We need to check that the multiplier stored in a branch is:
            `key_rlc_mult_branch = key_rlc_mult_prev_branch * mult_diff`.
            */
            constraints.push((
                "Long odd sel1 extension node > branch key RLC mult",
                    long_odd
                    * sel1
                    * (key_rlc_mult_branch.clone() - mult_prev.clone() * mult_diff)
                    // mult_diff is checked in a lookup below
            ));

            let short = q_not_first.clone()
                * not_first_level
                * (one.clone() - is_first_storage_level)
                * is_extension_c_row
                * (is_ext_short_c16.clone() + is_ext_short_c1.clone());

            let short_sel2_rlc = key_rlc_prev_branch +
                c16.clone() * (s_rlp2 - c16.clone()) * mult_prev.clone(); // -16 because of hexToCompact

            /*
            `Short` means there is only one nibble in the extension node.
            `sel2` means there are odd number of nibbles above the branch. 
            That means there are even number of nibbles above the extension node.

            Because of `short`, we have the first (and only) nibble in `s_main.rlp2`.
            We add this nibble to the previous key RLC to obtain the extension node key RLC.
            */
            constraints.push((
                "Short sel2 extension node key RLC",
                    short.clone() // no need for check_extension here
                    * sel2.clone()
                    * (key_rlc_ext_node_cur.clone() - short_sel2_rlc)
            ));

            /*
            Once we have extension node key RLC computed we need to take into account also the nibble
            corresponding to the branch (this nibble is `modified_node`):
            `key_rlc_branch = key_rlc_ext_node + modified_node * key_rlc_mult_prev_branch`.

            Note that there is no multiplication by power of `r` needed because `modified_node`
            nibble uses the same multiplier as the nibble in the extension node as the two
            of them form a byte in a key.
            */
            constraints.push((
                "Short sel2 branch extension node > branch key RLC",
                    short.clone()
                    * sel2.clone()
                    * (key_rlc_branch - key_rlc_ext_node_cur -
                        modified_node_cur * mult_prev.clone())
            ));

            /*
            We need to check that the multiplier stored in a branch is:
            `key_rlc_mult_branch = key_rlc_mult_prev_branch * r`.

            Note that we only need to multiply by `r`, because only one key byte is used
            in this extension node (one nibble in extension node + modified node nibble).
            */
            constraints.push((
                "Short sel2 branch extension node > branch key RLC mult",
                    short
                    * sel2
                    * (key_rlc_mult_branch - mult_prev * power_of_randomness[0].clone())
            ));

            let is_extension_s_row =
                meta.query_advice(branch.is_extension_node_s, Rotation::cur());

            /*
            We need to ensure `s_main.bytes` are all 0 when short - the only nibble is in `s_main.rlp2`.
            For long version, the constraints to have 0s after nibbles end in `s_main.bytes` are
            implemented using `key_len_lookup`.
            */
            for ind in 0..HASH_WIDTH {
                let s = meta.query_advice(s_main.bytes[ind], Rotation::cur());
                constraints.push((
                    "s_main.bytes[i] = 0 for short",
                        q_not_first.clone()
                        * is_extension_s_row.clone()
                        * (is_ext_short_c1.clone() + is_ext_short_c16.clone())
                        * s,
                ));
            }

            constraints
        });

        let get_long_even = |meta: &mut VirtualCells<F>| {
            let is_account_leaf_in_added_branch_prev = meta.query_advice(
                is_account_leaf_in_added_branch,
                Rotation(rot_into_branch_init - 1),
            );

            let is_extension_c_row = meta.query_advice(branch.is_extension_node_c, Rotation::cur());

            let is_ext_long_even_c16 = meta.query_advice(
                s_main.bytes[IS_EXT_LONG_EVEN_C16_POS - RLP_NUM],
                Rotation(rot_into_branch_init),
            );
            let is_ext_long_even_c1 = meta.query_advice(
                s_main.bytes[IS_EXT_LONG_EVEN_C1_POS - RLP_NUM],
                Rotation(rot_into_branch_init),
            );

            (one.clone() - is_account_leaf_in_added_branch_prev)
                * is_extension_c_row
                * (is_ext_long_even_c16 + is_ext_long_even_c1)
        };

        let get_long_odd = |meta: &mut VirtualCells<F>| {
            let is_account_leaf_in_added_branch_prev = meta.query_advice(
                is_account_leaf_in_added_branch,
                Rotation(rot_into_branch_init - 1),
            );
            let is_extension_c_row = meta.query_advice(branch.is_extension_node_c, Rotation::cur());

            let is_ext_long_odd_c16 = meta.query_advice(
                s_main.bytes[IS_EXT_LONG_ODD_C16_POS - RLP_NUM],
                Rotation(rot_into_branch_init),
            );
            let is_ext_long_odd_c1 = meta.query_advice(
                s_main.bytes[IS_EXT_LONG_ODD_C1_POS - RLP_NUM],
                Rotation(rot_into_branch_init),
            );

            (one.clone() - is_account_leaf_in_added_branch_prev)
                * is_extension_c_row
                * (is_ext_long_odd_c16 + is_ext_long_odd_c1)
        };

        /*
        It needs to be checked that `mult_diff` value corresponds to the number
        of the extension node nibbles. The information about the number of nibbles
        is encoded in `s_main.rlp2` - except in `short` case, but in this case we only
        have one nibble and we already know what value should have `mult_diff`.
        Thus, we check whether `(RMult, s_main.rlp2, mult_diff)` is in `fixed_table`.
        */
        meta.lookup_any("Extension node key mult_diff", |meta| {
            let mut constraints = vec![];
            let not_first_level = meta.query_advice(position_cols.not_first_level, Rotation::cur());

            let is_extension_c_row = meta.query_advice(branch.is_extension_node_c, Rotation::cur());

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

            let is_extension_node = is_ext_short_c16.clone()
                + is_ext_short_c1.clone()
                + is_ext_long_even_c16.clone()
                + is_ext_long_even_c1.clone()
                + is_ext_long_odd_c16.clone()
                + is_ext_long_odd_c1.clone();
            let is_long = is_ext_long_even_c16.clone()
                + is_ext_long_even_c1.clone()
                + is_ext_long_odd_c16
                + is_ext_long_odd_c1.clone();
            let is_short = is_ext_short_c16 + is_ext_short_c1;

            let is_even = is_ext_long_even_c16 + is_ext_long_even_c1;
            let s_rlp2 = meta.query_advice(s_main.rlp2, Rotation::prev());
            // key_len = s_rlp2 - 128 - 1   if long even
            // key_len = s_rlp2 - 128 - 1   if is_ext_long_odd_c1
            // key_len = s_rlp2 - 128       if is_ext_long_odd_c16
            // key_len = 1                  if short
            let key_len =
                (s_rlp2 - c128.clone() - one.clone() * is_even - one.clone() * is_ext_long_odd_c1)
                    * is_long
                    + is_short;

            let mult_diff = meta.query_advice(accs.mult_diff, Rotation(rot_into_branch_init + 1));

            constraints.push((
                Expression::Constant(F::from(FixedTableTag::RMult as u64)),
                meta.query_fixed(fixed_table[0], Rotation::cur()),
            ));

            constraints.push((
                is_extension_c_row.clone()
                    * is_extension_node.clone()
                    * key_len
                    * not_first_level.clone(),
                meta.query_fixed(fixed_table[1], Rotation::cur()),
            ));
            constraints.push((
                is_extension_c_row * is_extension_node * mult_diff * not_first_level,
                meta.query_fixed(fixed_table[2], Rotation::cur()),
            ));

            constraints
        });

        /*
        It needs to be checked that `second_nibbles` stored in `IS_EXTENSION_NODE_C` row
        are all between 0 and 15.
        */
        for ind in 0..HASH_WIDTH - 1 {
            meta.lookup_any("Extension node second_nibble", |meta| {
                let mut constraints = vec![];
                let not_first_level =
                    meta.query_advice(position_cols.not_first_level, Rotation::cur());

                let sel1 = meta.query_advice(
                    s_main.bytes[IS_BRANCH_C16_POS - RLP_NUM],
                    Rotation(rot_into_branch_init),
                );
                let sel2 = meta.query_advice(
                    s_main.bytes[IS_BRANCH_C1_POS - RLP_NUM],
                    Rotation(rot_into_branch_init),
                );

                /*
                Note that get_long_even also has is_extension_c factor, so this is checked
                only in IS_EXTENSION_NODE_C row.
                */
                let long_even_sel2 = get_long_even(meta) * sel2;
                let long_odd_sel1 = get_long_odd(meta) * sel1;

                let second_nibble = meta.query_advice(s_main.bytes[ind], Rotation::cur());

                constraints.push((
                    Expression::Constant(F::from(FixedTableTag::Range16 as u64)),
                    meta.query_fixed(fixed_table[0], Rotation::cur()),
                ));
                constraints.push((
                    (long_even_sel2 + long_odd_sel1) * not_first_level * second_nibble,
                    meta.query_fixed(fixed_table[1], Rotation::cur()),
                ));

                constraints
            });
        }

        let sel_long = |meta: &mut VirtualCells<F>| {
            let is_extension_s_row = meta.query_advice(branch.is_extension_node_s, Rotation::cur());

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
            let is_long = is_ext_long_even_c16
                + is_ext_long_even_c1
                + is_ext_long_odd_c16
                + is_ext_long_odd_c1;

            is_extension_s_row * is_long
        };

        /*
        `s_main.bytes[i] = 0` after last extension node nibble.

        Note that for a short version (only one nibble), all
        `s_main.bytes` need to be 0 (the only nibble is in `s_main.rlp2`) - this is checked
        separately.
        */
        if check_zeros {
            for ind in 1..HASH_WIDTH {
                key_len_lookup(
                    meta,
                    sel_long,
                    ind,
                    s_main.bytes[0],
                    s_main.bytes[ind],
                    128,
                    fixed_table,
                )
            }
            key_len_lookup(
                meta,
                sel_long,
                32,
                s_main.bytes[0],
                c_main.rlp1,
                128,
                fixed_table,
            );
        }

        let sel_s = |meta: &mut VirtualCells<F>| {
            let is_extension_s_row = meta.query_advice(branch.is_extension_node_s, Rotation::cur());

            get_is_extension_node(meta, s_main.bytes, rot_into_branch_init + 1) * is_extension_s_row
        };
        let sel_c = |meta: &mut VirtualCells<F>| {
            let is_extension_c_row = meta.query_advice(branch.is_extension_node_c, Rotation::cur());

            get_is_extension_node(meta, s_main.bytes, rot_into_branch_init) * is_extension_c_row
        };

        range_lookups(
            meta,
            sel_s,
            s_main.bytes.to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );
        range_lookups(
            meta,
            sel_s,
            c_main.bytes.to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );
        range_lookups(
            meta,
            sel_s,
            [s_main.rlp1, s_main.rlp2, c_main.rlp1].to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );

        /*
        There is no need to check s_main.bytes in C row as these bytes are checked
        to be nibbles.
        */
        range_lookups(
            meta,
            sel_c,
            c_main.bytes.to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );
        range_lookups(
            meta,
            sel_c,
            [s_main.rlp1, s_main.rlp2, c_main.rlp1].to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );

        config
    }
}
