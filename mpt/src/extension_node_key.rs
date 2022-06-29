use halo2_proofs::{
    circuit::Chip,
    plonk::{
        Advice, Column, ConstraintSystem, Expression, Fixed, VirtualCells,
    },
    poly::Rotation,
};
use itertools::Itertools;
use pairing::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::{
    helpers::{compute_rlc, range_lookups, key_len_lookup, get_is_extension_node},
    mpt::FixedTableTag,
    param::{
        HASH_WIDTH,
        LAYOUT_OFFSET, IS_BRANCH_C16_POS, IS_BRANCH_C1_POS, IS_EXT_SHORT_C16_POS, IS_EXT_SHORT_C1_POS, IS_EXT_LONG_EVEN_C16_POS, IS_EXT_LONG_EVEN_C1_POS, IS_EXT_LONG_ODD_C16_POS, IS_EXT_LONG_ODD_C1_POS, EXTENSION_ROWS_NUM, BRANCH_ROWS_NUM,
    },
};

#[derive(Clone, Debug)]
pub(crate) struct ExtensionNodeKeyConfig {}

pub(crate) struct ExtensionNodeKeyChip<F> {
    config: ExtensionNodeKeyConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> ExtensionNodeKeyChip<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_not_first: Column<Fixed>,
        not_first_level: Column<Advice>, // to avoid rotating back when in the first branch (for key rlc)
        is_branch_init: Column<Advice>,
        is_branch_child: Column<Advice>,
        is_account_leaf_in_added_branch: Column<Advice>,
        s_rlp1: Column<Advice>,
        s_rlp2: Column<Advice>,
        c_rlp1: Column<Advice>,
        s_advices: [Column<Advice>; HASH_WIDTH],
        c_advices: [Column<Advice>; HASH_WIDTH],
        modified_node: Column<Advice>, // index of the modified node
        key_rlc: Column<Advice>, // used first for account address, then for storage key
        key_rlc_mult: Column<Advice>,
        mult_diff: Column<Advice>,
        is_extension_s_row: Column<Advice>,
        is_extension_c_row: Column<Advice>,
        fixed_table: [Column<Fixed>; 3],
        r_table: Vec<Expression<F>>,
    ) -> ExtensionNodeKeyConfig {
        let config = ExtensionNodeKeyConfig {};
        let one = Expression::Constant(F::one());
        let c128 = Expression::Constant(F::from(128));
        let c16 = Expression::Constant(F::from(16));
        let c16inv = Expression::Constant(F::from(16).invert().unwrap());
        let rot_into_branch_init = -BRANCH_ROWS_NUM+1;

        // Note: these constraints check whether extension C row key_rlc is properly computed (taking into
        // account nibbles) and the underlying branch key_rlc is properly computed (taking into account
        // modified_node). S and C branch / extension node always have the same key_rlc, so there are no constraints
        // for extension S row, except that extension S key_rlc is the same as extension C key_rlc (in case
        // rotation into S row is used to retrieve extension node key_rlc).

        meta.create_gate("extension node key", |meta| {
            let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
            let not_first_level =
                meta.query_advice(not_first_level, Rotation::cur());

            let mut constraints = vec![];

            // Could be used any rotation into previous branch, because key RLC is the same in all
            // branch children:
            let rot_into_prev_branch = rot_into_branch_init - EXTENSION_ROWS_NUM - 1;

            // To reduce the expression degree, we pack together multiple information.
            // Constraints on selectors are in extension_node.
            // NOTE: even and odd refers to number of nibbles that are compactly encoded.
            let is_ext_short_c16 = meta.query_advice(
                s_advices[IS_EXT_SHORT_C16_POS - LAYOUT_OFFSET],
                Rotation(rot_into_branch_init),
            );
            let is_ext_short_c1 = meta.query_advice(
                s_advices[IS_EXT_SHORT_C1_POS - LAYOUT_OFFSET],
                Rotation(rot_into_branch_init),
            );
            let is_ext_long_even_c16 = meta.query_advice(
                s_advices[IS_EXT_LONG_EVEN_C16_POS - LAYOUT_OFFSET],
                Rotation(rot_into_branch_init),
            );
            let is_ext_long_even_c1 = meta.query_advice(
                s_advices[IS_EXT_LONG_EVEN_C1_POS - LAYOUT_OFFSET],
                Rotation(rot_into_branch_init),
            );
            let is_ext_long_odd_c16 = meta.query_advice(
                s_advices[IS_EXT_LONG_ODD_C16_POS - LAYOUT_OFFSET],
                Rotation(rot_into_branch_init),
            );
            let is_ext_long_odd_c1 = meta.query_advice(
                s_advices[IS_EXT_LONG_ODD_C1_POS - LAYOUT_OFFSET],
                Rotation(rot_into_branch_init),
            );

            let is_extension_c_row =
                meta.query_advice(is_extension_c_row, Rotation::cur());

            let is_extension_node = get_is_extension_node(meta, s_advices, rot_into_branch_init);

            // sel1 and sel2 determines whether branch modified_node needs to be
            // multiplied by 16 or not. However, implicitly, sel1 and sel2 determines
            // also (together with extension node key length) whether the extension
            // node key nibble needs to be multiplied by 16 or not.
            
            let sel1 =
                meta.query_advice( s_advices[IS_BRANCH_C16_POS - LAYOUT_OFFSET], Rotation(rot_into_branch_init));
            let sel2 =
                meta.query_advice(s_advices[IS_BRANCH_C1_POS - LAYOUT_OFFSET], Rotation(rot_into_branch_init));

            // We are in extension row C, -18 brings us in the branch init row.
            // -19 is account leaf storage codehash when we are in the first storage proof level.
            let is_account_leaf_in_added_branch_prev = meta.query_advice(
                is_account_leaf_in_added_branch,
                Rotation(rot_into_branch_init-1),
            );

            let is_branch_init_prev =
                meta.query_advice(is_branch_init, Rotation::prev());
            let is_branch_child_prev =
                meta.query_advice(is_branch_child, Rotation::prev());
            let is_branch_child_cur =
                meta.query_advice(is_branch_child, Rotation::cur());

            // Any rotation that lands into branch children can be used:
            let modified_node_cur =
                meta.query_advice(modified_node, Rotation(-2));
            
            let key_rlc_prev = meta.query_advice(key_rlc, Rotation::prev());
            let key_rlc_prev_level = meta.query_advice(key_rlc, Rotation(rot_into_prev_branch));
            let key_rlc_cur = meta.query_advice(key_rlc, Rotation::cur());

            let mult_diff_cur = meta.query_advice(mult_diff, Rotation::cur());
            let mult_diff_prev = meta.query_advice(mult_diff, Rotation::prev());

            let key_rlc_mult_prev = meta.query_advice(key_rlc_mult, Rotation::prev());
            let key_rlc_mult_prev_level = meta.query_advice(key_rlc_mult, Rotation(rot_into_prev_branch));
            let key_rlc_mult_cur = meta.query_advice(key_rlc_mult, Rotation::cur());

            // Any rotation into branch children can be used:
            let key_rlc_branch = meta.query_advice(key_rlc, Rotation(rot_into_branch_init+1));
            let key_rlc_mult_branch = meta.query_advice(key_rlc_mult, Rotation(rot_into_branch_init+1));
            let mult_diff = meta.query_advice(mult_diff, Rotation(rot_into_branch_init+1));

            constraints.push((
                "branch key RLC same over all branch children with index > 0",
                q_not_first.clone()
                    * is_branch_child_prev.clone()
                    * is_branch_child_cur.clone()
                    * (key_rlc_cur.clone() - key_rlc_prev.clone()),
            ));
            constraints.push((
                "branch key RLC MULT same over all branch children with index > 0",
                q_not_first.clone()
                    * is_branch_child_prev.clone()
                    * is_branch_child_cur.clone()
                    * (key_rlc_mult_cur.clone() - key_rlc_mult_prev.clone()),
            ));
            constraints.push((
                "branch key MULT diff same over all branch children with index > 0",
                q_not_first.clone()
                    * is_branch_child_prev.clone()
                    * is_branch_child_cur.clone()
                    * (mult_diff_cur.clone() - mult_diff_prev.clone()),
            ));

            constraints.push((
                "extension node row S and C key RLC are the same",
                q_not_first.clone()
                    * is_extension_c_row.clone()
                    * is_extension_node.clone()
                    * (key_rlc_cur.clone() - key_rlc_prev.clone()),
            ));
            constraints.push((
                "extension node row S and C mult key RLC are the same",
                q_not_first.clone()
                    * is_extension_c_row.clone()
                    * is_extension_node.clone()
                    * (key_rlc_mult_cur.clone() - key_rlc_mult_prev.clone()),
            ));

            let s_rlp2 = meta.query_advice(s_rlp2, Rotation::prev());
            let s_advices0 = meta.query_advice(s_advices[0], Rotation::prev());
            let s_advices1 = meta.query_advice(s_advices[1], Rotation::prev());

            // long even not first level not first storage selector:
            let after_first_level = not_first_level.clone()
                    * (one.clone() - is_account_leaf_in_added_branch_prev.clone())
                    * is_extension_node.clone()
                    * is_extension_c_row.clone();

            // mult_prev = 1 if first level, mult_prev = key_rlc_mult_prev_level if not first level
            let mult_prev = after_first_level.clone() * key_rlc_mult_prev_level.clone() +
                one.clone() - after_first_level.clone();
            // rlc_prev = 0 if first level, rlc_prv = key_rlc_prev_level if not first level
            let rlc_prev = after_first_level.clone() * key_rlc_prev_level.clone();

            let mut long_even_rlc_sel1 = rlc_prev.clone() +
                s_advices1 * mult_prev.clone();
            // skip 1 because s_advices[0] is 0 and doesn't contain any key info, and skip another 1
            // because s_advices[1] is not to be multiplied by any r_table element (as it's in compute_rlc).
            long_even_rlc_sel1 = long_even_rlc_sel1.clone() + compute_rlc(
                meta,
                s_advices.iter().skip(2).map(|v| *v).collect_vec(),
                0,
                mult_prev.clone(),
                -1,
                r_table.clone(),
            );
            constraints.push((
                "long even sel1 extension",
                    q_not_first.clone()
                    * is_ext_long_even_c16.clone()
                    * is_extension_c_row.clone()
                    * (key_rlc_cur.clone() - long_even_rlc_sel1.clone())
            ));
            // We check branch key RLC in extension C row too (otherwise +rotation would be needed
            // because we first have branch rows and then extension rows):
            constraints.push((
                "long even sel1 branch",
                    q_not_first.clone()
                    * is_ext_long_even_c16.clone()
                    * is_extension_c_row.clone()
                    * (key_rlc_branch.clone() - key_rlc_cur.clone() -
                        c16.clone() * modified_node_cur.clone() * mult_prev.clone() * mult_diff.clone())
            ));
            constraints.push((
                "long even sel1 branch mult",
                    q_not_first.clone()
                    * is_ext_long_even_c16.clone()
                    * is_extension_c_row.clone()
                    * (key_rlc_mult_branch.clone() - mult_prev.clone() * mult_diff.clone())
                    // mult_diff is checked in a lookup below
            ));

            /* 
            Example:
            bytes: [228, 130, 16 + 3, 9*16 + 5, 0, ...]
            nibbles: [5, 0, ...]
            */
            // Note: sel1 and sel2 are turned around here (because of odd number of nibbles).
            let mut long_odd_sel2_rlc = rlc_prev.clone() +
                c16.clone() * (s_advices0.clone() - c16.clone()) * mult_prev.clone(); // -16 because of hexToCompact
            // s_advices0 - 16 = 3 in example above
            let mut mult = one.clone();
            for ind in 0..HASH_WIDTH-1 {
                let s = meta.query_advice(s_advices[1+ind], Rotation::prev());
                let second_nibble = meta.query_advice(s_advices[ind], Rotation::cur());
                let first_nibble = (s.clone() - second_nibble.clone()) * c16inv.clone();
                // Note that first_nibble and second_nibble need to be between 0 and 15 - this
                // is checked in a lookup below.
                constraints.push((
                    "long odd sel2 nibble correspond to byte",
                    q_not_first.clone()
                        * is_ext_long_odd_c1.clone()
                        * is_extension_c_row.clone()
                        * (s - first_nibble.clone() * c16.clone() - second_nibble.clone())
                ));

                long_odd_sel2_rlc = long_odd_sel2_rlc +
                    first_nibble.clone() * mult_prev.clone() * mult.clone();
                mult = mult * r_table[0].clone();

                long_odd_sel2_rlc = long_odd_sel2_rlc +
                    second_nibble.clone() * c16.clone() * mult_prev.clone() * mult.clone();
            }
            constraints.push((
                "long odd sel2 extension",
                    q_not_first.clone()
                        * is_ext_long_odd_c1.clone()
                        * is_extension_c_row.clone()
                        * (key_rlc_cur.clone() - long_odd_sel2_rlc.clone())
            ));
            // We check branch key RLC in extension C row too (otherwise +rotation would be needed
            // because we first have branch rows and then extension rows):
            constraints.push((
                "long odd sel2 branch",
                    q_not_first.clone()
                        * is_ext_long_odd_c1.clone()
                        * is_extension_c_row.clone()
                        * (key_rlc_branch.clone() - key_rlc_cur.clone() -
                            modified_node_cur.clone() * mult_prev.clone() * mult_diff.clone())
            ));
            constraints.push((
                "long odd sel2 branch mult",
                    q_not_first.clone()
                        * is_ext_long_odd_c1.clone()
                        * is_extension_c_row.clone()
                        * (key_rlc_mult_branch.clone() - mult_prev.clone() * mult_diff.clone() * r_table[0].clone())
                        // mult_diff is checked in a lookup below
            ));

            // short
 
            let short_sel1_rlc = rlc_prev.clone() +
                (s_rlp2.clone() - c16.clone()) * mult_prev.clone(); // -16 because of hexToCompact
            constraints.push((
                "short sel1 extension",
                    q_not_first.clone()
                        * is_ext_short_c16.clone()
                        * is_extension_c_row.clone()
                        * (key_rlc_cur.clone() - short_sel1_rlc.clone())
            ));
            // We check branch key RLC in extension C row too (otherwise +rotation would be needed
            // because we first have branch rows and then extension rows):
            constraints.push((
                "short sel1 branch",
                    q_not_first.clone()
                        * is_ext_short_c16.clone()
                        * is_extension_c_row.clone()
                        * (key_rlc_branch.clone() - key_rlc_cur.clone() -
                            c16.clone() * modified_node_cur.clone() * mult_prev.clone() * r_table[0].clone())
            ));
            constraints.push((
                "short sel1 branch mult",
                    q_not_first.clone()
                        * is_ext_short_c16.clone()
                        * is_extension_c_row.clone()
                        * (key_rlc_mult_branch.clone() - mult_prev.clone() * r_table[0].clone())
            ));

            /* 
            Note that there can be at max 31 key bytes because 32 same bytes would mean
            the two keys being the same - update operation, not splitting into extension node.
            So, we don't need to look further than s_advices even if the first byte (s_advices[0])
            is "padding".

            Example:
            bytes: [228, 130, 0, 9*16 + 5, 0, ...]
            nibbles: [5, 0, ...]
            Having sel2 means we need to:
                key_rlc_prev_level + first_nibble * key_rlc_mult_prev_level,
            However, we need to compute first_nibble (which is 9 in the example above).
            We get first_nibble by having second_nibble (5 in the example above) as the witness
            in extension row C and then: first_nibble = ((9*16 + 5) - 5) / 16.
            */
            let mut long_even_sel2_rlc = key_rlc_prev_level.clone();
            // Note: this can't appear in first level because it's sel2.

            let mut mult = one.clone();
            for ind in 0..HASH_WIDTH-1 {
                let s = meta.query_advice(s_advices[1+ind], Rotation::prev());
                let second_nibble = meta.query_advice(s_advices[ind], Rotation::cur());
                let first_nibble = (s.clone() - second_nibble.clone()) * c16inv.clone();
                // Note that first_nibble and second_nibble need to be between 0 and 15 - this
                // is checked in a lookup below.
                constraints.push((
                    "long even sel2 nibble correspond to byte",
                        q_not_first.clone()
                        * after_first_level.clone() // no need for check_extension here
                        * is_ext_long_even_c1.clone()
                        * (s - first_nibble.clone() * c16.clone() - second_nibble.clone())
                ));

                long_even_sel2_rlc = long_even_sel2_rlc +
                    first_nibble.clone() * key_rlc_mult_prev_level.clone() * mult.clone();
                mult = mult * r_table[0].clone();

                long_even_sel2_rlc = long_even_sel2_rlc +
                    second_nibble.clone() * c16.clone() * key_rlc_mult_prev_level.clone() * mult.clone();
            }
            constraints.push((
                "long even sel2 extension",
                        q_not_first.clone()
                        * after_first_level.clone()
                        * is_ext_long_even_c1.clone()
                        * (key_rlc_cur.clone() - long_even_sel2_rlc.clone())
            ));
            // We check branch key RLC in extension C row too (otherwise +rotation would be needed
            // because we first have branch rows and then extension rows):
            constraints.push((
                "long even sel2 branch",
                        q_not_first.clone()
                        * after_first_level.clone()
                        * is_ext_long_even_c1.clone()
                        * (key_rlc_branch.clone() - key_rlc_cur.clone() -
                            modified_node_cur.clone() * key_rlc_mult_prev_level.clone() * mult_diff.clone())
            ));
            constraints.push((
                "long even sel2 branch mult",
                        q_not_first.clone()
                        * after_first_level
                        * is_ext_long_even_c1.clone()
                        * (key_rlc_mult_branch.clone() - key_rlc_mult_prev_level.clone() * mult_diff.clone() * r_table[0].clone())
                        // mult_diff is checked in a lookup below
            ));

            // long odd not first level not first storage selector:
            let long_odd = q_not_first.clone()
                    * not_first_level.clone()
                    * (one.clone() - is_account_leaf_in_added_branch_prev.clone())
                    * is_extension_c_row.clone()
                    * (is_ext_long_odd_c16.clone() + is_ext_long_odd_c1.clone());
    
            /* 
            Example:
            bytes: [228, 130, 16 + 3, 137, 0, ...]
            nibbles: [5, 0, ...]
            */
            let mut long_odd_sel1_rlc = key_rlc_prev_level.clone() +
                (s_advices0 - c16.clone()) * key_rlc_mult_prev_level.clone();
            // skip 1 because s_advices[0] has already been taken into account
            long_odd_sel1_rlc = long_odd_sel1_rlc.clone() + compute_rlc(
                meta,
                s_advices.iter().skip(1).map(|v| *v).collect_vec(),
                0,
                key_rlc_mult_prev_level.clone(),
                -1,
                r_table.clone(),
            );
            constraints.push((
                "long odd sel1 extension",
                    long_odd.clone() // no need for check_extension here
                    * sel1.clone()
                    * (key_rlc_cur.clone() - long_odd_sel1_rlc.clone())
            ));
            // We check branch key RLC in extension C row too (otherwise +rotation would be needed
            // because we first have branch rows and then extension rows):
            constraints.push((
                "long odd sel1 branch",
                    long_odd.clone()
                    * sel1.clone()
                    * (key_rlc_branch.clone() - key_rlc_cur.clone() -
                        c16.clone() * modified_node_cur.clone() * key_rlc_mult_prev_level.clone() * mult_diff.clone())
            ));
            constraints.push((
                "long odd sel1 branch mult",
                    long_odd.clone()
                    * sel1.clone()
                    * (key_rlc_mult_branch.clone() - key_rlc_mult_prev_level.clone() * mult_diff.clone())
                    // mult_diff is checked in a lookup below
            ));

            // short: 
            let short = q_not_first.clone()
                * not_first_level.clone()
                * (one.clone() - is_account_leaf_in_added_branch_prev.clone())
                * is_extension_c_row.clone()
                * (is_ext_short_c16.clone() + is_ext_short_c1.clone());

            let short_sel2_rlc = key_rlc_prev_level.clone() +
                c16.clone() * (s_rlp2 - c16.clone()) * key_rlc_mult_prev_level.clone(); // -16 because of hexToCompact
            constraints.push((
                "short sel2 extension",
                    short.clone() // no need for check_extension here
                    * sel2.clone()
                    * (key_rlc_cur.clone() - short_sel2_rlc.clone())
            ));
            // We check branch key RLC in extension C row too (otherwise +rotation would be needed
            // because we first have branch rows and then extension rows):
            constraints.push((
                "short sel2 branch",
                    short.clone()
                    * sel2.clone()
                    * (key_rlc_branch.clone() - key_rlc_cur.clone() -
                        modified_node_cur.clone() * key_rlc_mult_prev_level.clone())
            ));
            constraints.push((
                "short sel2 branch mult",
                    short
                    * sel2.clone()
                    * (key_rlc_mult_branch.clone() - key_rlc_mult_prev_level.clone() * r_table[0].clone())
            ));

            constraints
        });

        let get_long_even = |meta: &mut VirtualCells<F>| {
            let is_account_leaf_in_added_branch_prev = meta.query_advice(
                is_account_leaf_in_added_branch,
                Rotation(rot_into_branch_init - 1),
            );

            let is_extension_c_row =
                meta.query_advice(is_extension_c_row, Rotation::cur());

            let is_ext_long_even_c16 = meta.query_advice(
                s_advices[IS_EXT_LONG_EVEN_C16_POS - LAYOUT_OFFSET],
                Rotation(rot_into_branch_init),
            );
            let is_ext_long_even_c1 = meta.query_advice(
                s_advices[IS_EXT_LONG_EVEN_C1_POS - LAYOUT_OFFSET],
                Rotation(rot_into_branch_init),
            );

            (one.clone() - is_account_leaf_in_added_branch_prev.clone())
                * is_extension_c_row.clone()
                * (is_ext_long_even_c16 + is_ext_long_even_c1)
        };

        let get_long_odd = |meta: &mut VirtualCells<F>| { 
            let is_account_leaf_in_added_branch_prev = meta.query_advice(
                is_account_leaf_in_added_branch,
                Rotation(rot_into_branch_init - 1),
            );
            let is_extension_c_row =
                meta.query_advice(is_extension_c_row, Rotation::cur());

            let is_ext_long_odd_c16 = meta.query_advice(
                s_advices[IS_EXT_LONG_ODD_C16_POS - LAYOUT_OFFSET],
                Rotation(rot_into_branch_init),
            );
            let is_ext_long_odd_c1 = meta.query_advice(
                s_advices[IS_EXT_LONG_ODD_C1_POS - LAYOUT_OFFSET],
                Rotation(rot_into_branch_init),
            );

            (one.clone() - is_account_leaf_in_added_branch_prev.clone())
                * is_extension_c_row.clone()
                * (is_ext_long_odd_c16 + is_ext_long_odd_c1)
        };

        // mult_diff
        meta.lookup_any("extension_node_key mult_diff", |meta| {
            let mut constraints = vec![];
            let not_first_level =
                meta.query_advice(not_first_level, Rotation::cur());

            let is_extension_c_row =
                meta.query_advice(is_extension_c_row, Rotation::cur());

            let is_ext_short_c16 = meta.query_advice(
                s_advices[IS_EXT_SHORT_C16_POS - LAYOUT_OFFSET],
                Rotation(rot_into_branch_init),
            );
            let is_ext_short_c1 = meta.query_advice(
                s_advices[IS_EXT_SHORT_C1_POS - LAYOUT_OFFSET],
                Rotation(rot_into_branch_init),
            );
            let is_ext_long_even_c16 = meta.query_advice(
                s_advices[IS_EXT_LONG_EVEN_C16_POS - LAYOUT_OFFSET],
                Rotation(rot_into_branch_init),
            );
            let is_ext_long_even_c1 = meta.query_advice(
                s_advices[IS_EXT_LONG_EVEN_C1_POS - LAYOUT_OFFSET],
                Rotation(rot_into_branch_init),
            );
            let is_ext_long_odd_c16 = meta.query_advice(
                s_advices[IS_EXT_LONG_ODD_C16_POS - LAYOUT_OFFSET],
                Rotation(rot_into_branch_init),
            );
            let is_ext_long_odd_c1 = meta.query_advice(
                s_advices[IS_EXT_LONG_ODD_C1_POS - LAYOUT_OFFSET],
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
                + is_ext_long_odd_c16.clone()
                + is_ext_long_odd_c1.clone();
            let is_short = is_ext_short_c16.clone()
                + is_ext_short_c1.clone();

            let is_even = is_ext_long_even_c16.clone() + is_ext_long_even_c1.clone();
            let s_rlp2 = meta.query_advice(s_rlp2, Rotation::prev());
            // key_len = s_rlp2 - 128 - 1   if long even
            // key_len = s_rlp2 - 128 - 1   if is_ext_long_odd_c1
            // key_len = s_rlp2 - 128       if is_ext_long_odd_c16
            // key_len = 1                  if short
            let key_len =
                (s_rlp2 - c128.clone() - one.clone() * is_even - one.clone() * is_ext_long_odd_c1.clone()) * is_long +
                is_short;

            let mult_diff = meta
                .query_advice(mult_diff, Rotation(rot_into_branch_init + 1));

            constraints.push((
                Expression::Constant(F::from(FixedTableTag::RMult as u64)),
                meta.query_fixed(fixed_table[0], Rotation::cur()),
            ));

            constraints.push((
                is_extension_c_row.clone() * is_extension_node.clone()
                    * key_len * not_first_level.clone(),
                meta.query_fixed(fixed_table[1], Rotation::cur()),
            ));
            constraints.push((
                is_extension_c_row.clone() * is_extension_node.clone()
                    * mult_diff * not_first_level.clone(),
                meta.query_fixed(fixed_table[2], Rotation::cur()),
            ));

            constraints
        });

        // second_nibble needs to be between 0 and 15.
        for ind in 0..HASH_WIDTH - 1 {
            meta.lookup_any("extension_node second nibble", |meta| {
                let mut constraints = vec![];
                let not_first_level =
                    meta.query_advice(not_first_level, Rotation::cur());

                let sel1 =
                    meta.query_advice( s_advices[IS_BRANCH_C16_POS - LAYOUT_OFFSET], Rotation(rot_into_branch_init));
                let sel2 =
                    meta.query_advice(s_advices[IS_BRANCH_C1_POS - LAYOUT_OFFSET], Rotation(rot_into_branch_init));

                let long_even_sel2 = get_long_even(meta) * sel2;
                let long_odd_sel1 = get_long_odd(meta) * sel1;

                let second_nibble =
                    meta.query_advice(s_advices[ind], Rotation::cur());

                constraints.push((
                    Expression::Constant(F::from(
                        FixedTableTag::Range16 as u64,
                    )),
                    meta.query_fixed(fixed_table[0], Rotation::cur()),
                ));
                constraints.push((
                    (long_even_sel2 + long_odd_sel1) * not_first_level * second_nibble,
                    meta.query_fixed(fixed_table[1], Rotation::cur()),
                ));

                constraints
            });
        }

        // first_nibble needs to be between 0 and 15.
        for ind in 0..HASH_WIDTH - 1 {
            meta.lookup_any("extension node first nibble", |meta| {
                let mut constraints = vec![];
                let not_first_level =
                    meta.query_advice(not_first_level, Rotation::cur());

                let sel1 =
                    meta.query_advice( s_advices[IS_BRANCH_C16_POS - LAYOUT_OFFSET], Rotation(rot_into_branch_init));
                let sel2 =
                    meta.query_advice(s_advices[IS_BRANCH_C1_POS - LAYOUT_OFFSET], Rotation(rot_into_branch_init));

                let long_even_sel2 = get_long_even(meta) * sel2;
                let long_odd_sel1 = get_long_odd(meta) * sel1;

                let s = meta.query_advice(s_advices[1 + ind], Rotation::prev());
                let second_nibble =
                    meta.query_advice(s_advices[ind], Rotation::cur());
                let first_nibble =
                    (s.clone() - second_nibble.clone()) * c16inv.clone();

                constraints.push((
                    Expression::Constant(F::from(
                        FixedTableTag::Range16 as u64,
                    )),
                    meta.query_fixed(fixed_table[0], Rotation::cur()),
                ));
                constraints.push((
                    (long_even_sel2 + long_odd_sel1) * not_first_level * first_nibble,
                    meta.query_fixed(fixed_table[1], Rotation::cur()),
                ));

                constraints
            });
        }

        let sel_short = |meta: &mut VirtualCells<F>| {
            let is_extension_s_row =
                meta.query_advice(is_extension_s_row, Rotation::cur());
            let is_ext_short_c16 = meta.query_advice(
                s_advices[IS_EXT_SHORT_C16_POS - LAYOUT_OFFSET],
                Rotation(rot_into_branch_init),
            );
            let is_ext_short_c1 = meta.query_advice(
                s_advices[IS_EXT_SHORT_C1_POS - LAYOUT_OFFSET],
                Rotation(rot_into_branch_init),
            );
            let is_short = is_ext_short_c16.clone()
                + is_ext_short_c1.clone();

            is_extension_s_row * is_short
        };
        let sel_long = |meta: &mut VirtualCells<F>| {
            let is_extension_s_row =
                meta.query_advice(is_extension_s_row, Rotation::cur());

            let is_ext_long_even_c16 = meta.query_advice(
                s_advices[IS_EXT_LONG_EVEN_C16_POS - LAYOUT_OFFSET],
                Rotation(rot_into_branch_init),
            );
            let is_ext_long_even_c1 = meta.query_advice(
                s_advices[IS_EXT_LONG_EVEN_C1_POS - LAYOUT_OFFSET],
                Rotation(rot_into_branch_init),
            );
            let is_ext_long_odd_c16 = meta.query_advice(
                s_advices[IS_EXT_LONG_ODD_C16_POS - LAYOUT_OFFSET],
                Rotation(rot_into_branch_init),
            );
            let is_ext_long_odd_c1 = meta.query_advice(
                s_advices[IS_EXT_LONG_ODD_C1_POS - LAYOUT_OFFSET],
                Rotation(rot_into_branch_init),
            );
            let is_long = is_ext_long_even_c16.clone()
                + is_ext_long_even_c1.clone()
                + is_ext_long_odd_c16.clone()
                + is_ext_long_odd_c1.clone();

            is_extension_s_row * is_long
        };

        // There are 0s after key length.
        /*
        for ind in 0..HASH_WIDTH {
            key_len_lookup(
                meta,
                sel_short,
                ind + 1,
                s_rlp2,
                s_advices[ind],
                fixed_table,
            )
        }

        for ind in 1..HASH_WIDTH {
            key_len_lookup(
                meta,
                sel_long,
                ind,
                s_advices[0],
                s_advices[ind],
                fixed_table,
            )
        }
        key_len_lookup(meta, sel_long, 32, s_advices[0], c_rlp1, fixed_table);
        */ 

        let sel_s = |meta: &mut VirtualCells<F>| {
            let is_extension_s_row =
                meta.query_advice(is_extension_s_row, Rotation::cur());

            get_is_extension_node(meta, s_advices, rot_into_branch_init+1) * is_extension_s_row
        };
        let sel_c = |meta: &mut VirtualCells<F>| {
            let is_extension_c_row =
                meta.query_advice(is_extension_c_row, Rotation::cur());

            get_is_extension_node(meta, s_advices, rot_into_branch_init) * is_extension_c_row
        };

        range_lookups(
            meta,
            sel_s,
            s_advices.to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );
        range_lookups(
            meta,
            sel_s,
            c_advices.to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );
        range_lookups(
            meta,
            sel_s,
            [s_rlp1, s_rlp2, c_rlp1].to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );
        // There is no need to check s_advices in C row as these bytes are checked
        // to be nibbles.
        range_lookups(
            meta,
            sel_c,
            c_advices.to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );
        range_lookups(
            meta,
            sel_c,
            [s_rlp1, s_rlp2, c_rlp1].to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );

        config
    }

    pub fn construct(config: ExtensionNodeKeyConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }
}

impl<F: FieldExt> Chip<F> for ExtensionNodeKeyChip<F> {
    type Config = ExtensionNodeKeyConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}
