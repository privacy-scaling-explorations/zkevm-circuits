use halo2_proofs::{
    circuit::Chip,
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, VirtualCells},
    poly::Rotation,
};
use pairing::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::{
    helpers::{get_bool_constraint, key_len_lookup, range_lookups},
    mpt::FixedTableTag,
    param::{BRANCH_ROWS_NUM, HASH_WIDTH, KECCAK_INPUT_WIDTH, KECCAK_OUTPUT_WIDTH},
};

#[derive(Clone, Debug)]
pub(crate) struct LeafValueConfig {}

// Verifies the hash of a leaf is in the parent branch. Verifies storage leaf
// RLP.
pub(crate) struct LeafValueChip<F> {
    config: LeafValueConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> LeafValueChip<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        inter_root: Column<Advice>,
        q_not_first: Column<Fixed>,
        not_first_level: Column<Advice>,
        is_leaf_value: Column<Advice>,
        s_rlp1: Column<Advice>,
        s_rlp2: Column<Advice>,
        s_advices: [Column<Advice>; HASH_WIDTH],
        s_mod_node_hash_rlc: Column<Advice>,
        c_mod_node_hash_rlc: Column<Advice>,
        keccak_table: [Column<Fixed>; KECCAK_INPUT_WIDTH + KECCAK_OUTPUT_WIDTH],
        acc_s: Column<Advice>,
        acc_mult_s: Column<Advice>,
        acc_c: Column<Advice>,
        sel1: Column<Advice>,
        sel2: Column<Advice>,
        key_rlc: Column<Advice>,
        key_rlc_mult: Column<Advice>, // to store key_rlc from previous row (to enable lookup)
        mult_diff: Column<Advice>,    /* to store leaf value S RLC from two rows above (to
                                       * enable lookup) */
        is_account_leaf_in_added_branch: Column<Advice>,
        is_branch_placeholder: Column<Advice>,
        is_s: bool,
        acc_r: F,
        fixed_table: [Column<Fixed>; 3],
    ) -> LeafValueConfig {
        let config = LeafValueConfig {};

        // TODO: use r_table

        // NOTE: Rotation -6 can be used here (in S and C leaf), because
        // s_mod_node_hash_rlc and c_mod_node_hash_rlc have the same value in all branch
        // rows (thus, the same value in branch node_index: 13 and branch
        // node_index: 15). The same holds for sel1 and sel2.
        let rot = -6;
        let mut rot_into_init = -20;
        let mut rot_into_account = -2;
        if !is_s {
            rot_into_init = -22;
            rot_into_account = -4;
        }
        let one = Expression::Constant(F::one());

        // RLC is needed in lookup below and in storage_root_in_account_leaf for
        // leaf without branch.
        meta.create_gate("Leaf & leaf value RLC", |meta| {
            let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
            let is_leaf = meta.query_advice(is_leaf_value, Rotation::cur());
            let q_enable = q_not_first * is_leaf;

            let mut constraints = vec![];

            let c128 = Expression::Constant(F::from(128));
            let c192 = Expression::Constant(F::from(192));
            let is_long = meta.query_advice(s_mod_node_hash_rlc, Rotation::cur());
            let is_short = meta.query_advice(c_mod_node_hash_rlc, Rotation::cur());
            let is_leaf_long = meta.query_advice(s_mod_node_hash_rlc, Rotation::prev());
            let is_leaf_short = meta.query_advice(c_mod_node_hash_rlc, Rotation::prev());
            let s_rlp1_prev = meta.query_advice(s_rlp1, Rotation::prev());
            let s_rlp1_cur = meta.query_advice(s_rlp1, Rotation::cur());

            constraints.push((
                "is_long is boolean",
                get_bool_constraint(q_enable.clone(), is_long.clone()),
            ));
            constraints.push((
                "is_short is boolean",
                get_bool_constraint(q_enable.clone(), is_long.clone()),
            ));
            constraints.push((
                "is_long + is_short = 1",
                q_enable.clone() * (is_long.clone() + is_short.clone() - one.clone()),
            ));

            // Note: is_short means value has only one byte and consequently, the RLP of
            // value is this byte itself. If there are more bytes, the value is
            // equipped with two RLP meta bytes, like 161 160 if there is a
            // value of length 32 (the first RLP byte means 33 bytes after it, the second
            // RLP byte means 32 bytes after it).

            let leaf_rlc_prev = meta.query_advice(acc_s, Rotation::prev());
            let leaf_mult_prev = meta.query_advice(acc_mult_s, Rotation::prev());
            let s_rlp2_prev = meta.query_advice(s_rlp2, Rotation::prev());
            let s_rlp2_cur = meta.query_advice(s_rlp2, Rotation::cur());

            let mut value_rlc_long = Expression::Constant(F::zero());
            let mut mult_long = F::one();
            for col in s_advices.iter() {
                let s = meta.query_advice(*col, Rotation::cur());
                value_rlc_long = value_rlc_long + s * mult_long.clone();
                mult_long = mult_long * acc_r;
            }

            let leaf_value_rlc =
                value_rlc_long.clone() * is_long.clone() + s_rlp1_cur.clone() * is_short.clone();

            let leaf_rlc_long = leaf_rlc_prev.clone()
                + s_rlp1_cur.clone() * leaf_mult_prev.clone()
                + s_rlp2_cur.clone() * leaf_mult_prev.clone() * acc_r.clone()
                + value_rlc_long.clone() * leaf_mult_prev.clone() * acc_r.clone() * acc_r;
            let leaf_rlc = leaf_rlc_long * is_long.clone()
                + (leaf_rlc_prev + s_rlp1_cur.clone() * leaf_mult_prev) * is_short.clone();

            let acc_s = meta.query_advice(acc_s, Rotation::cur());
            let acc_c_cur = meta.query_advice(acc_c, Rotation::cur());

            constraints.push(("Leaf RLC", q_enable.clone() * (acc_s - leaf_rlc)));
            constraints.push((
                "Leaf value RLC",
                q_enable.clone() * (acc_c_cur - leaf_value_rlc),
            ));

            // Constraints to enable lookup:
            // key RLC is in sel1, leaf value S RLC is in sel2 (for lookup it's needed also
            // leaf value C RLC, which is in acc_c)
            // NOTE: when placeholder leaf, prev value needs to be set to 0 - the witness
            // generator add all 0s as a placeholder leaf for this reason; no constraint
            // is needed for this 0s as the lookup will fail if otherwise.
            if !is_s {
                let key_c_rlc_from_prev = meta.query_advice(key_rlc, Rotation(-1));
                let key_c_rlc_from_cur = meta.query_advice(key_rlc_mult, Rotation::cur());
                let leaf_value_s_rlc_from_prev = meta.query_advice(acc_c, Rotation(-2));
                let leaf_value_s_rlc_from_cur = meta.query_advice(mult_diff, Rotation::cur());
                constraints.push((
                    "key C RLC",
                    q_enable.clone() * (key_c_rlc_from_prev - key_c_rlc_from_cur),
                ));
                constraints.push((
                    "leaf value S RLC",
                    q_enable.clone() * (leaf_value_s_rlc_from_prev - leaf_value_s_rlc_from_cur),
                ));
            }

            // If sel = 1, value = 0:
            // This is to prevent attacks where sel would be set to 1 to avoid
            // hash in parent constraints.
            let mut sel = meta.query_advice(sel1, Rotation(rot));
            if !is_s {
                sel = meta.query_advice(sel2, Rotation(rot));
            }
            let is_leaf_without_branch =
                meta.query_advice(is_account_leaf_in_added_branch, Rotation(rot_into_account));
            // For leaf without branch the constraint is in storage_root_in_account_leaf
            constraints.push((
                "Placeholder leaf (no value set) needs to have value = 0 (s_rlp1)",
                q_enable.clone()
                    * sel.clone()
                    * (one.clone() - is_leaf_without_branch.clone())
                    * s_rlp1_cur.clone(),
            ));
            constraints.push((
                "Placeholder leaf (no value set) needs to have value = 0 (s_rlp2)",
                q_enable.clone()
                    * sel.clone()
                    * (one.clone() - is_leaf_without_branch.clone())
                    * s_rlp2_cur.clone(),
            ));
            for col in s_advices.iter() {
                let s = meta.query_advice(*col, Rotation::cur());
                constraints.push((
                    "Placeholder leaf (no value set) needs to have value = 0",
                    q_enable.clone()
                        * sel.clone()
                        * (one.clone() - is_leaf_without_branch.clone())
                        * s.clone(),
                ));
            }

            // RLP constraints:
            let s_advices0_prev = meta.query_advice(s_advices[0], Rotation::prev());
            let short_remainder = s_rlp1_prev.clone() - c192.clone() - s_rlp2_prev.clone()
                + c128.clone()
                - one.clone();
            let long_remainder = s_rlp2_prev - s_advices0_prev + c128.clone() - one.clone();
            let long_value_len = s_rlp2_cur.clone() - c128.clone() + one.clone() + one.clone();

            let short_short_check = short_remainder.clone() - one.clone();
            let long_long_check = long_remainder - long_value_len.clone();
            let short_long_check = short_remainder - long_value_len;
            // Note: long short is not possible because the key has at most 32 bytes and
            // short value means only 1 byte which (together with RLP meta
            // bytes) cannot go over 55 bytes.

            let long_value_check = s_rlp1_cur - c128.clone() - s_rlp2_cur + c128 - one.clone();

            constraints.push((
                "RLP leaf short value short",
                q_enable.clone() * short_short_check * is_leaf_short.clone() * is_short.clone(),
            ));
            constraints.push((
                "RLP leaf long value long",
                q_enable.clone() * long_long_check * is_leaf_long.clone() * is_long.clone(),
            ));
            constraints.push((
                "RLP leaf short value long",
                q_enable.clone() * short_long_check * is_leaf_short.clone() * is_long.clone(),
            ));

            constraints.push((
                "RLP long value check",
                q_enable.clone() * long_value_check * is_long.clone(),
            ));

            // sel is set to 1 in leaf value row when leaf is without branch and it is a
            // placeholder - this appears when a first leaf is added to an empty
            // trie or when the only leaf is deleted from the trie.
            // This selector is used only to prevent checking the leaf hash being the
            // storage trie root (because leaf is just a placeholder) in
            // storage_root_in_account_leaf.
            // To prevent setting sel = 1 in cases when storage trie is not empty, the
            // constraints below are added.
            let empty_trie_hash: Vec<u8> = vec![
                86, 232, 31, 23, 27, 204, 85, 166, 255, 131, 69, 230, 146, 192, 248, 110, 91, 72,
                224, 27, 153, 108, 173, 192, 1, 98, 47, 181, 227, 99, 180, 33,
            ];
            let mut sel = meta.query_advice(sel1, Rotation::cur());

            // account leaf storage codehash S
            // account leaf storage codehash C
            // account leaf in added branch
            // leaf key S
            // leaf value S
            // leaf key C
            // leaf value C
            let mut rot_into_storage_root = -4;
            if !is_s {
                sel = meta.query_advice(sel2, Rotation::cur());
                rot_into_storage_root = -5;
            }
            for (ind, col) in s_advices.iter().enumerate() {
                let s = meta.query_advice(*col, Rotation(rot_into_storage_root));
                constraints.push((
                    "If placeholder leaf without branch (sel = 1), then storage trie is empty",
                    q_enable.clone()
                        * sel.clone()
                        * is_leaf_without_branch.clone()
                        * (s.clone() - Expression::Constant(F::from(empty_trie_hash[ind] as u64))),
                ));
            }

            constraints
        });

        meta.lookup_any("leaf hash in parent", |meta| {
            let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
            let not_first_level = meta.query_advice(not_first_level, Rotation::cur());
            let is_leaf = meta.query_advice(is_leaf_value, Rotation::cur());
            let q_enable = q_not_first * not_first_level * is_leaf;

            let rlc = meta.query_advice(acc_s, Rotation::cur());

            let mut placeholder_leaf = meta.query_advice(sel1, Rotation(rot));
            if !is_s {
                placeholder_leaf = meta.query_advice(sel2, Rotation(rot));
            }

            let is_branch_placeholder =
                meta.query_advice(is_branch_placeholder, Rotation(rot_into_init));

            // For leaf without branch, the constraints are in storage_root_in_account_leaf.
            let is_leaf_without_branch =
                meta.query_advice(is_account_leaf_in_added_branch, Rotation(rot_into_account));

            // If sel = 1, there is no leaf at this position (value is being added or
            // deleted) and we don't check the hash of it.
            let mut constraints = vec![];
            constraints.push((
                q_enable.clone()
                    * rlc
                    * (one.clone() - placeholder_leaf.clone())
                    * (one.clone() - is_leaf_without_branch.clone())
                    * (one.clone() - is_branch_placeholder.clone()),
                meta.query_fixed(keccak_table[0], Rotation::cur()),
            ));
            let mut mod_node_hash_rlc_cur = meta.query_advice(s_mod_node_hash_rlc, Rotation(rot));
            if !is_s {
                mod_node_hash_rlc_cur = meta.query_advice(c_mod_node_hash_rlc, Rotation(rot));
            }
            let keccak_table_i = meta.query_fixed(keccak_table[1], Rotation::cur());
            constraints.push((
                q_enable.clone()
                    * mod_node_hash_rlc_cur
                    * (one.clone() - placeholder_leaf.clone())
                    * (one.clone() - is_leaf_without_branch.clone())
                    * (one.clone() - is_branch_placeholder.clone()),
                keccak_table_i,
            ));

            constraints
        });

        // Lookup for case when there is a placeholder branch - in this case we need to
        // check the hash in the branch above the placeholder branch.
        meta.lookup_any("leaf hash in parent (branch placeholder)", |meta| {
            let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
            let not_first_level = meta.query_advice(not_first_level, Rotation::cur());
            let is_leaf = meta.query_advice(is_leaf_value, Rotation::cur());
            let q_enable = q_not_first * not_first_level * is_leaf;

            let mut rlc = meta.query_advice(acc_s, Rotation::prev());
            let mut mult = meta.query_advice(acc_mult_s, Rotation::prev());

            let s_rlp1 = meta.query_advice(s_rlp1, Rotation::cur());
            rlc = rlc + s_rlp1 * mult.clone();
            mult = mult * acc_r;

            let s_rlp2 = meta.query_advice(s_rlp2, Rotation::cur());
            rlc = rlc + s_rlp2 * mult.clone();
            mult = mult * acc_r;

            for col in s_advices.iter() {
                let s = meta.query_advice(*col, Rotation::cur());
                rlc = rlc + s * mult.clone();
                mult = mult * acc_r;
            }

            let mut sel = meta.query_advice(sel1, Rotation(rot));
            if !is_s {
                sel = meta.query_advice(sel2, Rotation(rot));
            }

            let is_branch_placeholder =
                meta.query_advice(is_branch_placeholder, Rotation(rot_into_init));

            // For leaf without branch, the constraints are in storage_root_in_account_leaf.
            let is_leaf_without_branch_after_placeholder = meta.query_advice(
                is_account_leaf_in_added_branch,
                Rotation(rot_into_account - BRANCH_ROWS_NUM),
            );
            let is_leaf_without_branch =
                meta.query_advice(is_account_leaf_in_added_branch, Rotation(rot_into_account));

            // Note: sel1 and sel2 in branch children: denote whether there is no leaf at
            // is_modified (when value is added or deleted from trie)

            // If sel = 1, there is no leaf at this position (value is being added or
            // deleted) and we don't check the hash of it.
            let mut constraints = vec![];
            constraints.push((
                q_enable.clone()
                    * rlc
                    * (one.clone() - sel.clone())
                    * (one.clone() - is_leaf_without_branch_after_placeholder.clone())
                    * (one.clone() - is_leaf_without_branch.clone())
                    * is_branch_placeholder.clone(),
                meta.query_fixed(keccak_table[0], Rotation::cur()),
            ));
            let mut mod_node_hash_rlc = meta.query_advice(
                s_mod_node_hash_rlc,
                Rotation(rot_into_init - 3), /* -3 to get from init branch into the previous
                                              * branch (last row), note that -2 is needed
                                              * because of extension nodes */
            );
            if !is_s {
                mod_node_hash_rlc =
                    meta.query_advice(c_mod_node_hash_rlc, Rotation(rot_into_init - 3));
            }

            let keccak_table_i = meta.query_fixed(keccak_table[1], Rotation::cur());
            constraints.push((
                q_enable.clone()
                    * mod_node_hash_rlc
                    * (one.clone() - sel.clone())
                    * (one.clone() - is_leaf_without_branch_after_placeholder.clone())
                    * (one.clone() - is_leaf_without_branch.clone())
                    * is_branch_placeholder.clone(),
                keccak_table_i,
            ));

            constraints
        });

        // Note: For cases when storage leaf is in the first storage level, the
        // constraints are in storage_root_in_account_leaf.

        // Check hash of a storage leaf to be state root when leaf without branch -
        // Note: probably not needed, except if the circuit is used without account
        // proof.
        // TODO: prepare test
        meta.lookup_any(
            "storage (no account proof) in first level leaf without branch - compared to root",
            |meta| {
                let mut constraints = vec![];
                let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
                let not_first_level = meta.query_advice(not_first_level, Rotation::cur());
                let is_leaf = meta.query_advice(is_leaf_value, Rotation::cur());

                let rlc = meta.query_advice(acc_s, Rotation::cur());
                let root = meta.query_advice(inter_root, Rotation::cur());

                constraints.push((
                    q_not_first.clone()
                        * is_leaf.clone()
                        * (one.clone() - not_first_level.clone())
                        * rlc,
                    meta.query_fixed(keccak_table[0], Rotation::cur()),
                ));
                let keccak_table_i = meta.query_fixed(keccak_table[1], Rotation::cur());
                constraints.push((
                    q_not_first * is_leaf * (one.clone() - not_first_level) * root,
                    keccak_table_i,
                ));

                constraints
            },
        );

        let sel = |meta: &mut VirtualCells<F>| {
            let not_first_level = meta.query_advice(not_first_level, Rotation::cur());
            let is_leaf = meta.query_advice(is_leaf_value, Rotation::cur());
            not_first_level * is_leaf
        };

        range_lookups(
            meta,
            sel,
            s_advices.to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );
        range_lookups(
            meta,
            sel,
            [s_rlp1, s_rlp2].to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );

        // There are zeros in s_advices after value:
        /*
        for ind in 0..HASH_WIDTH {
            key_len_lookup(
                meta,
                sel,
                ind + 1,
                s_rlp2,
                s_advices[ind],
                fixed_table,
            )
        }
        */

        config
    }

    pub fn construct(config: LeafValueConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }
}

impl<F: FieldExt> Chip<F> for LeafValueChip<F> {
    type Config = LeafValueConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}
