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
    param::{HASH_WIDTH, KECCAK_INPUT_WIDTH, KECCAK_OUTPUT_WIDTH},
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
        sel: Column<Advice>,
        is_account_leaf_storage_codehash_c: Column<Advice>,
        is_branch_placeholder: Column<Advice>,
        is_s: bool,
        acc_r: F,
        fixed_table: [Column<Fixed>; 3],
    ) -> LeafValueConfig {
        let config = LeafValueConfig {};
        let one = Expression::Constant(F::one());

        // TODO: check values are 0 after RLP stream ends (to prevent attacks on RLC)

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
            let mut is_leaf = meta.query_advice(is_leaf_value, Rotation::cur());
            let q_enable = q_not_first * is_leaf;

            let mut constraints = vec![];

            let c128 = Expression::Constant(F::from(128));
            let c192 = Expression::Constant(F::from(192));
            let c248 = Expression::Constant(F::from(248));
            let is_long = meta.query_advice(s_mod_node_hash_rlc, Rotation::cur());
            let is_short = meta.query_advice(c_mod_node_hash_rlc, Rotation::cur());
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

            let mut leaf_rlc_prev = meta.query_advice(acc_s, Rotation::prev());
            let mut leaf_mult_prev = meta.query_advice(acc_mult_s, Rotation::prev());
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
            let acc_c = meta.query_advice(acc_c, Rotation::cur());

            constraints.push(("Leaf RLC", q_enable.clone() * (acc_s - leaf_rlc)));
            constraints.push((
                "Leaf value RLC",
                q_enable.clone() * (acc_c - leaf_value_rlc),
            ));

            let s_advices0_prev = meta.query_advice(s_advices[0], Rotation::prev());
            let short_check =
                s_rlp1_prev - c192 - s_rlp2_prev.clone() + c128.clone() - one.clone() - one.clone();
            let long_check1 = s_rlp2_prev - s_advices0_prev + c128.clone()
                - one.clone()
                - (s_rlp2_cur.clone() - c128.clone() + one.clone() + one.clone());
            let long_check2 = s_rlp1_cur - c128.clone() - s_rlp2_cur + c128 - one.clone();

            // RLP constraints:
            constraints.push(("RLP short", q_enable.clone() * short_check * is_short));
            constraints.push((
                "RLP long 1",
                q_enable.clone() * long_check1 * is_long.clone(),
            ));
            constraints.push(("RLP long 2", q_enable.clone() * long_check2 * is_long));

            constraints
        });

        meta.lookup_any("leaf hash in parent", |meta| {
            let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
            let not_first_level = meta.query_advice(not_first_level, Rotation::cur());
            let mut is_leaf = meta.query_advice(is_leaf_value, Rotation::cur());
            let q_enable = q_not_first * not_first_level * is_leaf;

            let rlc = meta.query_advice(acc_s, Rotation::cur());

            let sel = meta.query_advice(sel, Rotation(rot));

            let is_branch_placeholder =
                meta.query_advice(is_branch_placeholder, Rotation(rot_into_init));

            // For leaf without branch, the constraints are in storage_root_in_account_leaf.
            let is_leaf_without_branch = meta.query_advice(
                is_account_leaf_storage_codehash_c,
                Rotation(rot_into_account),
            );

            // If sel = 1, there is no leaf at this position (value is being added or
            // deleted) and we don't check the hash of it.
            let mut constraints = vec![];
            constraints.push((
                q_enable.clone()
                    * rlc
                    * (one.clone() - sel.clone())
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
                    * (one.clone() - sel.clone())
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
            let mut is_leaf = meta.query_advice(is_leaf_value, Rotation::cur());
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

            let sel = meta.query_advice(sel, Rotation(rot));

            let is_branch_placeholder =
                meta.query_advice(is_branch_placeholder, Rotation(rot_into_init));

            // For leaf without branch, the constraints are in storage_root_in_account_leaf.
            let is_leaf_without_branch_after_placeholder = meta.query_advice(
                is_account_leaf_storage_codehash_c,
                Rotation(rot_into_account - 19),
            );
            let is_leaf_without_branch = meta.query_advice(
                is_account_leaf_storage_codehash_c,
                Rotation(rot_into_account),
            );

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

        // Check hash of a storage leaf to be state root when leaf without branch -
        // this can happen only if the circuit is used without account proof.
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
            let mut is_leaf = meta.query_advice(is_leaf_value, Rotation::cur());
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
