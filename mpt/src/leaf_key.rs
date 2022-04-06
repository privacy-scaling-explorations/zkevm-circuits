use halo2_proofs::{
    circuit::Chip,
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, VirtualCells},
    poly::Rotation,
};
use pairing::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::{
    helpers::{compute_rlc, get_bool_constraint, key_len_lookup, mult_diff_lookup, range_lookups},
    mpt::FixedTableTag,
    param::{HASH_WIDTH, IS_BRANCH_C16_POS, IS_BRANCH_C1_POS, LAYOUT_OFFSET, R_TABLE_LEN},
};

#[derive(Clone, Debug)]
pub(crate) struct LeafKeyConfig {}

// Verifies the RLC of leaf RLP: RLP meta data & key (value and then hash of
// the whole RLC are checked in leaf_value).
// Verifies RLC of a leaf key - used for a check from outside the circuit to
// verify that the proper key is used.
pub(crate) struct LeafKeyChip<F> {
    config: LeafKeyConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> LeafKeyChip<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: impl Fn(&mut VirtualCells<'_, F>) -> Expression<F> + Copy,
        s_rlp1: Column<Advice>,
        s_rlp2: Column<Advice>,
        c_rlp1: Column<Advice>,
        c_rlp2: Column<Advice>,
        s_advices: [Column<Advice>; HASH_WIDTH],
        s_mod_node_hash_rlc: Column<Advice>,
        c_mod_node_hash_rlc: Column<Advice>,
        acc: Column<Advice>,
        acc_mult: Column<Advice>,
        key_rlc: Column<Advice>,
        key_rlc_mult: Column<Advice>,
        key_rlc_prev: Column<Advice>,
        key_rlc_mult_prev: Column<Advice>,
        is_branch_placeholder: Column<Advice>,
        modified_node: Column<Advice>,
        is_account_leaf_storage_codehash_c: Column<Advice>,
        r_table: Vec<Expression<F>>,
        fixed_table: [Column<Fixed>; 3],
        is_s: bool,
    ) -> LeafKeyConfig {
        let config = LeafKeyConfig {};
        let one = Expression::Constant(F::one());

        let mut rot_into_init = -19;
        let mut rot_into_account = -1;
        if !is_s {
            rot_into_init = -21;
            rot_into_account = -3;
        }

        // TODO: if key is of length 1, then there is one less byte in RLP meta data
        // (this is easier seen in extension nodes, it will probably be difficult
        // to generate such test for normal ShortNode)

        // Checking leaf RLC is ok - this value is then taken in the next row, where
        // leaf value is added to RLC, finally lookup is used to check the hash that
        // corresponds to this RLC is in the parent branch.
        meta.create_gate("Storage leaf RLC", |meta| {
            let q_enable = q_enable(meta);
            let mut constraints = vec![];

            let c248 = Expression::Constant(F::from(248));
            let s_rlp1 = meta.query_advice(s_rlp1, Rotation::cur());
            let is_long = meta.query_advice(s_mod_node_hash_rlc, Rotation::cur());
            let is_short = meta.query_advice(c_mod_node_hash_rlc, Rotation::cur());
            constraints.push((
                "is_long",
                q_enable.clone() * is_long.clone() * (s_rlp1.clone() - c248),
            ));
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

            let mut rlc = s_rlp1;
            let s_rlp2 = meta.query_advice(s_rlp2, Rotation::cur());
            rlc = rlc + s_rlp2 * r_table[0].clone();

            rlc = rlc + compute_rlc(meta, s_advices.to_vec(), 1, one.clone(), 0, r_table.clone());

            let c_rlp1 = meta.query_advice(c_rlp1, Rotation::cur());
            // c_rlp2 can appear if long and if no branch above leaf
            let c_rlp2 = meta.query_advice(c_rlp2, Rotation::cur());
            rlc = rlc + c_rlp1 * r_table[R_TABLE_LEN - 1].clone() * r_table[1].clone();
            rlc = rlc + c_rlp2 * r_table[R_TABLE_LEN - 1].clone() * r_table[2].clone();

            let acc = meta.query_advice(acc, Rotation::cur());
            constraints.push(("Leaf key acc", q_enable * (rlc - acc)));

            constraints
        });

        let sel_short = |meta: &mut VirtualCells<F>| {
            let q_enable = q_enable(meta);
            let is_short = meta.query_advice(c_mod_node_hash_rlc, Rotation::cur());

            q_enable * is_short
        };
        let sel_long = |meta: &mut VirtualCells<F>| {
            let q_enable = q_enable(meta);
            let is_long = meta.query_advice(s_mod_node_hash_rlc, Rotation::cur());

            q_enable * is_long
        };

        /*
        // There are 0s after key length.
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
        key_len_lookup(meta, sel_short, 32, s_advices[0], c_rlp1, fixed_table);

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
        key_len_lookup(meta, sel_long, 33, s_advices[0], c_rlp2, fixed_table);
        */

        // acc_mult corresponds to key length (short):
        mult_diff_lookup(meta, sel_short, 2, s_rlp2, acc_mult, fixed_table);
        // acc_mult corresponds to key length (long):
        mult_diff_lookup(meta, sel_long, 3, s_advices[0], acc_mult, fixed_table);

        // Checking the key - accumulated RLC is taken (computed using the path through
        // branches) and key bytes are added to the RLC. The external circuit
        // can check the key (where value in trie is being set at key) RLC is
        // the same as in key_rlc column.
        meta.create_gate("Storage leaf key RLC", |meta| {
            let q_enable = q_enable(meta);
            let mut constraints = vec![];

            let is_long = meta.query_advice(s_mod_node_hash_rlc, Rotation::cur());
            let is_short = meta.query_advice(c_mod_node_hash_rlc, Rotation::cur());

            let is_leaf_without_branch = meta.query_advice(
                is_account_leaf_storage_codehash_c,
                Rotation(rot_into_account),
            );

            // key rlc is in the first branch node (not branch init)
            let mut rot = -18;
            if !is_s {
                rot = -20;
            }

            let key_rlc_acc_start = meta.query_advice(key_rlc, Rotation(rot));
            let key_mult_start = meta.query_advice(key_rlc_mult, Rotation(rot));

            // sel1 and sel2 are in init branch
            let sel1 = meta.query_advice(
                s_advices[IS_BRANCH_C16_POS - LAYOUT_OFFSET],
                Rotation(rot - 1),
            );
            let sel2 = meta.query_advice(
                s_advices[IS_BRANCH_C1_POS - LAYOUT_OFFSET],
                Rotation(rot - 1),
            );

            let c32 = Expression::Constant(F::from(32));
            let c48 = Expression::Constant(F::from(48));

            let is_branch_placeholder = meta.query_advice(is_branch_placeholder, Rotation(rot - 1));

            // If the last branch is placeholder (the placeholder branch is the same as its
            // parallel counterpart), there is a branch modified_index nibble already
            // incorporated in key_rlc. That means we need to ignore the first nibble here
            // (in leaf key).

            // For short RLP (key starts at s_advices[0]):

            // If sel1 = 1, we have one nibble+48 in s_advices[0].
            let s_advice0 = meta.query_advice(s_advices[0], Rotation::cur());
            let mut key_rlc_acc_short = key_rlc_acc_start.clone()
                + (s_advice0.clone() - c48.clone()) * key_mult_start.clone() * sel1.clone();
            let mut key_mult = key_mult_start.clone() * r_table[0].clone() * sel1.clone();
            key_mult = key_mult + key_mult_start.clone() * sel2.clone(); // set to key_mult_start if sel2, stays key_mult if sel1

            // If sel2 = 1 and !is_branch_placeholder, we have 32 in s_advices[0].
            constraints.push((
                "Leaf key acc s_advice0",
                q_enable.clone()
                    * (s_advice0.clone() - c32.clone())
                    * sel2.clone()
                    * (one.clone() - is_branch_placeholder.clone())
                    * (one.clone() - is_leaf_without_branch.clone())
                    * is_short.clone(),
            ));

            let s_advices1 = meta.query_advice(s_advices[1], Rotation::cur());
            key_rlc_acc_short = key_rlc_acc_short + s_advices1.clone() * key_mult.clone();

            for ind in 2..HASH_WIDTH {
                let s = meta.query_advice(s_advices[ind], Rotation::cur());
                key_rlc_acc_short =
                    key_rlc_acc_short + s * key_mult.clone() * r_table[ind - 2].clone();
            }

            // c_rlp1 can appear if no branch above the leaf
            let c_rlp1 = meta.query_advice(c_rlp1, Rotation::cur());
            key_rlc_acc_short =
                key_rlc_acc_short + c_rlp1.clone() * key_mult.clone() * r_table[30].clone();

            let key_rlc = meta.query_advice(key_rlc, Rotation::cur());

            // No need to distinguish between sel1 and sel2 here as it was already
            // when computing key_rlc_acc_short.
            constraints.push((
                "Key RLC short",
                q_enable.clone()
                    * (key_rlc_acc_short - key_rlc.clone())
                    * (one.clone() - is_branch_placeholder.clone())
                    * (one.clone() - is_leaf_without_branch.clone())
                    * is_short.clone(),
            ));

            // For long RLP (key starts at s_advices[1]):

            // If sel1 = 1, we have nibble+48 in s_advices[1].
            let s_advice1 = meta.query_advice(s_advices[1], Rotation::cur());
            let mut key_rlc_acc_long = key_rlc_acc_start.clone()
                + (s_advice1.clone() - c48) * key_mult_start.clone() * sel1.clone();
            let mut key_mult = key_mult_start.clone() * r_table[0].clone() * sel1.clone();
            key_mult = key_mult + key_mult_start.clone() * sel2.clone(); // set to key_mult_start if sel2, stays key_mult if sel1

            // If sel2 = 1 and !is_branch_placeholder, we have 32 in s_advices[1].
            constraints.push((
                "Leaf key acc s_advice1",
                q_enable.clone()
                    * (s_advice1.clone() - c32.clone())
                    * sel2.clone()
                    * (one.clone() - is_branch_placeholder.clone())
                    * (one.clone() - is_leaf_without_branch.clone())
                    * is_long.clone(),
            ));

            let s_advices2 = meta.query_advice(s_advices[2], Rotation::cur());
            key_rlc_acc_long = key_rlc_acc_long + s_advices2 * key_mult.clone();

            for ind in 3..HASH_WIDTH {
                let s = meta.query_advice(s_advices[ind], Rotation::cur());
                key_rlc_acc_long =
                    key_rlc_acc_long + s * key_mult.clone() * r_table[ind - 3].clone();
            }

            key_rlc_acc_long =
                key_rlc_acc_long + c_rlp1.clone() * key_mult.clone() * r_table[29].clone();
            // c_rlp2 can appear if no branch above the leaf
            let c_rlp2 = meta.query_advice(c_rlp2, Rotation::cur());
            key_rlc_acc_long = key_rlc_acc_long + c_rlp2 * key_mult.clone() * r_table[30].clone();

            // No need to distinguish between sel1 and sel2 here as it was already
            // when computing key_rlc_acc_long.
            constraints.push((
                "Key RLC long",
                q_enable.clone()
                    * (key_rlc_acc_long - key_rlc.clone())
                    * (one.clone() - is_branch_placeholder.clone())
                    * (one.clone() - is_leaf_without_branch.clone())
                    * is_long.clone(),
            ));

            constraints
        });

        meta.create_gate("Storage leaf key RLC (without branch)", |meta| {
            let q_enable = q_enable(meta);
            let mut constraints = vec![];

            let is_long = meta.query_advice(s_mod_node_hash_rlc, Rotation::cur());
            let is_short = meta.query_advice(c_mod_node_hash_rlc, Rotation::cur());

            let is_leaf_without_branch = meta.query_advice(
                is_account_leaf_storage_codehash_c,
                Rotation(rot_into_account),
            );

            let key_rlc_acc_start = Expression::Constant(F::zero());
            let key_mult_start = one.clone();

            let c32 = Expression::Constant(F::from(32));
            let c48 = Expression::Constant(F::from(48));

            // This is the case like sel2 = 1 (there 32 in s_rlp2 or s_advices[0] for
            // short and long RLP respectively).

            // For short RLP (key starts at s_advices[0]):

            // If sel1 = 1, we have one nibble+48 in s_advices[0].
            let s_advice0 = meta.query_advice(s_advices[0], Rotation::cur());
            let mut key_rlc_acc_short = key_rlc_acc_start.clone();
            let key_mult = key_mult_start.clone();

            // If sel2 = 1 and !is_branch_placeholder, we have 32 in s_advices[0].
            constraints.push((
                "Leaf key acc s_advice0",
                q_enable.clone()
                    * (s_advice0.clone() - c32.clone())
                    * is_leaf_without_branch.clone()
                    * is_short.clone(),
            ));

            let s_advices1 = meta.query_advice(s_advices[1], Rotation::cur());
            key_rlc_acc_short = key_rlc_acc_short + s_advices1.clone() * key_mult.clone();

            for ind in 2..HASH_WIDTH {
                let s = meta.query_advice(s_advices[ind], Rotation::cur());
                key_rlc_acc_short =
                    key_rlc_acc_short + s * key_mult.clone() * r_table[ind - 2].clone();
            }

            // c_rlp1 can appear if no branch above the leaf
            let c_rlp1 = meta.query_advice(c_rlp1, Rotation::cur());
            key_rlc_acc_short =
                key_rlc_acc_short + c_rlp1.clone() * key_mult.clone() * r_table[30].clone();

            let key_rlc = meta.query_advice(key_rlc, Rotation::cur());

            // No need to distinguish between sel1 and sel2 here as it was already
            // when computing key_rlc_acc_short.
            constraints.push((
                "Key RLC short",
                q_enable.clone()
                    * (key_rlc_acc_short - key_rlc.clone())
                    * is_leaf_without_branch.clone()
                    * is_short.clone(),
            ));

            // For long RLP (key starts at s_advices[1]):

            // If sel1 = 1, we have nibble+48 in s_advices[1].
            let s_advice1 = meta.query_advice(s_advices[1], Rotation::cur());
            let mut key_rlc_acc_long = key_rlc_acc_start.clone();

            // If sel2 = 1 and !is_branch_placeholder, we have 32 in s_advices[1].
            constraints.push((
                "Leaf key acc s_advice1",
                q_enable.clone()
                    * (s_advice1.clone() - c32.clone())
                    * is_leaf_without_branch.clone()
                    * is_long.clone(),
            ));

            let s_advices2 = meta.query_advice(s_advices[2], Rotation::cur());
            key_rlc_acc_long = key_rlc_acc_long + s_advices2 * key_mult.clone();

            for ind in 3..HASH_WIDTH {
                let s = meta.query_advice(s_advices[ind], Rotation::cur());
                key_rlc_acc_long =
                    key_rlc_acc_long + s * key_mult.clone() * r_table[ind - 3].clone();
            }

            key_rlc_acc_long =
                key_rlc_acc_long + c_rlp1.clone() * key_mult.clone() * r_table[29].clone();
            // c_rlp2 can appear if no branch above the leaf
            let c_rlp2 = meta.query_advice(c_rlp2, Rotation::cur());
            key_rlc_acc_long = key_rlc_acc_long + c_rlp2 * key_mult.clone() * r_table[30].clone();

            // No need to distinguish between sel1 and sel2 here as it was already
            // when computing key_rlc_acc_long.
            constraints.push((
                "Key RLC long",
                q_enable.clone()
                    * (key_rlc_acc_long - key_rlc.clone())
                    * is_leaf_without_branch.clone()
                    * is_long.clone(),
            ));

            constraints
        });

        // For leaf under placeholder branch we wouldn't need to check key RLC -
        // this leaf is something we didn't ask for. For example, when setting a leaf L
        // causes that leaf L1 (this is the leaf under branch placeholder)
        // is replaced by branch, then we get placeholder branch at S positions
        // and leaf L1 under it. However, key RLC needs to be compared for leaf L,
        // because this is where the key was changed (but it causes to change also L1).
        // In delete, the situation is just turned around.
        // However, we check key RLC for this leaf too because this simplifies
        // the constraints for checking that leaf L1 is the same as the leaf that
        // is in the branch parallel to the placeholder branch -
        // same with the exception of extension node key. This can be checked by
        // comparing key RLC of the leaf before being replaced by branch and key RLC
        // of this same leaf after it drifted into a branch.
        // Constraints for this are in leaf_key_in_added_branch.

        // Note that hash of leaf L1 needs to be checked to be in the branch
        // above the placeholder branch - this is checked in leaf_value (where RLC
        // from the first gate above is used).

        meta.create_gate("Previous level RLC", |meta| {
            let q_enable = q_enable(meta);
            let mut constraints = vec![];

            let is_first_storage_level = meta.query_advice(
                is_account_leaf_storage_codehash_c,
                Rotation(rot_into_init - 1),
            );

            let is_leaf_without_branch = meta.query_advice(
                is_account_leaf_storage_codehash_c,
                Rotation(rot_into_account),
            );

            // Could be used any rotation into previous branch, because key RLC is the same
            // in all branch children:
            let rot_into_prev_branch = rot_into_init - 5;
            // TODO: check why a different rotation causes (for example rot_into_init - 3)
            // causes ConstraintPoisened

            // key_rlc_mult_prev_level = 1 if is_first_storage_level
            let key_rlc_mult_prev_level = (one.clone() - is_first_storage_level.clone())
                * meta.query_advice(key_rlc_mult, Rotation(rot_into_prev_branch))
                + is_first_storage_level.clone();
            // key_rlc_prev_level = 0 if is_first_storage_level
            let key_rlc_prev_level = (one.clone() - is_first_storage_level)
                * meta.query_advice(key_rlc, Rotation(rot_into_prev_branch));

            let rlc_prev = meta.query_advice(key_rlc_prev, Rotation::cur());
            let mult_prev = meta.query_advice(key_rlc_mult_prev, Rotation::cur());

            constraints.push((
                "Previous key RLC",
                q_enable.clone()
                    * (rlc_prev - key_rlc_prev_level)
                    * (one.clone() - is_leaf_without_branch.clone()),
            ));
            constraints.push((
                "Previous key RLC mult",
                q_enable
                    * (mult_prev - key_rlc_mult_prev_level)
                    * (one.clone() - is_leaf_without_branch.clone()),
            ));

            constraints
        });

        // For a leaf after placeholder, we need to use key_rlc from previous level
        // (the branch above placeholder).
        meta.create_gate("Storage leaf after placeholder key RLC", |meta| {
            let q_enable = q_enable(meta);
            let mut constraints = vec![];

            let is_long = meta.query_advice(s_mod_node_hash_rlc, Rotation::cur());
            let is_short = meta.query_advice(c_mod_node_hash_rlc, Rotation::cur());

            // Note: key rlc is in the first branch node (not branch init).
            let rot_level_above = rot_into_init + 1 - 19;

            let is_first_storage_level = meta.query_advice(
                is_account_leaf_storage_codehash_c,
                Rotation(rot_into_init - 1),
            );

            let is_leaf_without_branch = meta.query_advice(
                is_account_leaf_storage_codehash_c,
                Rotation(rot_into_account),
            );

            let c32 = Expression::Constant(F::from(32));
            let c48 = Expression::Constant(F::from(48));

            let is_branch_placeholder =
                meta.query_advice(is_branch_placeholder, Rotation(rot_into_init));

            // previous key RLC:
            let key_rlc_acc_start = meta.query_advice(key_rlc_prev, Rotation::cur())
                * (one.clone() - is_first_storage_level.clone());
            let key_mult_start = meta.query_advice(key_rlc_mult_prev, Rotation::cur())
                * (one.clone() - is_first_storage_level.clone())
                + is_first_storage_level.clone();

            // Note: the approach (like for sel1 and sel2) with retrieving
            // key RLC and key RLC mult from the level above placeholder fails
            // due to ConstraintPoisened error.
            // sel1 and sel2 are in init branch
            // Note that when is_first_storage_level, it is always sel2 = 1 because
            // there are all 32 bytes in a key.
            let sel1 = (one.clone() - is_first_storage_level.clone())
                * meta.query_advice(
                    s_advices[IS_BRANCH_C16_POS - LAYOUT_OFFSET],
                    Rotation(rot_level_above - 1),
                );
            let sel2 = (one.clone() - is_first_storage_level.clone())
                * meta.query_advice(
                    s_advices[IS_BRANCH_C1_POS - LAYOUT_OFFSET],
                    Rotation(rot_level_above - 1),
                )
                + is_first_storage_level.clone();

            // For short RLP (key starts at s_advices[0]):

            // If sel1 = 1, we have one nibble+48 in s_advices[0].
            let s_advice0 = meta.query_advice(s_advices[0], Rotation::cur());
            let mut key_rlc_acc_short = key_rlc_acc_start.clone()
                + (s_advice0.clone() - c48.clone()) * key_mult_start.clone() * sel1.clone();
            let key_mult = key_mult_start.clone() * r_table[0].clone() * sel1.clone()
                + key_mult_start.clone() * sel2.clone(); // set to key_mult_start if sel2, stays key_mult if sel1

            // If sel2 = 1, we have 32 in s_advices[0].
            constraints.push((
                "Leaf key acc s_advice0",
                q_enable.clone()
                    * (s_advice0.clone() - c32.clone())
                    * sel2.clone()
                    * is_branch_placeholder.clone()
                    * (one.clone() - is_leaf_without_branch.clone())
                    * is_short.clone(),
            ));

            let s_advices1 = meta.query_advice(s_advices[1], Rotation::cur());
            key_rlc_acc_short = key_rlc_acc_short + s_advices1.clone() * key_mult.clone();

            for ind in 2..HASH_WIDTH {
                let s = meta.query_advice(s_advices[ind], Rotation::cur());
                key_rlc_acc_short =
                    key_rlc_acc_short + s * key_mult.clone() * r_table[ind - 2].clone();
            }

            let c_rlp1 = meta.query_advice(c_rlp1, Rotation::cur());
            key_rlc_acc_short =
                key_rlc_acc_short + c_rlp1.clone() * key_mult.clone() * r_table[30].clone();

            let key_rlc = meta.query_advice(key_rlc, Rotation::cur());

            // No need to distinguish between sel1 and sel2 here as it was already
            // when computing key_rlc_acc_short.
            constraints.push((
                "Key RLC short",
                q_enable.clone()
                    * (key_rlc_acc_short - key_rlc.clone())
                    * is_branch_placeholder.clone()
                    * (one.clone() - is_leaf_without_branch.clone())
                    * is_short.clone(),
            ));

            // For long RLP (key starts at s_advices[1]):

            // If sel1 = 1, we have nibble+48 in s_advices[1].
            let s_advice1 = meta.query_advice(s_advices[1], Rotation::cur());
            let mut key_rlc_acc_long = key_rlc_acc_start.clone()
                + (s_advice1.clone() - c48) * key_mult_start.clone() * sel1.clone();

            // If sel2 = 1, we have 32 in s_advices[1].
            constraints.push((
                "Leaf key acc s_advice1",
                q_enable.clone()
                    * (s_advice1.clone() - c32.clone())
                    * sel2.clone()
                    * is_branch_placeholder.clone()
                    * (one.clone() - is_leaf_without_branch.clone())
                    * is_long.clone(),
            ));

            let s_advices2 = meta.query_advice(s_advices[2], Rotation::cur());
            key_rlc_acc_long = key_rlc_acc_long + s_advices2 * key_mult.clone();

            for ind in 3..HASH_WIDTH {
                let s = meta.query_advice(s_advices[ind], Rotation::cur());
                key_rlc_acc_long =
                    key_rlc_acc_long + s * key_mult.clone() * r_table[ind - 3].clone();
            }

            key_rlc_acc_long =
                key_rlc_acc_long + c_rlp1.clone() * key_mult.clone() * r_table[29].clone();

            let c_rlp2 = meta.query_advice(c_rlp2, Rotation::cur());
            key_rlc_acc_long = key_rlc_acc_long + c_rlp2.clone() * key_mult * r_table[30].clone();

            // No need to distinguish between sel1 and sel2 here as it was already
            // when computing key_rlc_acc_long.
            constraints.push((
                "Key RLC long",
                q_enable.clone()
                    * (key_rlc_acc_long - key_rlc.clone())
                    * is_branch_placeholder.clone()
                    * (one.clone() - is_leaf_without_branch.clone())
                    * is_long.clone(),
            ));

            constraints
        });

        range_lookups(
            meta,
            q_enable,
            s_advices.to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );
        range_lookups(
            meta,
            q_enable,
            [s_rlp1, s_rlp2, c_rlp1, c_rlp2].to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );

        config
    }

    pub fn construct(config: LeafKeyConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }
}

impl<F: FieldExt> Chip<F> for LeafKeyChip<F> {
    type Config = LeafKeyConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}
