use halo2_proofs::{
    circuit::{Layouter, Region},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed, Selector},
    poly::Rotation,
};
use keccak256::plain::Keccak;
use pairing::arithmetic::FieldExt;
use std::{convert::TryInto, marker::PhantomData};

use crate::{
    account_leaf_key::AccountLeafKeyChip,
    account_leaf_nonce_balance::AccountLeafNonceBalanceChip,
    account_leaf_storage_codehash::AccountLeafStorageCodehashChip,
    branch::BranchChip,
    branch_acc::BranchAccChip,
    branch_acc_init::BranchAccInitChip,
    branch_hash_in_parent::BranchHashInParentChip,
    branch_rows::BranchRowsChip,
    extension_node::ExtensionNodeChip,
    extension_node_key::ExtensionNodeKeyChip,
    helpers::{get_is_extension_node, hash_into_rlc},
    leaf_key::LeafKeyChip,
    leaf_key_in_added_branch::LeafKeyInAddedBranchChip,
    leaf_value::LeafValueChip,
    param::{
        IS_BRANCH_C16_POS, IS_BRANCH_C1_POS, IS_EXT_LONG_EVEN_C16_POS, IS_EXT_LONG_EVEN_C1_POS,
        IS_EXT_LONG_ODD_C16_POS, IS_EXT_LONG_ODD_C1_POS, IS_EXT_SHORT_C16_POS, IS_EXT_SHORT_C1_POS,
        LAYOUT_OFFSET,
    },
    storage_root_in_account_leaf::StorageRootChip,
};
use crate::{branch_key::BranchKeyChip, param::WITNESS_ROW_WIDTH};
use crate::{
    param::{
        BRANCH_0_C_START, BRANCH_0_KEY_POS, BRANCH_0_S_START, C_RLP_START, C_START, DRIFTED_POS,
        HASH_WIDTH, IS_BRANCH_C_PLACEHOLDER_POS, IS_BRANCH_S_PLACEHOLDER_POS, KECCAK_INPUT_WIDTH,
        KECCAK_OUTPUT_WIDTH, S_RLP_START, S_START,
    },
    selectors::SelectorsChip,
};

/*
    MPT circuit contains S and C columns (other columns are mostly selectors).

    With S columns the prover proves the knowledge of key1/val1 that is in the
    trie with rootS.

    With C columns the prover proves the knowledge of key1/val2 that is in the
    trie with rootC. Note that key is the same for both S and C, whereas value
    is different. The prover thus proves the knowledge how to change value at key
    key1 from val1 to val2 that results the root being changed from rootS to rootC.

    The branch contains 16 nodes which are stored in 16 rows.
    A row looks like:
    [0,        160,      123,    ...,  148,     0,        160,    232,    ..., 92     ]
    [rlp1 (S), rlp2 (S), b0 (S), ...,  b31 (S), rlp1 (C), rlp2 C, b0 (C), ..., b31 (C)]

    Values bi (S) and bi(C) present hash of a node. Thus, the first half of a row
    is a S node:
    [rlp1, rlp2, b0, ..., b31]

    The second half of the row is a C node (same structure):
    [rlp1, rlp2, b0, ..., b31]

    We start with top level branch and then we follow branches (could be also extension
    nodes) down to the leaf.
*/

#[derive(Clone, Debug)]
pub struct MPTConfig<F> {
    q_enable: Selector,
    q_not_first: Column<Fixed>, // not first row
    not_first_level: Column<Fixed>, /* to avoid rotating back when in the first branch (for key
                                 * rlc) */
    is_branch_init: Column<Advice>,
    is_branch_child: Column<Advice>,
    is_last_branch_child: Column<Advice>,
    is_leaf_s: Column<Advice>,
    is_leaf_s_value: Column<Advice>,
    is_leaf_c: Column<Advice>,
    is_leaf_c_value: Column<Advice>,
    is_account_leaf_key_s: Column<Advice>,
    is_account_leaf_nonce_balance_s: Column<Advice>,
    is_account_leaf_nonce_balance_c: Column<Advice>,
    is_account_leaf_storage_codehash_s: Column<Advice>,
    is_account_leaf_storage_codehash_c: Column<Advice>,
    node_index: Column<Advice>,
    is_modified: Column<Advice>,   // whether this branch node is modified
    modified_node: Column<Advice>, // index of the modified node
    is_at_drifted_pos: Column<Advice>, // needed when leaf is turned into branch
    drifted_pos: Column<Advice>,   /* needed when leaf is turned into branch - first nibble of
                                    * the key stored in a leaf (because the existing leaf will
                                    * jump to this position in added branch) */
    is_leaf_in_added_branch: Column<Advice>, /* it is at drifted_pos position in added branch,
                                              * note that this row could be omitted when there
                                              * is no added branch but then it would open a
                                              * vulnerability because the attacker could omit
                                              * these row in cases when it's needed too (and
                                              * constraints happen in this row) */
    is_extension_node_s: Column<Advice>, /* contains extension node key (s_advices) and hash of
                                          * the branch (c_advices) */
    is_extension_node_c: Column<Advice>,
    s_rlp1: Column<Advice>,
    s_rlp2: Column<Advice>,
    c_rlp1: Column<Advice>,
    c_rlp2: Column<Advice>,
    s_advices: [Column<Advice>; HASH_WIDTH],
    c_advices: [Column<Advice>; HASH_WIDTH],
    s_mod_node_hash_rlc: Column<Advice>, /* modified node s_advices RLC when s_advices present
                                          * hash (used also for leaf long/short) */
    c_mod_node_hash_rlc: Column<Advice>, /* modified node c_advices RLC when c_advices present
                                          * hash (used also for leaf long/short) */
    s_root: Column<Advice>,
    c_root: Column<Advice>,
    acc_s: Column<Advice>,      // for branch s and account leaf
    acc_mult_s: Column<Advice>, // for branch s and account leaf
    acc_c: Column<Advice>,      // for branch c
    acc_mult_c: Column<Advice>, // for branch c
    acc_r: F,
    // sel1 and sel2 in branch children: denote whether there is no leaf at is_modified (when value
    // is added or deleted from trie - but no branch is added or turned into leaf)
    // sel1 and sel2 in storage leaf key: key_rlc_prev and key_rlc_mult_prev
    sel1: Column<Advice>,
    sel2: Column<Advice>,
    r_table: Vec<Expression<F>>,
    // key_rlc & key_rlc_mult used for account address, for storage key,
    // and for mult_diff_nonce/mult_diff_balance in account_leaf_nonce_balance
    key_rlc: Column<Advice>,
    key_rlc_mult: Column<Advice>,
    mult_diff: Column<Advice>,
    keccak_table: [Column<Fixed>; KECCAK_INPUT_WIDTH + KECCAK_OUTPUT_WIDTH],
    fixed_table: [Column<Fixed>; 3],
    _marker: PhantomData<F>,
}

#[derive(Clone, Copy, Debug)]
pub enum FixedTableTag {
    RMult,
    Range16,
    Range256,
    RangeKeyLen256,
}

impl<F: FieldExt> MPTConfig<F> {
    pub(crate) fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let q_enable = meta.selector();
        let q_not_first = meta.fixed_column();
        let not_first_level = meta.fixed_column();

        // having 2 to enable key RLC check (not using 1 to enable proper checks of mult
        // too) TODO: generate from commitments
        let acc_r = F::one() + F::one();

        let one = Expression::Constant(F::one());
        let mut r_table = vec![];
        let mut r = one.clone();
        for _ in 0..HASH_WIDTH {
            r = r * acc_r;
            r_table.push(r.clone());
        }

        // TODO: r_table constraints

        // TODO: in many cases different rotations can be used - for example, when
        // getting back into s_mod_node_hash_rlc or c_mod_node_hash_rlc to get
        // the hash (all 16 branch children contain the same hash in
        // s_mod_node_hash_rlc and c_mod_node_hash_rlc), so we can choose the
        // rotations smartly to have at least as possible of them

        let is_branch_init = meta.advice_column();
        let is_branch_child = meta.advice_column();
        let is_last_branch_child = meta.advice_column();
        let is_leaf_s = meta.advice_column();
        let is_leaf_s_value = meta.advice_column();
        let is_leaf_c = meta.advice_column();
        let is_leaf_c_value = meta.advice_column();

        let is_account_leaf_key_s = meta.advice_column();
        let is_account_leaf_nonce_balance_s = meta.advice_column();
        let is_account_leaf_nonce_balance_c = meta.advice_column();
        let is_account_leaf_storage_codehash_s = meta.advice_column();
        let is_account_leaf_storage_codehash_c = meta.advice_column();

        let node_index = meta.advice_column();
        let is_modified = meta.advice_column();
        let modified_node = meta.advice_column();

        let is_at_drifted_pos = meta.advice_column();
        let drifted_pos = meta.advice_column();
        let is_leaf_in_added_branch = meta.advice_column();
        let is_extension_node_s = meta.advice_column();
        let is_extension_node_c = meta.advice_column();

        let s_rlp1 = meta.advice_column();
        let s_rlp2 = meta.advice_column();
        let s_advices: [Column<Advice>; HASH_WIDTH] = (0..HASH_WIDTH)
            .map(|_| meta.advice_column())
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let c_rlp1 = meta.advice_column();
        let c_rlp2 = meta.advice_column();
        let c_advices: [Column<Advice>; HASH_WIDTH] = (0..HASH_WIDTH)
            .map(|_| meta.advice_column())
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let keccak_table: [Column<Fixed>; KECCAK_INPUT_WIDTH + KECCAK_OUTPUT_WIDTH] = (0
            ..KECCAK_INPUT_WIDTH + KECCAK_OUTPUT_WIDTH)
            .map(|_| meta.fixed_column())
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let fixed_table: [Column<Fixed>; 3] = (0..3)
            .map(|_| meta.fixed_column())
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let s_mod_node_hash_rlc = meta.advice_column();
        let c_mod_node_hash_rlc = meta.advice_column();

        let s_root = meta.advice_column();
        let c_root = meta.advice_column();

        let acc_s = meta.advice_column();
        let acc_mult_s = meta.advice_column();
        let acc_c = meta.advice_column();
        let acc_mult_c = meta.advice_column();

        let sel1 = meta.advice_column();
        let sel2 = meta.advice_column();

        // NOTE: acc_mult_s and acc_mult_c wouldn't be needed if we would have
        // big endian instead of little endian. However, then it would be much more
        // difficult to handle the accumulator when we iterate over the row.
        // For example, big endian would mean to compute acc = acc * mult_r + row[i],
        // but we don't want acc to be multiplied by mult_r when row[i] = 0 where
        // the stream already ended and 0s are only to fulfill the row.

        let key_rlc = meta.advice_column();
        let key_rlc_mult = meta.advice_column();
        let mult_diff = meta.advice_column();

        // NOTE: key_rlc_mult wouldn't be needed if we would have
        // big endian instead of little endian. However, then it would be much more
        // difficult to handle the accumulator when we iterate over the key.
        // At some point (but we don't know this point at compile time), key ends
        // and from there on the values in the row need to be 0s.
        // However, if we are computing rlc using little endian:
        // rlc = rlc + row[i] * acc_r,
        // rlc will stay the same once r[i] = 0.
        // If big endian would be used:
        // rlc = rlc * acc_r + row[i],
        // the rlc would be multiplied by acc_r when row[i] = 0.

        SelectorsChip::<F>::configure(
            meta,
            q_enable,
            q_not_first,
            is_branch_init,
            is_branch_child,
            is_last_branch_child,
            is_leaf_s,
            is_leaf_s_value,
            is_leaf_c,
            is_leaf_c_value,
            is_account_leaf_key_s,
            is_account_leaf_nonce_balance_s,
            is_account_leaf_nonce_balance_c,
            is_account_leaf_storage_codehash_s,
            is_account_leaf_storage_codehash_c,
            is_leaf_in_added_branch,
            is_extension_node_s,
            is_extension_node_c,
            sel1,
            sel2,
            is_modified,
            is_at_drifted_pos,
        );

        BranchChip::<F>::configure(
            meta,
            q_enable,
            q_not_first,
            s_rlp1,
            s_rlp2,
            c_rlp1,
            c_rlp2,
            s_advices,
            c_advices,
            is_branch_init,
            is_branch_child,
            is_last_branch_child,
            node_index,
            is_modified,
            modified_node,
            is_at_drifted_pos,
            drifted_pos,
            fixed_table.clone(),
        );

        BranchKeyChip::<F>::configure(
            meta,
            q_not_first,
            not_first_level,
            is_branch_init,
            is_account_leaf_storage_codehash_c,
            s_advices,
            modified_node,
            s_advices[IS_BRANCH_C16_POS - LAYOUT_OFFSET],
            s_advices[IS_BRANCH_C1_POS - LAYOUT_OFFSET],
            key_rlc,
            key_rlc_mult,
            acc_r,
        );

        BranchRowsChip::<F>::configure(
            meta,
            q_not_first,
            is_branch_child,
            s_mod_node_hash_rlc,
            s_advices,
            node_index,
            is_modified,
            is_at_drifted_pos,
            sel1,
            acc_r,
        );

        BranchRowsChip::<F>::configure(
            meta,
            q_not_first,
            is_branch_child,
            c_mod_node_hash_rlc,
            c_advices,
            node_index,
            is_modified,
            is_at_drifted_pos,
            sel2,
            acc_r,
        );

        BranchHashInParentChip::<F>::configure(
            meta,
            not_first_level,
            is_account_leaf_storage_codehash_c,
            is_last_branch_child,
            s_advices[IS_BRANCH_S_PLACEHOLDER_POS - LAYOUT_OFFSET],
            s_advices,
            s_mod_node_hash_rlc,
            acc_s,
            acc_mult_s,
            keccak_table,
        );

        BranchHashInParentChip::<F>::configure(
            meta,
            not_first_level,
            is_account_leaf_storage_codehash_c,
            is_last_branch_child,
            s_advices[IS_BRANCH_C_PLACEHOLDER_POS - LAYOUT_OFFSET],
            s_advices,
            c_mod_node_hash_rlc,
            acc_c,
            acc_mult_c,
            keccak_table,
        );

        ExtensionNodeChip::<F>::configure(
            meta,
            |meta| {
                // We need to do the lookup only if we are one after last branch child.
                let is_after_last_branch_child =
                    meta.query_advice(is_last_branch_child, Rotation(-1));
                // is_extension_node is in branch init row
                let is_extension_node = get_is_extension_node(meta, s_advices, -17);

                is_after_last_branch_child * is_extension_node
            },
            not_first_level,
            q_not_first,
            is_account_leaf_storage_codehash_c,
            is_branch_init,
            s_rlp1,
            s_rlp2,
            c_rlp2,
            s_advices,
            c_advices,
            acc_s,
            acc_mult_s,
            acc_c,
            acc_mult_c,
            keccak_table,
            s_mod_node_hash_rlc,
            r_table.clone(),
            true,
            acc_r,
        );

        ExtensionNodeChip::<F>::configure(
            meta,
            |meta| {
                // We need to do the lookup only if we are two after last branch child.
                let is_after_last_branch_child =
                    meta.query_advice(is_last_branch_child, Rotation(-2));
                // is_extension_node is in branch init row
                let is_extension_node = get_is_extension_node(meta, s_advices, -18);

                is_after_last_branch_child * is_extension_node
            },
            not_first_level,
            q_not_first,
            is_account_leaf_storage_codehash_c,
            is_branch_init,
            s_rlp1,
            s_rlp2,
            c_rlp2,
            s_advices,
            c_advices,
            acc_s,
            acc_mult_s,
            acc_c,
            acc_mult_c,
            keccak_table,
            c_mod_node_hash_rlc,
            r_table.clone(),
            false,
            acc_r,
        );

        ExtensionNodeKeyChip::<F>::configure(
            meta,
            q_not_first,
            not_first_level,
            is_branch_init,
            is_branch_child,
            is_last_branch_child,
            is_account_leaf_storage_codehash_c,
            s_rlp1,
            s_rlp2,
            c_rlp1,
            s_advices,
            c_advices,
            modified_node,
            key_rlc,
            key_rlc_mult,
            mult_diff,
            fixed_table.clone(),
            r_table.clone(),
        );

        StorageRootChip::<F>::configure(
            meta,
            not_first_level,
            is_leaf_s,
            is_leaf_c,
            is_account_leaf_storage_codehash_c,
            is_last_branch_child,
            s_advices,
            acc_s,
            acc_mult_s,
            acc_c,
            acc_mult_c,
            keccak_table,
            acc_r,
            true,
        );

        StorageRootChip::<F>::configure(
            meta,
            not_first_level,
            is_leaf_s,
            is_leaf_c,
            is_account_leaf_storage_codehash_c,
            is_last_branch_child,
            s_advices, // s_advices (and not c_advices) is correct
            acc_s,
            acc_mult_s,
            acc_c,
            acc_mult_c,
            keccak_table,
            acc_r,
            false,
        );

        BranchAccInitChip::<F>::configure(
            meta,
            |meta| {
                meta.query_advice(is_branch_init, Rotation::cur()) * meta.query_selector(q_enable)
            },
            s_rlp1,
            s_rlp2,
            s_advices,
            acc_s,
            acc_mult_s,
            acc_c,
            acc_mult_c,
            acc_r,
        );

        BranchAccChip::<F>::configure(
            meta,
            |meta| {
                let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
                let is_branch_child = meta.query_advice(is_branch_child, Rotation::cur());

                q_not_first * is_branch_child
            },
            s_rlp2,
            s_advices,
            acc_s,
            acc_mult_s,
            r_table.clone(),
        );

        BranchAccChip::<F>::configure(
            meta,
            |meta| {
                let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
                let is_branch_child = meta.query_advice(is_branch_child, Rotation::cur());

                q_not_first * is_branch_child
            },
            c_rlp2,
            c_advices,
            acc_c,
            acc_mult_c,
            r_table.clone(),
        );

        LeafKeyChip::<F>::configure(
            meta,
            |meta| {
                let not_first_level = meta.query_fixed(not_first_level, Rotation::cur());
                let is_leaf_s = meta.query_advice(is_leaf_s, Rotation::cur());

                not_first_level * is_leaf_s
            },
            s_rlp1,
            s_rlp2,
            c_rlp1,
            c_rlp2,
            s_advices,
            s_mod_node_hash_rlc,
            c_mod_node_hash_rlc,
            acc_s,
            acc_mult_s,
            key_rlc,
            key_rlc_mult,
            sel1,
            sel2,
            s_advices[IS_BRANCH_S_PLACEHOLDER_POS - LAYOUT_OFFSET],
            modified_node,
            is_account_leaf_storage_codehash_c,
            r_table.clone(),
            fixed_table.clone(),
            true,
        );

        LeafKeyChip::<F>::configure(
            meta,
            |meta| {
                let not_first_level = meta.query_fixed(not_first_level, Rotation::cur());
                let is_leaf_c = meta.query_advice(is_leaf_c, Rotation::cur());

                not_first_level * is_leaf_c
            },
            s_rlp1,
            s_rlp2,
            c_rlp1,
            c_rlp2,
            s_advices,
            s_mod_node_hash_rlc,
            c_mod_node_hash_rlc,
            acc_s,
            acc_mult_s,
            key_rlc,
            key_rlc_mult,
            sel1,
            sel2,
            s_advices[IS_BRANCH_C_PLACEHOLDER_POS - LAYOUT_OFFSET],
            modified_node,
            is_account_leaf_storage_codehash_c,
            r_table.clone(),
            fixed_table.clone(),
            false,
        );

        LeafKeyInAddedBranchChip::<F>::configure(
            meta,
            |meta| {
                let not_first_level = meta.query_fixed(not_first_level, Rotation::cur());
                let is_leaf = meta.query_advice(is_leaf_in_added_branch, Rotation::cur());

                not_first_level * is_leaf
            },
            s_rlp1,
            s_rlp2,
            c_rlp1,
            c_rlp2,
            s_advices,
            s_mod_node_hash_rlc,
            c_mod_node_hash_rlc,
            acc_s,
            acc_mult_s,
            key_rlc,
            key_rlc_mult,
            mult_diff,
            drifted_pos,
            is_account_leaf_storage_codehash_c,
            r_table.clone(),
            fixed_table.clone(),
            keccak_table.clone(),
        );

        LeafValueChip::<F>::configure(
            meta,
            |meta| {
                let not_first_level = meta.query_fixed(not_first_level, Rotation::cur());
                let is_leaf_s_value = meta.query_advice(is_leaf_s_value, Rotation::cur());

                not_first_level * is_leaf_s_value
            },
            s_rlp1,
            s_rlp2,
            s_advices,
            s_mod_node_hash_rlc,
            keccak_table,
            acc_s,
            acc_mult_s,
            sel1,
            is_account_leaf_storage_codehash_c,
            s_advices[IS_BRANCH_S_PLACEHOLDER_POS - LAYOUT_OFFSET],
            true,
            acc_r,
            fixed_table.clone(),
        );

        LeafValueChip::<F>::configure(
            meta,
            |meta| {
                let not_first_level = meta.query_fixed(not_first_level, Rotation::cur());
                let is_leaf_c_value = meta.query_advice(is_leaf_c_value, Rotation::cur());

                not_first_level * is_leaf_c_value
            },
            s_rlp1,
            s_rlp2,
            s_advices,
            c_mod_node_hash_rlc,
            keccak_table,
            acc_s,
            acc_mult_s,
            sel2,
            is_account_leaf_storage_codehash_c,
            s_advices[IS_BRANCH_C_PLACEHOLDER_POS - LAYOUT_OFFSET],
            false,
            acc_r,
            fixed_table.clone(),
        );

        AccountLeafKeyChip::<F>::configure(
            meta,
            |meta| {
                let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
                let is_account_leaf_key_s =
                    meta.query_advice(is_account_leaf_key_s, Rotation::cur());

                q_not_first * is_account_leaf_key_s
            },
            s_rlp1,
            s_rlp2,
            c_rlp1,
            c_rlp2,
            s_advices,
            acc_s,
            acc_mult_s,
            key_rlc,
            key_rlc_mult,
            r_table.clone(),
            fixed_table.clone(),
        );

        AccountLeafNonceBalanceChip::<F>::configure(
            meta,
            |meta| {
                let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
                let is_account_leaf_nonce_balance_s =
                    meta.query_advice(is_account_leaf_nonce_balance_s, Rotation::cur());
                q_not_first * is_account_leaf_nonce_balance_s
            },
            s_rlp1,
            s_rlp2,
            c_rlp1,
            c_rlp2,
            s_advices,
            c_advices,
            acc_s,
            acc_mult_s,
            acc_mult_c,
            key_rlc,
            key_rlc_mult,
            r_table.clone(),
            fixed_table.clone(),
        );

        AccountLeafStorageCodehashChip::<F>::configure(
            meta,
            q_not_first,
            not_first_level,
            is_account_leaf_storage_codehash_s,
            is_account_leaf_storage_codehash_c,
            s_rlp2,
            c_rlp2,
            s_advices,
            c_advices,
            acc_r,
            acc_s,
            acc_mult_s,
            fixed_table.clone(),
            s_mod_node_hash_rlc,
            keccak_table,
            true,
        );

        AccountLeafStorageCodehashChip::<F>::configure(
            meta,
            q_not_first,
            not_first_level,
            is_account_leaf_storage_codehash_s,
            is_account_leaf_storage_codehash_c,
            s_rlp2,
            c_rlp2,
            s_advices,
            c_advices,
            acc_r,
            acc_s,
            acc_mult_s,
            fixed_table.clone(),
            c_mod_node_hash_rlc,
            keccak_table,
            false,
        );

        MPTConfig {
            q_enable,
            q_not_first,
            not_first_level,
            is_branch_init,
            is_branch_child,
            is_last_branch_child,
            is_leaf_s,
            is_leaf_s_value,
            is_leaf_c,
            is_leaf_c_value,
            is_account_leaf_key_s,
            is_account_leaf_nonce_balance_s,
            is_account_leaf_nonce_balance_c,
            is_account_leaf_storage_codehash_s,
            is_account_leaf_storage_codehash_c,
            node_index,
            is_modified,
            modified_node,
            is_at_drifted_pos,
            drifted_pos,
            is_leaf_in_added_branch,
            is_extension_node_s,
            is_extension_node_c,
            s_rlp1,
            s_rlp2,
            c_rlp1,
            c_rlp2,
            s_advices,
            c_advices,
            s_mod_node_hash_rlc,
            c_mod_node_hash_rlc,
            s_root,
            c_root,
            acc_s,
            acc_mult_s,
            acc_c,
            acc_mult_c,
            acc_r,
            sel1,
            sel2,
            r_table,
            key_rlc,
            key_rlc_mult,
            mult_diff,
            keccak_table,
            fixed_table,
            _marker: PhantomData,
        }
    }

    fn assign_row(
        &self,
        region: &mut Region<'_, F>,
        row: &[u8],
        is_branch_init: bool,
        is_branch_child: bool,
        is_last_branch_child: bool,
        node_index: u8,
        modified_node: u8,
        is_leaf_s: bool,
        is_leaf_s_value: bool,
        is_leaf_c: bool,
        is_leaf_c_value: bool,
        is_account_leaf_key_s: bool,
        is_account_leaf_nonce_balance_s: bool,
        is_account_leaf_nonce_balance_c: bool,
        is_account_leaf_storage_codehash_s: bool,
        is_account_leaf_storage_codehash_c: bool,
        drifted_pos: u8,
        is_leaf_in_added_branch: bool,
        is_extension_node_s: bool,
        is_extension_node_c: bool,
        offset: usize,
    ) -> Result<(), Error> {
        region.assign_advice(
            || "assign is_branch_init".to_string(),
            self.is_branch_init,
            offset,
            || Ok(F::from(is_branch_init as u64)),
        )?;

        region.assign_advice(
            || "assign is_branch_child".to_string(),
            self.is_branch_child,
            offset,
            || Ok(F::from(is_branch_child as u64)),
        )?;

        region.assign_advice(
            || "assign acc_s".to_string(),
            self.acc_s,
            offset,
            || Ok(F::zero()),
        )?;

        region.assign_advice(
            || "assign acc_mult_s".to_string(),
            self.acc_mult_s,
            offset,
            || Ok(F::zero()),
        )?;

        region.assign_advice(
            || "assign acc_c".to_string(),
            self.acc_c,
            offset,
            || Ok(F::zero()),
        )?;

        region.assign_advice(
            || "assign acc_mult_c".to_string(),
            self.acc_mult_c,
            offset,
            || Ok(F::zero()),
        )?;

        // because used for is_long
        region.assign_advice(
            || "assign s_modified_node_rlc".to_string(),
            self.s_mod_node_hash_rlc,
            offset,
            || Ok(F::zero()),
        )?;
        // because used for is_short
        region.assign_advice(
            || "assign c_modified_node_rlc".to_string(),
            self.c_mod_node_hash_rlc,
            offset,
            || Ok(F::zero()),
        )?;

        region.assign_advice(
            || "assign is_last_branch_child".to_string(),
            self.is_last_branch_child,
            offset,
            || Ok(F::from(is_last_branch_child as u64)),
        )?;

        region.assign_advice(
            || "assign node_index".to_string(),
            self.node_index,
            offset,
            || Ok(F::from(node_index as u64)),
        )?;

        region.assign_advice(
            || "assign modified node".to_string(),
            self.modified_node,
            offset,
            || Ok(F::from(modified_node as u64)),
        )?;

        region.assign_advice(
            || "assign drifted_pos".to_string(),
            self.drifted_pos,
            offset,
            || Ok(F::from(drifted_pos as u64)),
        )?;

        region.assign_advice(
            || "assign is_at_drifted_pos".to_string(),
            self.is_at_drifted_pos,
            offset,
            || Ok(F::from((drifted_pos == node_index) as u64)),
        )?;

        region.assign_advice(
            || "assign key rlc".to_string(),
            self.key_rlc,
            offset,
            || Ok(F::zero()),
        )?;

        region.assign_advice(
            || "assign key rlc mult".to_string(),
            self.key_rlc_mult,
            offset,
            || Ok(F::zero()),
        )?;

        region.assign_advice(
            || "assign mult diff".to_string(),
            self.mult_diff,
            offset,
            || Ok(F::zero()),
        )?;

        region.assign_advice(
            || "assign sel1".to_string(),
            self.sel1,
            offset,
            || Ok(F::zero()),
        )?;
        region.assign_advice(
            || "assign sel2".to_string(),
            self.sel2,
            offset,
            || Ok(F::zero()),
        )?;

        region.assign_advice(
            || "assign is_modified".to_string(),
            self.is_modified,
            offset,
            || Ok(F::from((modified_node == node_index) as u64)),
        )?;

        region.assign_advice(
            || "assign is_leaf_s".to_string(),
            self.is_leaf_s,
            offset,
            || Ok(F::from(is_leaf_s as u64)),
        )?;
        region.assign_advice(
            || "assign is_leaf_c".to_string(),
            self.is_leaf_c,
            offset,
            || Ok(F::from(is_leaf_c as u64)),
        )?;

        region.assign_advice(
            || "assign is_leaf_s_value".to_string(),
            self.is_leaf_s_value,
            offset,
            || Ok(F::from(is_leaf_s_value as u64)),
        )?;
        region.assign_advice(
            || "assign is_leaf_c_value".to_string(),
            self.is_leaf_c_value,
            offset,
            || Ok(F::from(is_leaf_c_value as u64)),
        )?;

        region.assign_advice(
            || "assign is account leaf key s".to_string(),
            self.is_account_leaf_key_s,
            offset,
            || Ok(F::from(is_account_leaf_key_s as u64)),
        )?;
        region.assign_advice(
            || "assign is account leaf nonce balance s".to_string(),
            self.is_account_leaf_nonce_balance_s,
            offset,
            || Ok(F::from(is_account_leaf_nonce_balance_s as u64)),
        )?;
        region.assign_advice(
            || "assign is account leaf nonce balance c".to_string(),
            self.is_account_leaf_nonce_balance_c,
            offset,
            || Ok(F::from(is_account_leaf_nonce_balance_c as u64)),
        )?;
        region.assign_advice(
            || "assign is account leaf storage codehash s".to_string(),
            self.is_account_leaf_storage_codehash_s,
            offset,
            || Ok(F::from(is_account_leaf_storage_codehash_s as u64)),
        )?;
        region.assign_advice(
            || "assign is account leaf storage codehash c".to_string(),
            self.is_account_leaf_storage_codehash_c,
            offset,
            || Ok(F::from(is_account_leaf_storage_codehash_c as u64)),
        )?;

        region.assign_advice(
            || "assign is leaf in added branch".to_string(),
            self.is_leaf_in_added_branch,
            offset,
            || Ok(F::from(is_leaf_in_added_branch as u64)),
        )?;
        region.assign_advice(
            || "assign is extension node s".to_string(),
            self.is_extension_node_s,
            offset,
            || Ok(F::from(is_extension_node_s as u64)),
        )?;
        region.assign_advice(
            || "assign is extension node c".to_string(),
            self.is_extension_node_c,
            offset,
            || Ok(F::from(is_extension_node_c as u64)),
        )?;

        region.assign_advice(
            || "assign s_rlp1".to_string(),
            self.s_rlp1,
            offset,
            || Ok(F::from(row[0] as u64)),
        )?;

        region.assign_advice(
            || "assign s_rlp2".to_string(),
            self.s_rlp2,
            offset,
            || Ok(F::from(row[1] as u64)),
        )?;

        for idx in 0..HASH_WIDTH {
            region.assign_advice(
                || format!("assign s_advice {}", idx),
                self.s_advices[idx],
                offset,
                || Ok(F::from(row[LAYOUT_OFFSET + idx] as u64)),
            )?;
        }

        // not all columns may be needed
        let get_val = |curr_ind: usize| {
            let val;
            if curr_ind >= row.len() {
                val = 0;
            } else {
                val = row[curr_ind];
            }

            val as u64
        };

        region.assign_advice(
            || "assign c_rlp1".to_string(),
            self.c_rlp1,
            offset,
            || Ok(F::from(get_val(WITNESS_ROW_WIDTH / 2))),
        )?;
        region.assign_advice(
            || "assign c_rlp2".to_string(),
            self.c_rlp2,
            offset,
            || Ok(F::from(get_val(WITNESS_ROW_WIDTH / 2 + 1))),
        )?;

        for (idx, _c) in self.c_advices.iter().enumerate() {
            let val = get_val(WITNESS_ROW_WIDTH / 2 + LAYOUT_OFFSET + idx);
            region.assign_advice(
                || format!("assign c_advice {}", idx),
                self.c_advices[idx],
                offset,
                || Ok(F::from(val)),
            )?;
        }
        Ok(())
    }

    fn assign_branch_init(
        &self,
        region: &mut Region<'_, F>,
        row: &Vec<u8>,
        offset: usize,
    ) -> Result<(), Error> {
        self.assign_row(
            region, row, true, false, false, 0, 0, false, false, false, false, false, false, false,
            false, false, 0, false, false, false, offset,
        )?;

        Ok(())
    }

    fn assign_branch_row(
        &self,
        region: &mut Region<'_, F>,
        node_index: u8,
        key: u8,
        key_rlc: F,
        key_rlc_mult: F,
        mult_diff: F,
        row: &[u8],
        s_mod_node_hash_rlc: F,
        c_mod_node_hash_rlc: F,
        drifted_pos: u8,
        s_rlp1: i32,
        c_rlp1: i32,
        offset: usize,
    ) -> Result<(), Error> {
        self.assign_row(
            region,
            row,
            false,
            true,
            node_index == 15,
            node_index,
            key,
            false,
            false,
            false,
            false,
            false,
            false,
            false,
            false,
            false,
            drifted_pos,
            false,
            false,
            false,
            offset,
        )?;

        region.assign_advice(
            || "s_mod_node_hash_rlc",
            self.s_mod_node_hash_rlc,
            offset,
            || Ok(s_mod_node_hash_rlc),
        )?;
        region.assign_advice(
            || "c_mod_node_hash_rlc",
            self.c_mod_node_hash_rlc,
            offset,
            || Ok(c_mod_node_hash_rlc),
        )?;

        region.assign_advice(|| "key rlc", self.key_rlc, offset, || Ok(key_rlc))?;
        region.assign_advice(
            || "key rlc mult",
            self.key_rlc_mult,
            offset,
            || Ok(key_rlc_mult),
        )?;
        region.assign_advice(|| "mult diff", self.mult_diff, offset, || Ok(mult_diff))?;

        region.assign_advice(
            || "s_rlp1",
            self.s_rlp1,
            offset,
            || Ok(F::from(s_rlp1 as u64)),
        )?;
        region.assign_advice(
            || "c_rlp1",
            self.c_rlp1,
            offset,
            || Ok(F::from(c_rlp1 as u64)),
        )?;

        Ok(())
    }

    fn assign_acc(
        &self,
        region: &mut Region<'_, F>,
        acc_s: F,
        acc_mult_s: F,
        acc_c: F,
        acc_mult_c: F,
        offset: usize,
    ) -> Result<(), Error> {
        region.assign_advice(
            || "assign acc_s".to_string(),
            self.acc_s,
            offset,
            || Ok(acc_s),
        )?;

        region.assign_advice(
            || "assign acc_mult_s".to_string(),
            self.acc_mult_s,
            offset,
            || Ok(acc_mult_s),
        )?;

        region.assign_advice(
            || "assign acc_c".to_string(),
            self.acc_c,
            offset,
            || Ok(acc_c),
        )?;

        region.assign_advice(
            || "assign acc_mult_c".to_string(),
            self.acc_mult_c,
            offset,
            || Ok(acc_mult_c),
        )?;

        Ok(())
    }

    // TODO: split assign
    pub(crate) fn assign(&self, mut layouter: impl Layouter<F>, witness: &[Vec<u8>]) {
        layouter
            .assign_region(
                || "MPT",
                |mut region| {
                    let mut offset = 0;

                    let mut modified_node = 0;
                    let mut s_mod_node_hash_rlc = F::zero();
                    let mut c_mod_node_hash_rlc = F::zero();
                    let mut node_index: u8 = 0;
                    let mut acc_s = F::zero();
                    let mut acc_mult_s = F::zero();
                    let mut acc_nonce_balance_s = F::zero();
                    let mut acc_mult_nonce_balance_s = F::zero();
                    let mut acc_nonce_balance_c = F::zero();
                    let mut acc_mult_nonce_balance_c = F::zero();

                    let mut acc_c = F::zero();
                    let mut acc_mult_c = F::zero();
                    let mut key_rlc = F::zero(); // used first for account address, then for storage key
                    let mut key_rlc_mult = F::one();
                    let mut extension_node_rlc = F::zero();
                    let mut key_rlc_prev = F::zero(); // for leaf after placeholder extension/branch, we need to go one level back to
                                                      // get previous key_rlc
                    let mut key_rlc_mult_prev = F::one();

                    let mut mult_diff = F::one();
                    let mut key_rlc_sel = true; // If true, nibble is multiplied by 16, otherwise by 1.
                    let mut is_branch_s_placeholder = false;
                    let mut is_branch_c_placeholder = false;

                    let mut drifted_pos: u8 = 0; // needed when leaf turned into branch and leaf moves into a branch where it's
                                                 // at drifted_pos position
                    let mut rlp_len_rem_s: i32 = 0; // branch RLP length remainder, in each branch children row this value is
                                                    // subtracted by the number of RLP bytes in this row (1 or 33)
                    let mut rlp_len_rem_c: i32 = 0;

                    let mut is_extension_node = false;
                    let mut is_even = false;
                    let mut is_odd = false;
                    let mut is_short = false;
                    let mut is_long = false;

                    let compute_acc_and_mult =
                        |row: &Vec<u8>, acc: &mut F, mult: &mut F, start: usize, len: usize| {
                            for i in 0..len {
                                *acc += F::from(row[start + i] as u64) * *mult;
                                *mult *= self.acc_r;
                            }
                        };

                    // TODO: constraints for not_first_level - avoid having not_first_level
                    // being set wrongly (further down in rows)
                    let mut not_first_level = F::zero();
                    // filter out rows that are just to be hashed
                    for (ind, row) in witness
                        .iter()
                        .filter(|r| r[r.len() - 1] != 5 && r[r.len() - 1] != 4)
                        .enumerate()
                    {
                        if ind == 19_usize && row[row.len() - 1] == 0 {
                            // when the first branch ends
                            // TODO: what if extension node is first
                            not_first_level = F::one();
                        }
                        region.assign_fixed(
                            || "not first level",
                            self.not_first_level,
                            offset,
                            || Ok(not_first_level),
                        )?;

                        let mut s_root_rlc = F::zero();
                        let mut c_root_rlc = F::zero();
                        let l = row.len();
                        let mut mult = F::one();
                        for i in 0..HASH_WIDTH {
                            s_root_rlc +=
                                F::from(row[l - 2 * HASH_WIDTH + i] as u64) * mult.clone();
                            mult *= self.acc_r;
                        }
                        let mut mult = F::one();
                        for i in 0..HASH_WIDTH {
                            c_root_rlc += F::from(row[l - HASH_WIDTH + i] as u64) * mult.clone();
                            mult *= self.acc_r;
                        }
                        region.assign_advice(
                            || "assign s_root",
                            self.s_root,
                            offset,
                            || Ok(s_root_rlc),
                        )?;
                        region.assign_advice(
                            || "assign c_root",
                            self.c_root,
                            offset,
                            || Ok(c_root_rlc),
                        )?;

                        if row[row.len() - 1] == 0 {
                            // branch init
                            modified_node = row[BRANCH_0_KEY_POS];
                            node_index = 0;
                            drifted_pos = row[DRIFTED_POS];

                            // Get the child that is being changed and convert it to words to enable
                            // lookups:
                            let mut s_hash = witness[ind + 1 + modified_node as usize]
                                [S_START..S_START + HASH_WIDTH]
                                .to_vec();
                            let mut c_hash = witness[ind + 1 + modified_node as usize]
                                [C_START..C_START + HASH_WIDTH]
                                .to_vec();
                            s_mod_node_hash_rlc = hash_into_rlc(&s_hash, self.acc_r);
                            c_mod_node_hash_rlc = hash_into_rlc(&c_hash, self.acc_r);

                            if row[IS_BRANCH_S_PLACEHOLDER_POS] == 1 {
                                // We put hash of a node that moved down to the added branch.
                                // This is needed to check the hash of leaf_in_added_branch.
                                s_hash = witness[ind + 1 + drifted_pos as usize]
                                    [S_START..S_START + HASH_WIDTH]
                                    .to_vec();
                                s_mod_node_hash_rlc = hash_into_rlc(&s_hash, self.acc_r);
                                is_branch_s_placeholder = true
                            } else {
                                is_branch_s_placeholder = false
                            }
                            if row[IS_BRANCH_C_PLACEHOLDER_POS] == 1 {
                                c_hash = witness[ind + 1 + drifted_pos as usize]
                                    [C_START..C_START + HASH_WIDTH]
                                    .to_vec();
                                c_mod_node_hash_rlc = hash_into_rlc(&c_hash, self.acc_r);
                                is_branch_c_placeholder = true
                            } else {
                                is_branch_c_placeholder = false
                            }
                            // If no placeholder branch, we set drifted_pos = modified_node. This
                            // is needed just to make some other constraints (s_mod_node_hash_rlc
                            // and c_mod_node_hash_rlc correspond to the proper node) easier to
                            // write.
                            if row[IS_BRANCH_S_PLACEHOLDER_POS] == 0
                                && row[IS_BRANCH_C_PLACEHOLDER_POS] == 0
                            {
                                drifted_pos = modified_node
                            }

                            self.q_enable.enable(&mut region, offset)?;
                            if ind == 0 {
                                region.assign_fixed(
                                    || "not first",
                                    self.q_not_first,
                                    offset,
                                    || Ok(F::zero()),
                                )?;
                            } else {
                                region.assign_fixed(
                                    || "not first",
                                    self.q_not_first,
                                    offset,
                                    || Ok(F::one()),
                                )?;
                            }
                            self.assign_branch_init(
                                &mut region,
                                &row[0..row.len() - 1].to_vec(),
                                offset,
                            )?;

                            // reassign (it was assigned to 0 in assign_row) branch_acc and
                            // branch_mult to proper values

                            // Branch (length 83) with two bytes of RLP meta data
                            // [248,81,128,128,...

                            // Branch (length 340) with three bytes of RLP meta data
                            // [249,1,81,128,16,...

                            acc_s = F::from(row[BRANCH_0_S_START] as u64)
                                + F::from(row[BRANCH_0_S_START + 1] as u64) * self.acc_r;
                            acc_mult_s = self.acc_r * self.acc_r;

                            if row[BRANCH_0_S_START] == 249 {
                                acc_s += F::from(row[BRANCH_0_S_START + 2] as u64) * acc_mult_s;
                                acc_mult_s *= self.acc_r;

                                rlp_len_rem_s = row[BRANCH_0_S_START + 1] as i32 * 256
                                    + row[BRANCH_0_S_START + 2] as i32;
                            } else {
                                rlp_len_rem_s = row[BRANCH_0_S_START + 1] as i32;
                            }

                            acc_c = F::from(row[BRANCH_0_C_START] as u64)
                                + F::from(row[BRANCH_0_C_START + 1] as u64) * self.acc_r;
                            acc_mult_c = self.acc_r * self.acc_r;

                            if row[BRANCH_0_C_START] == 249 {
                                acc_c += F::from(row[BRANCH_0_C_START + 2] as u64) * acc_mult_c;
                                acc_mult_c *= self.acc_r;

                                rlp_len_rem_c = row[BRANCH_0_C_START + 1] as i32 * 256
                                    + row[BRANCH_0_C_START + 2] as i32;
                            } else {
                                rlp_len_rem_c = row[BRANCH_0_C_START + 1] as i32;
                            }

                            self.assign_acc(
                                &mut region,
                                acc_s,
                                acc_mult_s,
                                acc_c,
                                acc_mult_c,
                                offset,
                            )?;

                            // sel1 and sel2 are here to distinguish whether it's the
                            // first or the second nibble of the key byte
                            // If sel1 = 1 and short, we have one nibble+48 in s_advices[0].
                            // If sel1 = 1 and long, we have nibble+48 in s_advices[1].
                            // If sel2 = 1 and short, we have 32 in s_advices[0].
                            // If sel2 = 1 and long, we have 32 in s_advices[1].

                            // TODO: remove sel1, sel2, this is now set in witness generator.

                            // Note that if the last branch is placeholder,
                            // sel1 and sel2 are still switched at this branch which
                            // needs to be considered in leaf rows.
                            let mut sel1 = F::zero();
                            let mut sel2 = F::zero();
                            // extension node:
                            is_even = witness[offset][IS_EXT_LONG_EVEN_C16_POS]
                                + witness[offset][IS_EXT_LONG_EVEN_C1_POS]
                                == 1;
                            is_odd = witness[offset][IS_EXT_LONG_ODD_C16_POS]
                                + witness[offset][IS_EXT_LONG_ODD_C1_POS]
                                + witness[offset][IS_EXT_SHORT_C16_POS]
                                + witness[offset][IS_EXT_SHORT_C1_POS]
                                == 1;
                            is_short = witness[offset][IS_EXT_SHORT_C16_POS]
                                + witness[offset][IS_EXT_SHORT_C1_POS]
                                == 1;
                            is_long = witness[offset][IS_EXT_LONG_EVEN_C16_POS]
                                + witness[offset][IS_EXT_LONG_EVEN_C1_POS]
                                + witness[offset][IS_EXT_LONG_ODD_C16_POS]
                                + witness[offset][IS_EXT_LONG_ODD_C1_POS]
                                == 1;
                            is_extension_node = is_even == true || is_odd == true;
                            // end of extension node

                            if !is_extension_node {
                                if key_rlc_sel {
                                    sel1 = F::one();
                                } else {
                                    sel2 = F::one();
                                }
                            } else {
                                if key_rlc_sel {
                                    if is_even && is_long {
                                        sel1 = F::one();
                                    } else if is_odd && is_long {
                                        sel2 = F::one();
                                    } else if is_short {
                                        sel2 = F::one();
                                    }
                                } else {
                                    if is_even && is_long {
                                        sel2 = F::one();
                                    } else if is_odd && is_long {
                                        sel1 = F::one();
                                    } else if is_short {
                                        sel1 = F::one();
                                    }
                                }
                            }
                            region.assign_advice(
                                || "assign sel1".to_string(),
                                self.sel1,
                                offset,
                                || Ok(sel1),
                            )?;
                            region.assign_advice(
                                || "assign sel2".to_string(),
                                self.sel2,
                                offset,
                                || Ok(sel2),
                            )?;

                            offset += 1;
                        } else if row[row.len() - 1] == 1 {
                            // branch child
                            self.q_enable.enable(&mut region, offset)?;
                            region.assign_fixed(
                                || "not first",
                                self.q_not_first,
                                offset,
                                || Ok(F::one()),
                            )?;

                            if row[S_RLP_START + 1] == 160 {
                                rlp_len_rem_s -= 33;
                            } else {
                                rlp_len_rem_s -= 1;
                            }
                            if row[C_RLP_START + 1] == 160 {
                                rlp_len_rem_c -= 33;
                            } else {
                                rlp_len_rem_c -= 1;
                            }

                            if node_index == 0 {
                                // If it's not extension node, rlc and rlc_mult in extension row
                                // will be the same as for branch rlc.
                                extension_node_rlc = key_rlc;

                                key_rlc_prev = key_rlc;
                                key_rlc_mult_prev = key_rlc_mult;

                                if is_extension_node
                                // Extension node
                                // We need nibbles here to be able to compute key RLC
                                {
                                    // For key RLC, we need to first take into account
                                    // extension node key.
                                    // witness[offset + 16]
                                    let ext_row = &witness[ind + 16];

                                    if key_rlc_sel {
                                        // Note: it can't be is_even = 1 && is_short = 1.
                                        if is_even && is_long {
                                            // extension node part:
                                            let key_len = ext_row[1] as usize - 128 - 1; // -1 because the first byte is 0 (is_even)
                                            compute_acc_and_mult(
                                                ext_row,
                                                &mut extension_node_rlc,
                                                &mut key_rlc_mult,
                                                3, /* first two positions are RLPs, third
                                                    * position is 0 (because is_even), we start
                                                    * with fourth */
                                                key_len,
                                            );
                                            mult_diff = F::one();
                                            for _ in 0..key_len {
                                                mult_diff *= self.acc_r;
                                            }
                                            key_rlc = extension_node_rlc;
                                            // branch part:
                                            key_rlc += F::from(modified_node as u64)
                                                * F::from(16)
                                                * key_rlc_mult;
                                            // key_rlc_mult stays the same
                                            key_rlc_sel = !key_rlc_sel;
                                        } else if is_odd && is_long {
                                            // extension node part:
                                            extension_node_rlc += F::from((ext_row[2] - 16) as u64)
                                                * F::from(16)
                                                * key_rlc_mult;

                                            let ext_row_c = &witness[ind + 17];
                                            let key_len = ext_row[1] as usize - 128 - 1;

                                            mult_diff = F::one();
                                            for k in 0..key_len {
                                                let second_nibble = ext_row_c[S_START + k];
                                                let first_nibble =
                                                    (ext_row[3 + k] - second_nibble) / 16;
                                                assert_eq!(
                                                    first_nibble * 16 + second_nibble,
                                                    ext_row[3 + k],
                                                );
                                                extension_node_rlc +=
                                                    F::from(first_nibble as u64) * key_rlc_mult;

                                                key_rlc_mult *= self.acc_r;
                                                mult_diff *= self.acc_r;

                                                extension_node_rlc += F::from(second_nibble as u64)
                                                    * F::from(16)
                                                    * key_rlc_mult;
                                            }

                                            key_rlc = extension_node_rlc;
                                            // branch part:
                                            key_rlc += F::from(modified_node as u64) * key_rlc_mult;
                                            key_rlc_mult *= self.acc_r;
                                        } else if is_short {
                                            extension_node_rlc += F::from((ext_row[1] - 16) as u64)
                                                * F::from(16)
                                                * key_rlc_mult;
                                            key_rlc = extension_node_rlc;
                                            // branch part:
                                            key_rlc += F::from(modified_node as u64) * key_rlc_mult;
                                            key_rlc_mult *= self.acc_r;
                                            mult_diff = self.acc_r;
                                        }
                                    } else {
                                        if is_even && is_long {
                                            // extension node part:
                                            let ext_row_c = &witness[ind + 17];
                                            let key_len = ext_row[1] as usize - 128 - 1; // -1 because the first byte is 0 (is_even)

                                            mult_diff = F::one();
                                            for k in 0..key_len {
                                                let second_nibble = ext_row_c[S_START + k];
                                                let first_nibble =
                                                    (ext_row[3 + k] - second_nibble) / 16;
                                                assert_eq!(
                                                    first_nibble * 16 + second_nibble,
                                                    ext_row[3 + k],
                                                );
                                                extension_node_rlc +=
                                                    F::from(first_nibble as u64) * key_rlc_mult;

                                                key_rlc_mult *= self.acc_r;
                                                mult_diff *= self.acc_r;

                                                extension_node_rlc += F::from(16)
                                                    * F::from(second_nibble as u64)
                                                    * key_rlc_mult;
                                            }

                                            key_rlc = extension_node_rlc;
                                            // branch part:
                                            key_rlc += F::from(modified_node as u64) * key_rlc_mult;
                                            key_rlc_mult *= self.acc_r;
                                            key_rlc_sel = !key_rlc_sel;
                                        } else if is_odd && is_long {
                                            extension_node_rlc +=
                                                F::from((ext_row[2] - 16) as u64) * key_rlc_mult;

                                            key_rlc_mult *= self.acc_r;

                                            let key_len = ext_row[1] as usize - 128 - 1; // -1 because the first byte is 0 (is_even)

                                            compute_acc_and_mult(
                                                ext_row,
                                                &mut extension_node_rlc,
                                                &mut key_rlc_mult,
                                                3, /* first two positions are RLPs, third
                                                    * position is 0 (because is_even), we start
                                                    * with fourth */
                                                key_len,
                                            );
                                            mult_diff = F::one();
                                            for _ in 0..key_len {
                                                mult_diff *= self.acc_r;
                                            }
                                            key_rlc = extension_node_rlc;
                                            // branch part:
                                            key_rlc += F::from(modified_node as u64)
                                                * F::from(16)
                                                * key_rlc_mult;
                                            // key_rlc_mult stays the same
                                        } else if is_short {
                                            extension_node_rlc +=
                                                F::from((ext_row[1] - 16) as u64) * key_rlc_mult;

                                            key_rlc = extension_node_rlc;

                                            key_rlc_mult *= self.acc_r;
                                            // branch part:
                                            key_rlc += F::from(modified_node as u64)
                                                * F::from(16)
                                                * key_rlc_mult;
                                            mult_diff = self.acc_r;
                                        }
                                    }
                                } else {
                                    if key_rlc_sel {
                                        key_rlc += F::from(modified_node as u64)
                                            * F::from(16)
                                            * key_rlc_mult;
                                        // key_rlc_mult stays the same
                                    } else {
                                        key_rlc += F::from(modified_node as u64) * key_rlc_mult;
                                        key_rlc_mult *= self.acc_r;
                                    }
                                    key_rlc_sel = !key_rlc_sel;
                                }
                                self.assign_branch_row(
                                    &mut region,
                                    node_index,
                                    modified_node,
                                    key_rlc,
                                    key_rlc_mult,
                                    mult_diff,
                                    &row[0..row.len() - 1].to_vec(),
                                    s_mod_node_hash_rlc,
                                    c_mod_node_hash_rlc,
                                    drifted_pos,
                                    rlp_len_rem_s,
                                    rlp_len_rem_c,
                                    offset,
                                )?;
                            } else {
                                // Note that key_rlc and key_rlc_mult are set the same in all
                                // branch children to avoid some rotations - constraint for this
                                // equality is in extension_node_key.
                                self.assign_branch_row(
                                    &mut region,
                                    node_index,
                                    modified_node,
                                    key_rlc,
                                    key_rlc_mult,
                                    mult_diff,
                                    &row[0..row.len() - 1].to_vec(),
                                    s_mod_node_hash_rlc,
                                    c_mod_node_hash_rlc,
                                    drifted_pos,
                                    rlp_len_rem_s,
                                    rlp_len_rem_c,
                                    offset,
                                )?;
                                // sel1 is to distinguish whether the S node is empty.
                                // sel2 is to distinguish whether the C node is empty.
                                // Note that 128 comes from the RLP byte denoting empty leaf.
                                // Having 128 for *_mod_node_hash_rlc means there is no node at
                                // this position in branch - for example,
                                // s_mode_node_hash_rlc = 128 and c_words is some other value
                                // when new value is added to the trie
                                // (as opposed to just updating the value).
                                // Note that there is a potential attack if a leaf node
                                // is found with hash [128, 0, ..., 0],
                                // but the probability is negligible.
                                let mut sel1 = F::zero();
                                let mut sel2 = F::zero();
                                if s_mod_node_hash_rlc == F::from(128 as u64) {
                                    sel1 = F::one();
                                }
                                if c_mod_node_hash_rlc == F::from(128 as u64) {
                                    sel2 = F::one();
                                }

                                region.assign_advice(
                                    || "assign sel1".to_string(),
                                    self.sel1,
                                    offset,
                                    || Ok(sel1),
                                )?;
                                region.assign_advice(
                                    || "assign sel2".to_string(),
                                    self.sel2,
                                    offset,
                                    || Ok(sel2),
                                )?;
                            }

                            // reassign (it was assigned to 0 in assign_row) branch_acc and
                            // branch_mult to proper values

                            // We need to distinguish between empty and non-empty node:
                            // empty node at position 1: 0
                            // non-empty node at position 1: 160

                            let c128 = F::from(128_u64);
                            let c160 = F::from(160_u64);

                            let compute_branch_acc_and_mult =
                                |branch_acc: &mut F,
                                 branch_mult: &mut F,
                                 rlp_start: usize,
                                 start: usize| {
                                    if row[rlp_start + 1] == 0 {
                                        *branch_acc += c128 * *branch_mult;
                                        *branch_mult *= self.acc_r;
                                    } else {
                                        *branch_acc += c160 * *branch_mult;
                                        *branch_mult *= self.acc_r;
                                        for i in 0..HASH_WIDTH {
                                            *branch_acc +=
                                                F::from(row[start + i] as u64) * *branch_mult;
                                            *branch_mult *= self.acc_r;
                                        }
                                    }
                                };

                            // TODO: add branch ValueNode info

                            compute_branch_acc_and_mult(
                                &mut acc_s,
                                &mut acc_mult_s,
                                S_RLP_START,
                                S_START,
                            );
                            compute_branch_acc_and_mult(
                                &mut acc_c,
                                &mut acc_mult_c,
                                C_RLP_START,
                                C_START,
                            );
                            self.assign_acc(
                                &mut region,
                                acc_s,
                                acc_mult_s,
                                acc_c,
                                acc_mult_c,
                                offset,
                            )?;

                            // This is to avoid Poisoned Constraint in extension_node_key.
                            region.assign_advice(
                                || "assign key_rlc".to_string(),
                                self.key_rlc,
                                offset,
                                || Ok(key_rlc),
                            )?;
                            region.assign_advice(
                                || "assign key_rlc_mult".to_string(),
                                self.key_rlc_mult,
                                offset,
                                || Ok(key_rlc_mult),
                            )?;

                            offset += 1;
                            node_index += 1;
                        } else if row[row.len() - 1] == 2
                            || row[row.len() - 1] == 3
                            || row[row.len() - 1] == 6
                            || row[row.len() - 1] == 7
                            || row[row.len() - 1] == 8
                            || row[row.len() - 1] == 9
                            || row[row.len() - 1] == 11
                            || row[row.len() - 1] == 13
                            || row[row.len() - 1] == 14
                            || row[row.len() - 1] == 15
                            || row[row.len() - 1] == 16
                            || row[row.len() - 1] == 17
                        {
                            // leaf s or leaf c or leaf key s or leaf key c
                            self.q_enable.enable(&mut region, offset)?;
                            region.assign_fixed(
                                || "not first",
                                self.q_not_first,
                                offset,
                                || Ok(F::one()),
                            )?;
                            let mut is_leaf_s = false;
                            let mut is_leaf_s_value = false;
                            let mut is_leaf_c = false;
                            let mut is_leaf_c_value = false;

                            let mut is_account_leaf_key_s = false;
                            let mut is_account_leaf_nonce_balance_s = false;
                            let mut is_account_leaf_nonce_balance_c = false;
                            let mut is_account_leaf_storage_codehash_s = false;
                            let mut is_account_leaf_storage_codehash_c = false;

                            let mut is_leaf_in_added_branch = false;
                            let mut is_extension_node_s = false;
                            let mut is_extension_node_c = false;

                            if row[row.len() - 1] == 2 {
                                is_leaf_s = true;
                            } else if row[row.len() - 1] == 3 {
                                is_leaf_c = true;
                            } else if row[row.len() - 1] == 6 {
                                is_account_leaf_key_s = true;
                            } else if row[row.len() - 1] == 7 {
                                is_account_leaf_nonce_balance_s = true;
                            } else if row[row.len() - 1] == 8 {
                                is_account_leaf_nonce_balance_c = true;
                            } else if row[row.len() - 1] == 9 {
                                is_account_leaf_storage_codehash_s = true;
                            } else if row[row.len() - 1] == 11 {
                                is_account_leaf_storage_codehash_c = true;
                                key_rlc = F::zero(); // account address until here, storage key from here on
                                key_rlc_mult = F::one();
                                key_rlc_sel = true;
                            } else if row[row.len() - 1] == 13 {
                                is_leaf_s_value = true;
                            } else if row[row.len() - 1] == 14 {
                                is_leaf_c_value = true;
                            } else if row[row.len() - 1] == 15 {
                                is_leaf_in_added_branch = true;
                            } else if row[row.len() - 1] == 16 {
                                is_extension_node_s = true;
                            } else if row[row.len() - 1] == 17 {
                                is_extension_node_c = true;
                            }

                            self.assign_row(
                                &mut region,
                                &row[0..row.len() - 1].to_vec(),
                                false,
                                false,
                                false,
                                0,
                                0,
                                is_leaf_s,
                                is_leaf_s_value,
                                is_leaf_c,
                                is_leaf_c_value,
                                is_account_leaf_key_s,
                                is_account_leaf_nonce_balance_s,
                                is_account_leaf_nonce_balance_c,
                                is_account_leaf_storage_codehash_s,
                                is_account_leaf_storage_codehash_c,
                                0,
                                is_leaf_in_added_branch,
                                is_extension_node_s,
                                is_extension_node_c,
                                offset,
                            )?;

                            let mut assign_long_short = |region: &mut Region<'_, F>, long: bool| {
                                let mut is_short = false;
                                let mut is_long = false;
                                if long {
                                    is_long = true;
                                } else {
                                    is_short = true;
                                }
                                region
                                    .assign_advice(
                                        || "assign s_modified_node_rlc".to_string(),
                                        self.s_mod_node_hash_rlc,
                                        offset,
                                        || Ok(F::from(is_long as u64)),
                                    )
                                    .ok();
                                region
                                    .assign_advice(
                                        || "assign c_modified_node_rlc".to_string(),
                                        self.c_mod_node_hash_rlc,
                                        offset,
                                        || Ok(F::from(is_short as u64)),
                                    )
                                    .ok();
                            };

                            let compute_key_rlc =
                                |key_rlc: &mut F, key_rlc_mult: &mut F, start: usize| {
                                    let even_num_of_nibbles = row[start + 1] == 32;
                                    // If odd number of nibbles, we have nibble+48 in s_advices[0].
                                    if !even_num_of_nibbles {
                                        *key_rlc +=
                                            F::from((row[start + 1] - 48) as u64) * *key_rlc_mult;
                                        *key_rlc_mult *= self.acc_r;

                                        let len = row[start] as usize - 128;
                                        compute_acc_and_mult(
                                            row,
                                            key_rlc,
                                            key_rlc_mult,
                                            start + 2,
                                            len - 1, // -1 because one byte was already considered
                                        );
                                    } else {
                                        let len = row[start] as usize - 128;
                                        compute_acc_and_mult(
                                            row,
                                            key_rlc,
                                            key_rlc_mult,
                                            start + 2,
                                            len - 1, /* -1 because the first byte doesn't
                                                      * contain any key byte (it's just 32) */
                                        );
                                    }
                                };

                            // Storage leaf key
                            if row[row.len() - 1] == 2 || row[row.len() - 1] == 3 {
                                // Info whether leaf rlp is long or short.
                                assign_long_short(&mut region, witness[ind][0] == 248);

                                acc_s = F::zero();
                                acc_mult_s = F::one();
                                let len: usize;
                                if row[0] == 248 {
                                    len = (row[2] - 128) as usize + 3;
                                } else {
                                    len = (row[1] - 128) as usize + 2;
                                }
                                compute_acc_and_mult(row, &mut acc_s, &mut acc_mult_s, 0, len);

                                self.assign_acc(
                                    &mut region,
                                    acc_s,
                                    acc_mult_s,
                                    F::zero(),
                                    F::zero(),
                                    offset,
                                )?;

                                // TODO: handle if branch or extension node is added
                                let mut start = S_START - 1;
                                if row[0] == 248 {
                                    // long RLP
                                    start = S_START;
                                }

                                // For leaf S and leaf C we need to start with the same rlc.
                                let mut key_rlc_new = key_rlc;
                                let mut key_rlc_mult_new = key_rlc_mult;

                                if (is_branch_s_placeholder && row[row.len() - 1] == 2)
                                    || (is_branch_c_placeholder && row[row.len() - 1] == 3)
                                {
                                    key_rlc_new = key_rlc_prev;
                                    key_rlc_mult_new = key_rlc_mult_prev;
                                }

                                compute_key_rlc(&mut key_rlc_new, &mut key_rlc_mult_new, start);

                                region.assign_advice(
                                    || "assign key_rlc".to_string(),
                                    self.key_rlc,
                                    offset,
                                    || Ok(key_rlc_new),
                                )?;

                                // Assign previous key RLC -
                                // needed in case of placeholder branch/extension.
                                // Constraint for this is in leaf_key.
                                region.assign_advice(
                                    || "assign key_rlc".to_string(),
                                    self.sel1,
                                    offset,
                                    || Ok(key_rlc_prev),
                                )?;
                                region.assign_advice(
                                    || "assign key_rlc_mult".to_string(),
                                    self.sel2,
                                    offset,
                                    || Ok(key_rlc_mult_prev),
                                )?;
                            }

                            if row[row.len() - 1] == 13 || row[row.len() - 1] == 14 {
                                compute_acc_and_mult(
                                    row,
                                    &mut acc_s,
                                    &mut acc_mult_s,
                                    0,
                                    HASH_WIDTH + 2,
                                );

                                self.assign_acc(
                                    &mut region,
                                    acc_s,
                                    acc_mult_s,
                                    F::zero(),
                                    F::zero(),
                                    offset,
                                )?;
                            }

                            if row[row.len() - 1] == 6 {
                                // account leaf key is the same for S and C
                                acc_s = F::zero();
                                acc_mult_s = F::one();
                                // 35 = 2 (leaf rlp) + 1 (key rlp) + key_len
                                let key_len = (row[2] - 128) as usize;
                                for b in row.iter().take(3 + key_len) {
                                    acc_s += F::from(*b as u64) * acc_mult_s;
                                    acc_mult_s *= self.acc_r;
                                }
                                self.assign_acc(
                                    &mut region,
                                    acc_s,
                                    acc_mult_s,
                                    F::zero(),
                                    F::zero(),
                                    offset,
                                )?;

                                // For leaf S and leaf C we need to start with the same rlc.
                                let mut key_rlc_new = key_rlc;
                                let mut key_rlc_mult_new = key_rlc_mult;
                                compute_key_rlc(&mut key_rlc_new, &mut key_rlc_mult_new, S_START);
                                region.assign_advice(
                                    || "assign key_rlc".to_string(),
                                    self.key_rlc,
                                    offset,
                                    || Ok(key_rlc_new),
                                )?;
                            } else if row[row.len() - 1] == 7 || row[row.len() - 1] == 8 {
                                // s_rlp1, s_rlp2
                                compute_acc_and_mult(
                                    row,
                                    &mut acc_s,
                                    &mut acc_mult_s,
                                    S_START - 2,
                                    2,
                                );
                                // c_rlp1, c_rlp2
                                compute_acc_and_mult(
                                    row,
                                    &mut acc_s,
                                    &mut acc_mult_s,
                                    C_START - 2,
                                    2,
                                );
                                // nonce
                                compute_acc_and_mult(
                                    row,
                                    &mut acc_s,
                                    &mut acc_mult_s,
                                    S_START,
                                    row[S_START] as usize - 128 + 1, /* +1 for byte with length
                                                                      * info */
                                );

                                let key_len = row[S_START] as usize - 128;
                                let mut mult_diff_s = F::one();
                                for _ in 0..key_len + 4 + 1 {
                                    // + 4 because of s_rlp1, s_rlp2, c_rlp1, c_rlp2
                                    // + 1 because of byte with length info
                                    mult_diff_s *= self.acc_r;
                                }

                                // It's easier to constrain (in account_leaf_nonce_balance.rs)
                                // the multiplier if we store acc_mult both after nonce and after
                                // balance.
                                let acc_mult_tmp = acc_mult_s;
                                // balance
                                compute_acc_and_mult(
                                    row,
                                    &mut acc_s,
                                    &mut acc_mult_s,
                                    C_START,
                                    row[C_START] as usize - 128 + 1, /* +1 for byte with length
                                                                      * info */
                                );

                                let key_len = row[C_START] as usize - 128;
                                let mut mult_diff_c = F::one();
                                for _ in 0..key_len + 1 {
                                    // + 1 because of byte with length info
                                    mult_diff_c *= self.acc_r;
                                }

                                self.assign_acc(
                                    &mut region,
                                    acc_s,
                                    acc_mult_s,
                                    F::zero(),
                                    acc_mult_tmp,
                                    offset,
                                )?;

                                region.assign_advice(
                                    || "assign mult diff".to_string(),
                                    self.key_rlc,
                                    offset,
                                    || Ok(mult_diff_s),
                                )?;
                                region.assign_advice(
                                    || "assign mult diff".to_string(),
                                    self.key_rlc_mult,
                                    offset,
                                    || Ok(mult_diff_c),
                                )?;
                                if row[row.len() - 1] == 7 {
                                    acc_nonce_balance_s = acc_s;
                                    acc_mult_nonce_balance_s = acc_mult_s;
                                } else {
                                    acc_nonce_balance_c = acc_s;
                                    acc_mult_nonce_balance_c = acc_mult_s;
                                }
                            } else if row[row.len() - 1] == 9 || row[row.len() - 1] == 11 {
                                if row[row.len() - 1] == 9 {
                                    acc_s = acc_nonce_balance_s;
                                    acc_mult_s = acc_mult_nonce_balance_s;
                                } else {
                                    acc_s = acc_nonce_balance_c;
                                    acc_mult_s = acc_mult_nonce_balance_c;
                                }
                                // storage
                                compute_acc_and_mult(
                                    row,
                                    &mut acc_s,
                                    &mut acc_mult_s,
                                    S_START - 1,
                                    HASH_WIDTH + 1,
                                );
                                // code hash
                                compute_acc_and_mult(
                                    row,
                                    &mut acc_s,
                                    &mut acc_mult_s,
                                    C_START - 1,
                                    HASH_WIDTH + 1,
                                );
                                self.assign_acc(
                                    &mut region,
                                    acc_s,
                                    acc_mult_s,
                                    F::zero(),
                                    F::zero(),
                                    offset,
                                )?;
                            } else if row[row.len() - 1] == 15 && row[1] != 0 {
                                // row[1] != 0 just to avoid usize problems below (when row doesn't
                                // need to be assigned) Info whether
                                // leaf rlp is long or short.
                                assign_long_short(&mut region, witness[ind][0] == 248);

                                acc_s = F::zero();
                                acc_mult_s = F::one();
                                let len: usize;
                                if row[0] == 248 {
                                    len = (row[2] - 128) as usize + 3;
                                } else {
                                    len = (row[1] - 128) as usize + 2;
                                }
                                compute_acc_and_mult(row, &mut acc_s, &mut acc_mult_s, 0, len);

                                self.assign_acc(
                                    &mut region,
                                    acc_s,
                                    acc_mult_s,
                                    F::zero(),
                                    F::zero(),
                                    offset,
                                )?;
                            } else if row[row.len() - 1] == 16 {
                                if is_extension_node {
                                    // Intermediate RLC value and mult (after key)
                                    // to know which mult we need to use in c_advices.
                                    acc_s = F::zero();
                                    acc_mult_s = F::one();
                                    let len: usize;
                                    if row[0] == 226 {
                                        // key length is 1
                                        len = 2 // [226, key]
                                    } else {
                                        len = (row[1] - 128) as usize + 2;
                                    }
                                    compute_acc_and_mult(row, &mut acc_s, &mut acc_mult_s, 0, len);

                                    // Final RLC value.
                                    acc_c = acc_s;
                                    acc_mult_c = acc_mult_s;
                                    compute_acc_and_mult(
                                        row,
                                        &mut acc_c,
                                        &mut acc_mult_c,
                                        C_RLP_START + 1,
                                        HASH_WIDTH + 1,
                                    );

                                    self.assign_acc(
                                        &mut region,
                                        acc_s,
                                        acc_mult_s,
                                        acc_c,
                                        F::zero(),
                                        offset,
                                    )?;
                                }
                                region.assign_advice(
                                    || "assign key_rlc".to_string(),
                                    self.key_rlc,
                                    offset,
                                    || Ok(extension_node_rlc),
                                )?;
                            } else if row[row.len() - 1] == 17 {
                                if is_extension_node {
                                    // We use intermediate value from previous row (because
                                    // up to acc_s it's about key and this is the same
                                    // for both S and C).
                                    acc_c = acc_s;
                                    acc_mult_c = acc_mult_s;
                                    compute_acc_and_mult(
                                        row,
                                        &mut acc_c,
                                        &mut acc_mult_c,
                                        C_RLP_START + 1,
                                        HASH_WIDTH + 1,
                                    );

                                    self.assign_acc(
                                        &mut region,
                                        acc_s,
                                        acc_mult_s,
                                        acc_c,
                                        F::zero(),
                                        offset,
                                    )?;
                                }

                                // This sets branch Key RLC when it's not extension node (to avoid
                                // additional rotations).
                                // It sets extension node RLC otherwise.
                                region.assign_advice(
                                    || "assign key_rlc".to_string(),
                                    self.key_rlc,
                                    offset,
                                    || Ok(extension_node_rlc),
                                )?;
                            }

                            offset += 1;
                        }
                    }

                    Ok(())
                },
            )
            .ok();
    }

    pub fn load(
        &self,
        _layouter: &mut impl Layouter<F>,
        to_be_hashed: Vec<Vec<u8>>,
    ) -> Result<(), Error> {
        self.load_keccak_table(_layouter, to_be_hashed).ok();
        self.load_fixed_table(_layouter).ok();

        Ok(())
    }

    fn compute_keccak(&self, msg: &[u8]) -> Vec<u8> {
        let mut keccak = Keccak::default();
        keccak.update(msg);
        keccak.digest()
    }

    fn load_keccak_table(
        &self,
        layouter: &mut impl Layouter<F>,
        to_be_hashed: Vec<Vec<u8>>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "keccak table",
            |mut region| {
                let mut offset = 0;

                for t in to_be_hashed.iter() {
                    let hash = self.compute_keccak(t);
                    let mut rlc = F::zero();
                    let mut mult = F::one();

                    for i in t.iter() {
                        rlc += F::from(*i as u64) * mult;
                        mult *= self.acc_r;
                    }
                    region.assign_fixed(
                        || "Keccak table",
                        self.keccak_table[0],
                        offset,
                        || Ok(rlc),
                    )?;

                    let hash_rlc = hash_into_rlc(&hash, self.acc_r);
                    region.assign_fixed(
                        || "Keccak table",
                        self.keccak_table[1],
                        offset,
                        || Ok(hash_rlc),
                    )?;

                    offset += 1;
                }

                Ok(())
            },
        )
    }

    fn load_fixed_table(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_region(
            || "fixed table",
            |mut region| {
                let mut offset = 0;
                let mut mult = F::one();
                for ind in 0..(2 * HASH_WIDTH + 1) {
                    region.assign_fixed(
                        || "fixed table",
                        self.fixed_table[0],
                        offset,
                        || Ok(F::from(FixedTableTag::RMult as u64)),
                    )?;

                    region.assign_fixed(
                        || "fixed table",
                        self.fixed_table[1],
                        offset,
                        || Ok(F::from(ind as u64)),
                    )?;

                    region.assign_fixed(
                        || "fixed table",
                        self.fixed_table[2],
                        offset,
                        || Ok(mult),
                    )?;
                    mult = mult * self.acc_r;

                    offset += 1;
                }

                for ind in 0..256 {
                    region.assign_fixed(
                        || "fixed table",
                        self.fixed_table[0],
                        offset,
                        || Ok(F::from(FixedTableTag::Range256 as u64)),
                    )?;

                    region.assign_fixed(
                        || "fixed table",
                        self.fixed_table[1],
                        offset,
                        || Ok(F::from(ind as u64)),
                    )?;

                    offset += 1;
                }

                /*
                for ind in 0..(33 * 255) {
                    region.assign_fixed(
                        || "fixed table",
                        self.fixed_table[0],
                        offset,
                        || Ok(F::from(FixedTableTag::RangeKeyLen256 as u64)),
                    )?;

                    region.assign_fixed(
                        || "fixed table",
                        self.fixed_table[1],
                        offset,
                        || Ok(F::from(ind as u64)),
                    )?;

                    offset += 1;
                }
                */

                for ind in 0..16 {
                    region.assign_fixed(
                        || "fixed table",
                        self.fixed_table[0],
                        offset,
                        || Ok(F::from(FixedTableTag::Range16 as u64)),
                    )?;

                    region.assign_fixed(
                        || "fixed table",
                        self.fixed_table[1],
                        offset,
                        || Ok(F::from(ind as u64)),
                    )?;

                    offset += 1;
                }

                Ok(())
            },
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use halo2_proofs::{
        circuit::{Layouter, SimpleFloorPlanner},
        dev::{MockProver, VerifyFailure},
        plonk::{
            create_proof, keygen_pk, keygen_vk, verify_proof, Advice, Circuit, Column,
            ConstraintSystem, Error,
        },
        poly::commitment::Params,
        transcript::{Blake2bRead, Blake2bWrite, Challenge255},
    };

    use ark_std::{end_timer, rand::SeedableRng, start_timer};
    use pairing::{
        arithmetic::FieldExt,
        bn256::{Bn256, Fr as Fp},
    };
    use rand_xorshift::XorShiftRng;
    use std::{fs, marker::PhantomData};

    #[test]
    fn test_mpt() {
        #[derive(Default)]
        struct MyCircuit<F> {
            _marker: PhantomData<F>,
            witness: Vec<Vec<u8>>,
        }

        impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
            type Config = MPTConfig<F>;
            type FloorPlanner = SimpleFloorPlanner;

            fn without_witnesses(&self) -> Self {
                Self::default()
            }

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                MPTConfig::configure(meta)
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<F>,
            ) -> Result<(), Error> {
                let mut to_be_hashed = vec![];

                for row in self.witness.iter() {
                    if row[row.len() - 1] == 5 {
                        // leaves or branch RLP
                        to_be_hashed.push(row[0..row.len() - 1].to_vec());
                    }
                }

                config.load(&mut layouter, to_be_hashed)?;
                config.assign(layouter, &self.witness);

                Ok(())
            }
        }

        // for debugging:
        let path = "mpt/tests";
        // let path = "tests";
        let files = fs::read_dir(path).unwrap();
        files
            .filter_map(Result::ok)
            .filter(|d| {
                if let Some(e) = d.path().extension() {
                    e == "json"
                } else {
                    false
                }
            })
            .for_each(|f| {
                let path = f.path();
                let mut parts = path.to_str().unwrap().split("-");
                parts.next();
                let file = std::fs::File::open(path);
                let reader = std::io::BufReader::new(file.unwrap());
                let w: Vec<Vec<u8>> = serde_json::from_reader(reader).unwrap();
                let circuit = MyCircuit::<Fp> {
                    _marker: PhantomData,
                    witness: w,
                };

                let prover = MockProver::<Fp>::run(9, &circuit, vec![]).unwrap();
                assert_eq!(prover.verify(), Ok(()));

                /*
                let degree: u32 = 12;

                let rng = XorShiftRng::from_seed([
                    0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb,
                    0x37, 0x32, 0x54, 0x06, 0xbc, 0xe5,
                ]);

                // Bench setup generation
                let setup_message =
                    format!("Setup generation with degree = {}", degree);
                let start1 = start_timer!(|| setup_message);
                let general_params = Setup::<Bn256>::new(degree, rng);
                end_timer!(start1);

                let vk = keygen_vk(&general_params, &circuit).unwrap();
                let pk = keygen_pk(&general_params, vk, &circuit).unwrap();

                // Prove
                let mut transcript =
                    Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);

                // Bench proof generation time
                let proof_message =
                    format!("MPT Proof generation with 2^{} rows", degree);
                let start2 = start_timer!(|| proof_message);
                create_proof(
                    &general_params,
                    &pk,
                    &[circuit],
                    &[&[]],
                    &mut transcript,
                )
                .unwrap();
                let proof = transcript.finalize();
                end_timer!(start2);

                // Verify
                let verifier_params =
                    Setup::<Bn256>::verifier_params(&general_params, 0)
                        .unwrap();
                let mut verifier_transcript =
                    Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);

                // Bench verification time
                let start3 = start_timer!(|| "MPT Proof verification");
                verify_proof(
                    &verifier_params,
                    pk.get_vk(),
                    &[&[]],
                    &mut verifier_transcript,
                )
                .unwrap();
                end_timer!(start3);
                */
            });
    }
}
