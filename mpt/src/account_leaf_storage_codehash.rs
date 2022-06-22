use halo2_proofs::{
    circuit::Chip,
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, VirtualCells},
    poly::Rotation,
};
use pairing::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::{
    helpers::range_lookups,
    mpt::FixedTableTag,
    param::{
        ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND, ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND, BRANCH_ROWS_NUM,
        EXTENSION_ROWS_NUM, HASH_WIDTH, IS_BRANCH_C_PLACEHOLDER_POS, IS_BRANCH_S_PLACEHOLDER_POS,
        KECCAK_INPUT_WIDTH, KECCAK_OUTPUT_WIDTH, LAYOUT_OFFSET, ACCOUNT_NON_EXISTING_IND,
    },
};

#[derive(Clone, Debug)]
pub(crate) struct AccountLeafStorageCodehashConfig {}

// Verifies the hash of a leaf is in the parent branch.
pub(crate) struct AccountLeafStorageCodehashChip<F> {
    config: AccountLeafStorageCodehashConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> AccountLeafStorageCodehashChip<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        inter_root: Column<Advice>,
        q_not_first: Column<Fixed>,
        not_first_level: Column<Advice>,
        is_account_leaf_storage_codehash: Column<Advice>,
        s_rlp1: Column<Advice>,
        s_rlp2: Column<Advice>,
        c_rlp2: Column<Advice>,
        s_advices: [Column<Advice>; HASH_WIDTH],
        c_advices: [Column<Advice>; HASH_WIDTH],
        acc_r: F,
        acc: Column<Advice>,
        acc_mult: Column<Advice>,
        fixed_table: [Column<Fixed>; 3],
        s_mod_node_hash_rlc: Column<Advice>,
        c_mod_node_hash_rlc: Column<Advice>,
        sel1: Column<Advice>,
        sel2: Column<Advice>,
        keccak_table: [Column<Fixed>; KECCAK_INPUT_WIDTH + KECCAK_OUTPUT_WIDTH],
        is_storage_mod: Column<Advice>,
        is_nonce_mod: Column<Advice>,
        is_balance_mod: Column<Advice>,
        is_codehash_mod: Column<Advice>,
        is_account_delete_mod: Column<Advice>,
        is_non_existing_account_proof: Column<Advice>,
        is_s: bool,
    ) -> AccountLeafStorageCodehashConfig {
        let config = AccountLeafStorageCodehashConfig {};
        let one = Expression::Constant(F::one());

        // We don't need to check acc_mult because it's not used after this row.

        // Note: differently as in leaf_value (see empty_trie there), the placeholder
        // leaf never appears in the first level here, because there is always
        // at least a genesis account.
        meta.create_gate("account leaf storage codehash", |meta| {
            let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
            let q_enable = q_not_first.clone()
                * meta.query_advice(is_account_leaf_storage_codehash, Rotation::cur());

            let mut constraints = vec![];

            // We have storage length in s_rlp2 (which is 160 presenting 128 + 32).
            // We have storage hash in s_advices.
            // We have codehash length in c_rlp2 (which is 160 presenting 128 + 32).
            // We have codehash in c_advices.

            // Rows:
            // account leaf key
            // account leaf nonce balance S
            // account leaf nonce balance C
            // account leaf storage codeHash S
            // account leaf storage codeHash C

            let mut rot_into_non_existing = -(ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND - ACCOUNT_NON_EXISTING_IND);
            if !is_s {
                rot_into_non_existing = -(ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND - ACCOUNT_NON_EXISTING_IND);
            }

            // When non_existing_account_proof and wrong leaf, these constraints need to be checked (the wrong
            // leaf is being checked). When non_existing_account_proof and not wrong leaf (there are only branches
            // in the proof and a placeholder account leaf), these constraints are not checked. It is checked
            // that there is nil in the parent branch at the proper position (see account_non_existing), note
            // that we need (placeholder) account leaf for lookups and to know when to check that parent branch
            // has a nil.
            let is_wrong_leaf = meta.query_advice(s_rlp1, Rotation(rot_into_non_existing));
            let is_non_existing_account_proof = meta.query_advice(is_non_existing_account_proof, Rotation::cur());
            // Note: (is_non_existing_account_proof.clone() - is_wrong_leaf.clone() - one.clone())
            // cannot be 0 when is_non_existing_account_proof = 0 (see account_leaf_nonce_balance).

            let c160 = Expression::Constant(F::from(160));
            let rot = -2;
            let acc_prev = meta.query_advice(acc, Rotation(rot));
            let acc_mult_prev = meta.query_advice(acc_mult, Rotation(rot));
            let s_rlp2 = meta.query_advice(s_rlp2, Rotation::cur());
            let c_rlp2 = meta.query_advice(c_rlp2, Rotation::cur());
            constraints.push((
                "account leaf storage codehash s_rlp2",
                q_enable.clone()
                * (is_non_existing_account_proof.clone() - is_wrong_leaf.clone() - one.clone())
                * (s_rlp2.clone() - c160.clone()),
            ));
            constraints.push((
                "account leaf storage codehash c_rlp2",
                q_enable.clone()
                * (is_non_existing_account_proof.clone() - is_wrong_leaf.clone() - one.clone())
                * (c_rlp2.clone() - c160),
            ));

            let mut expr = acc_prev + s_rlp2 * acc_mult_prev.clone();

            let mut storage_root_rlc = Expression::Constant(F::zero());
            let mut curr_r = one.clone();
            for col in s_advices.iter() {
                let s = meta.query_advice(*col, Rotation::cur());
                storage_root_rlc = storage_root_rlc + s * curr_r.clone();
                curr_r = curr_r * acc_r;
            }
            let storage_root_stored = meta.query_advice(s_mod_node_hash_rlc, Rotation::cur());
            constraints.push((
                "storage root RLC",
                q_enable.clone() * (storage_root_rlc.clone() - storage_root_stored.clone()),
            ));

            expr = expr + storage_root_rlc * acc_mult_prev.clone() * acc_r;

            curr_r = curr_r * acc_mult_prev.clone() * acc_r;

            expr = expr + c_rlp2 * curr_r.clone();
            let old_curr_r = curr_r * acc_r;

            curr_r = one.clone();
            let mut codehash_rlc = Expression::Constant(F::zero());
            for col in c_advices.iter() {
                let c = meta.query_advice(*col, Rotation::cur());
                codehash_rlc = codehash_rlc + c * curr_r.clone();
                curr_r = curr_r * acc_r;
            }
            let codehash_stored = meta.query_advice(c_mod_node_hash_rlc, Rotation::cur());
            constraints.push((
                "codehash RLC",
                q_enable.clone() * (codehash_rlc.clone() - codehash_stored.clone()),
            ));

            if !is_s {
                let storage_root_s_from_prev =
                    meta.query_advice(s_mod_node_hash_rlc, Rotation::prev());
                let storage_root_s_from_cur = meta.query_advice(sel1, Rotation::cur());
                let codehash_s_from_prev = meta.query_advice(c_mod_node_hash_rlc, Rotation::prev());
                let codehash_s_from_cur = meta.query_advice(sel2, Rotation::cur());
                // We need correct previous storage root to enable lookup in storage codehash C
                // row:
                constraints.push((
                    "storage root prev RLC",
                    q_enable.clone()
                        * (storage_root_s_from_prev.clone() - storage_root_s_from_cur.clone()),
                ));
                // We need correct previous codehash to enable lookup in storage codehash C row:
                constraints.push((
                    "codehash prev RLC",
                    q_enable.clone() * (codehash_s_from_prev.clone() - codehash_s_from_cur.clone()),
                ));

                // Check there is only one modification at once:
                let is_storage_mod = meta.query_advice(is_storage_mod, Rotation::cur());
                let is_nonce_mod = meta.query_advice(is_nonce_mod, Rotation::cur());
                let is_balance_mod = meta.query_advice(is_balance_mod, Rotation::cur());
                let is_codehash_mod = meta.query_advice(is_codehash_mod, Rotation::cur());
                let is_account_delete_mod = meta.query_advice(is_account_delete_mod, Rotation::cur());

                constraints.push((
                    "if nonce / balance / codehash mod: storage_root_s = storage_root_c",
                    q_enable.clone()
                        * (is_nonce_mod.clone() + is_balance_mod.clone() + is_codehash_mod.clone())
                        * (one.clone() - is_account_delete_mod.clone())
                        * (storage_root_s_from_cur.clone() - storage_root_stored.clone()),
                ));
                constraints.push((
                    "if nonce / balance / storage mod: codehash_s = codehash_c",
                    q_enable.clone()
                        * (is_nonce_mod.clone() + is_balance_mod.clone() + is_storage_mod.clone())
                        * (one.clone() - is_account_delete_mod.clone())
                        * (codehash_s_from_cur.clone() - codehash_stored.clone()),
                ));
            }

            expr = expr + codehash_rlc * old_curr_r;

            let acc = meta.query_advice(acc, Rotation::cur());
            constraints.push(("account leaf storage codehash acc", q_enable * (expr - acc)));

            constraints
        });

        // Check hash of a leaf to be state root when leaf without branch.
        // Note 1: first level branch compared to root in branch_hash_in_parent.
        // Note 2: placeholder account leaf can appear in the first level, in this
        // case it will be positioned after placeholder branch (because there is always
        // at least a genesis account and adding a new leaf will make a branch). But in
        // this case we do not check the hash to be the same as root (the lookup does
        // not trigger because in this case account leaf is not in the first level rows)
        // - this is ok because it is only a placeholder leaf.
        meta.lookup_any(
            "account first level leaf without branch - compared to root",
            |meta| {
                let mut constraints = vec![];
                let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
                let not_first_level = meta.query_advice(not_first_level, Rotation::cur());

                let is_account_leaf_storage_codehash =
                    meta.query_advice(is_account_leaf_storage_codehash, Rotation::cur());

                let rlc = meta.query_advice(acc, Rotation::cur());
                let root = meta.query_advice(inter_root, Rotation::cur());

                constraints.push((
                    q_not_first.clone()
                        * is_account_leaf_storage_codehash.clone()
                        * (one.clone() - not_first_level.clone())
                        * rlc,
                    meta.query_fixed(keccak_table[0], Rotation::cur()),
                ));
                let keccak_table_i = meta.query_fixed(keccak_table[1], Rotation::cur());
                constraints.push((
                    q_not_first
                        * is_account_leaf_storage_codehash
                        * (one.clone() - not_first_level)
                        * root,
                    keccak_table_i,
                ));

                constraints
            },
        );

        // Check hash of a leaf.
        meta.lookup_any("account_leaf_storage_codehash: hash of a leaf", |meta| {
            let not_first_level = meta.query_advice(not_first_level, Rotation::cur());

            let is_account_leaf_storage_codehash =
                meta.query_advice(is_account_leaf_storage_codehash, Rotation::cur());

            // Placeholder leaf appears when a new account is created (and no existing leaf
            // is replaced by a branch). There are no constraints for
            // placeholder leaf except that the `modified_node`
            // in parent branch is 0.

            // Rotate into any of the brach children rows:
            let mut is_placeholder_leaf = meta.query_advice(
                sel1,
                Rotation(-ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND - EXTENSION_ROWS_NUM - 1),
            );
            if !is_s {
                is_placeholder_leaf = meta.query_advice(
                    sel2,
                    Rotation(-ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND - EXTENSION_ROWS_NUM - 1),
                );
            }

            // Rotate into branch init:
            let mut is_branch_placeholder = meta.query_advice(
                s_advices[IS_BRANCH_S_PLACEHOLDER_POS - LAYOUT_OFFSET],
                Rotation(-ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND - BRANCH_ROWS_NUM),
            );
            if !is_s {
                is_branch_placeholder = meta.query_advice(
                    s_advices[IS_BRANCH_C_PLACEHOLDER_POS - LAYOUT_OFFSET],
                    Rotation(-ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND - BRANCH_ROWS_NUM),
                );
            }

            // Note: accumulated in s (not in c) for c:
            let acc_s = meta.query_advice(acc, Rotation::cur());

            let mut constraints = vec![];
            constraints.push((
                not_first_level.clone()
                    * (one.clone() - is_branch_placeholder.clone())
                    * (one.clone() - is_placeholder_leaf.clone())
                    * is_account_leaf_storage_codehash.clone()
                    * acc_s,
                meta.query_fixed(keccak_table[0], Rotation::cur()),
            ));
            // Any rotation that lands into branch can be used instead of -17.
            let mut mod_node_hash_rlc_cur = meta.query_advice(s_mod_node_hash_rlc, Rotation(-17));
            if !is_s {
                mod_node_hash_rlc_cur = meta.query_advice(c_mod_node_hash_rlc, Rotation(-17));
            }
            let keccak_table_i = meta.query_fixed(keccak_table[1], Rotation::cur());
            constraints.push((
                not_first_level.clone()
                    * (one.clone() - is_branch_placeholder.clone())
                    * (one.clone() - is_placeholder_leaf.clone())
                    * is_account_leaf_storage_codehash.clone()
                    * mod_node_hash_rlc_cur,
                keccak_table_i.clone(),
            ));

            constraints
        });

        meta.lookup_any(
            "account_leaf_storage_codehash: hash of a leaf (branch placeholder)",
            |meta| {
                let account_not_first_level = meta.query_advice(not_first_level, Rotation::cur());
                // Any rotation that lands into branch can be used instead of -17.
                let branch_placeholder_not_in_first_level = meta.query_advice(not_first_level, Rotation(-17));

                let is_account_leaf_storage_codehash =
                    meta.query_advice(is_account_leaf_storage_codehash, Rotation::cur());

                // Note: placeholder leaf cannot appear when there is a branch placeholder
                // (placeholder leaf appears when there is no leaf at certain
                // position, while branch placeholder appears when there is a
                // leaf on the way to this some position).

                // Rotate into branch init:
                let mut is_branch_placeholder = meta.query_advice(
                    s_advices[IS_BRANCH_S_PLACEHOLDER_POS - LAYOUT_OFFSET],
                    Rotation(-ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND - BRANCH_ROWS_NUM),
                );
                if !is_s {
                    is_branch_placeholder = meta.query_advice(
                        s_advices[IS_BRANCH_C_PLACEHOLDER_POS - LAYOUT_OFFSET],
                        Rotation(-ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND - BRANCH_ROWS_NUM),
                    );
                }

                // Note: accumulated in s (not in c) for c:
                let acc_s = meta.query_advice(acc, Rotation::cur());

                let mut constraints = vec![];
                constraints.push((
                    account_not_first_level.clone()
                        * branch_placeholder_not_in_first_level.clone()
                        * is_branch_placeholder.clone()
                        * is_account_leaf_storage_codehash.clone()
                        * acc_s,
                    meta.query_fixed(keccak_table[0], Rotation::cur()),
                ));
                // Any rotation that lands into branch can be used instead of -17.
                let mut mod_node_hash_rlc_cur_prev =
                    meta.query_advice(s_mod_node_hash_rlc, Rotation(-17 - BRANCH_ROWS_NUM));
                if !is_s {
                    mod_node_hash_rlc_cur_prev =
                        meta.query_advice(c_mod_node_hash_rlc, Rotation(-17 - BRANCH_ROWS_NUM));
                }
                let keccak_table_i = meta.query_fixed(keccak_table[1], Rotation::cur());
                constraints.push((
                    account_not_first_level.clone()
                        * branch_placeholder_not_in_first_level.clone()
                        * is_branch_placeholder.clone()
                        * is_account_leaf_storage_codehash.clone()
                        * mod_node_hash_rlc_cur_prev,
                    keccak_table_i.clone(),
                ));

                constraints
            },
        );

        meta.lookup_any(
            "account_leaf_storage_codehash: hash of a leaf compared to root (branch placeholder in first level)",
            |meta| {
                let account_not_first_level = meta.query_advice(not_first_level, Rotation::cur());
                // Any rotation that lands into branch can be used instead of -17.
                let branch_placeholder_in_first_level = one.clone()
                    - meta.query_advice(not_first_level, Rotation(-17));

                let is_account_leaf_storage_codehash =
                    meta.query_advice(is_account_leaf_storage_codehash, Rotation::cur());

                // Note: placeholder leaf cannot appear when there is a branch placeholder
                // (placeholder leaf appears when there is no leaf at certain
                // position, while branch placeholder appears when there is a
                // leaf on the way to this some position).

                // Rotate into branch init:
                let mut is_branch_placeholder = meta.query_advice(
                    s_advices[IS_BRANCH_S_PLACEHOLDER_POS - LAYOUT_OFFSET],
                    Rotation(-ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND - BRANCH_ROWS_NUM),
                );
                if !is_s {
                    is_branch_placeholder = meta.query_advice(
                        s_advices[IS_BRANCH_C_PLACEHOLDER_POS - LAYOUT_OFFSET],
                        Rotation(-ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND - BRANCH_ROWS_NUM),
                    );
                }

                // Note: accumulated in s (not in c) for c:
                let acc_s = meta.query_advice(acc, Rotation::cur());

                let mut constraints = vec![];
                constraints.push((
                    account_not_first_level.clone()
                        * branch_placeholder_in_first_level.clone()
                        * is_branch_placeholder.clone()
                        * is_account_leaf_storage_codehash.clone()
                        * acc_s,
                    meta.query_fixed(keccak_table[0], Rotation::cur()),
                ));
                let root = meta.query_advice(inter_root, Rotation::cur());
                let keccak_table_i = meta.query_fixed(keccak_table[1], Rotation::cur());
                constraints.push((
                    account_not_first_level.clone()
                        * branch_placeholder_in_first_level.clone()
                        * is_branch_placeholder.clone()
                        * is_account_leaf_storage_codehash.clone()
                        * root,
                    keccak_table_i.clone(),
                ));

                constraints
            },
        );

        let sel = |meta: &mut VirtualCells<F>| {
            let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
            let q_enable = q_not_first.clone()
                * meta.query_advice(is_account_leaf_storage_codehash, Rotation::cur());

            q_enable
        };

        range_lookups(
            meta,
            sel.clone(),
            s_advices.to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );
        range_lookups(
            meta,
            sel.clone(),
            c_advices.to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );
        // s_rlp1 and c_rlp1 not used
        range_lookups(
            meta,
            sel,
            [s_rlp2, c_rlp2].to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );

        config
    }

    pub fn construct(config: AccountLeafStorageCodehashConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }
}

impl<F: FieldExt> Chip<F> for AccountLeafStorageCodehashChip<F> {
    type Config = AccountLeafStorageCodehashConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}
