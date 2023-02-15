use eth_types::Field;
use halo2_proofs::plonk::{Advice, Column, ConstraintSystem, Expression};
use halo2_proofs::{
    circuit::{Region, Value},
    plonk::{Error, VirtualCells},
    poly::Rotation,
};
use std::marker::PhantomData;

use crate::{
    circuit,
    circuit_tools::cell_manager::{Cell, DataTransition},
    circuit_tools::constraint_builder::{ConstraintBuilder, RLCable},
    mpt_circuit::{
        helpers::{get_num_bytes_short, BranchNodeInfo},
        param::{BRANCH_ROWS_NUM, S_START},
    },
    mpt_circuit::{
        helpers::{
            get_num_nibbles, get_parent_rlc_state, key_memory, parent_memory, AccountLeafInfo,
            KeyData, MPTConstraintBuilder, ParentData,
        },
        param::{KEY_LEN_IN_NIBBLES, RLP_HASH_VALUE, RLP_LIST_LONG, RLP_LONG},
        FixedTableTag,
    },
    mpt_circuit::{param::IS_ACCOUNT_DELETE_MOD_POS, MPTConfig, ProofValues},
    mpt_circuit::{
        witness_row::{MptWitnessRow, MptWitnessRowType},
        MPTContext,
    },
};

use super::{
    helpers::bytes_into_rlc,
    param::{
        ACCOUNT_LEAF_KEY_C_IND, ACCOUNT_LEAF_KEY_S_IND, ACCOUNT_LEAF_NONCE_BALANCE_C_IND,
        ACCOUNT_LEAF_NONCE_BALANCE_S_IND, ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND,
        ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND, C_START, HASH_WIDTH, IS_BALANCE_MOD_POS,
        IS_CODEHASH_MOD_POS, IS_NONCE_MOD_POS, IS_NON_EXISTING_ACCOUNT_POS,
    },
};

#[derive(Clone, Debug)]
pub(crate) struct AccountLeafCols<F> {
    pub(crate) is_key_s: Column<Advice>,
    pub(crate) is_key_c: Column<Advice>,
    pub(crate) is_non_existing: Column<Advice>,
    pub(crate) is_nonce_balance_s: Column<Advice>,
    pub(crate) is_nonce_balance_c: Column<Advice>,
    pub(crate) is_storage_codehash_s: Column<Advice>,
    pub(crate) is_storage_codehash_c: Column<Advice>,
    pub(crate) is_in_added_branch: Column<Advice>,
    _marker: PhantomData<F>,
}

impl<F: Field> AccountLeafCols<F> {
    pub(crate) fn new(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            is_key_s: meta.advice_column(),
            is_key_c: meta.advice_column(),
            is_non_existing: meta.advice_column(),
            is_nonce_balance_s: meta.advice_column(),
            is_nonce_balance_c: meta.advice_column(),
            is_storage_codehash_s: meta.advice_column(),
            is_storage_codehash_c: meta.advice_column(),
            is_in_added_branch: meta.advice_column(),
            _marker: PhantomData,
        }
    }

    pub(crate) fn is_key(&self, is_s: bool) -> Column<Advice> {
        if is_s {
            self.is_key_s
        } else {
            self.is_key_c
        }
    }

    pub(crate) fn is_nonce_balance(&self, is_s: bool) -> Column<Advice> {
        if is_s {
            self.is_nonce_balance_s
        } else {
            self.is_nonce_balance_c
        }
    }

    pub(crate) fn is_storage_codehash(&self, is_s: bool) -> Column<Advice> {
        if is_s {
            self.is_storage_codehash_s
        } else {
            self.is_storage_codehash_c
        }
    }
}

#[derive(Default, Debug)]
pub(crate) struct AccountLeaf {
    pub(crate) is_key_s: bool,
    pub(crate) is_key_c: bool,
    pub(crate) is_non_existing_account_row: bool,
    pub(crate) is_nonce_balance_s: bool,
    pub(crate) is_nonce_balance_c: bool,
    pub(crate) is_storage_codehash_s: bool,
    pub(crate) is_storage_codehash_c: bool,
    pub(crate) is_in_added_branch: bool,
}

#[derive(Clone, Debug)]
pub(crate) struct AccountLeafConfig<F> {
    key_data_s: KeyData<F>,
    key_data_c: KeyData<F>,
    key_data_w: KeyData<F>,
    key_data_d: KeyData<F>,
    parent_data_s: ParentData<F>,
    parent_data_c: ParentData<F>,
    diff_inv: Cell<F>,
}

impl<F: Field> AccountLeafConfig<F> {
    pub fn configure(
        meta: &mut VirtualCells<'_, F>,
        cb: &mut MPTConstraintBuilder<F>,
        ctx: MPTContext<F>,
    ) -> Self {
        let proof_type = ctx.proof_type;
        let not_first_level = ctx.position_cols.not_first_level;
        let s_main = ctx.s_main;
        let accs = ctx.accumulators;
        let address_rlc = ctx.address_rlc;
        let s_main = ctx.s_main;
        let c_main = ctx.c_main;
        let accs = ctx.accumulators;
        let value_prev = ctx.value_prev;
        let value = ctx.value;
        let r = ctx.r.clone();

        let mut offset = -1;

        // key rlc is in the first branch node
        let rot_parent = offset - 1;
        let rot_first_child = offset - BRANCH_ROWS_NUM + 1;
        let rot_branch_init = rot_first_child - 1;

        cb.base.cell_manager.as_mut().unwrap().reset();
        let mut ctx_key_data_s: Option<KeyData<F>> = None;
        let mut ctx_key_data_c: Option<KeyData<F>> = None;
        let mut ctx_key_data_w: Option<KeyData<F>> = None;
        let mut ctx_key_data_d: Option<KeyData<F>> = None;
        let mut ctx_parent_data_s: Option<ParentData<F>> = None;
        let mut ctx_parent_data_c: Option<ParentData<F>> = None;
        let ctx_diff_inv: Cell<F>;

        circuit!([meta, cb.base], {
            for is_s in [true, false] {
                let branch = BranchNodeInfo::new(meta, ctx.clone(), is_s, rot_branch_init);
                let account = AccountLeafInfo::new(meta, ctx.clone(), offset);

                // Account leaf always starts with RLP_LIST_LONG + 1 because its length is
                // always longer than 55 bytes due to containing two hashes -
                // storage root and codehash.
                require!(a!(s_main.rlp1, offset) => RLP_LIST_LONG + 1);

                // Calculate and store the leaf data RLC
                require!(a!(accs.acc_s.rlc, offset) => ctx.rlc(meta, 0..36, offset));

                // Load the last key values, which depends on the branch being a placeholder.
                let is_branch_placeholder = ifx! {f!(ctx.position_cols.q_not_first), a!(not_first_level) => { branch.is_placeholder() }};
                let load_offset = ifx! {is_branch_placeholder => { 1.expr() }};
                let key_data =
                    KeyData::load(&mut cb.base, &ctx.memory[key_memory(is_s)], load_offset);

                // Calculate the key RLC
                let key_rlc = key_data.rlc.expr()
                    + account.key_rlc(
                        meta,
                        &mut cb.base,
                        key_data.mult.expr(),
                        key_data.is_odd.expr(),
                        1.expr(),
                        0,
                    );
                require!(a!(accs.key.rlc, offset) => key_rlc);

                // Total number of nibbles needs to be KEY_LEN_IN_NIBBLES.
                let key_len = account.key_len(meta);
                let num_nibbles = get_num_nibbles(key_len.expr(), key_data.is_odd.expr());
                require!(key_data.num_nibbles.expr() + num_nibbles => KEY_LEN_IN_NIBBLES);

                // Key done, set the starting values
                KeyData::store(
                    &mut cb.base,
                    &ctx.memory[key_memory(is_s)],
                    KeyData::default_values(),
                );

                // Num bytes used in RLC
                let num_bytes = account.num_bytes_on_key_row(meta);
                // Update `mult_diff`
                require!((FixedTableTag::RMult, num_bytes.expr(), a!(accs.acc_s.mult, offset)) => @"fixed");
                // RLC bytes zero check
                //cb.set_length(num_bytes.expr());

                // The computed key RLC needs to be the same as the value in `address_rlc`
                // column. Note that `key_rlc` is used in `account_leaf_key_in_added_branch` and
                // in cases when there is a placeholder branch we have `key_rlc -
                // address_rlc != 0` because `key_rlc` is computed for the branch
                // that is parallel to the placeholder branch.
                ifx! {not!(is_branch_placeholder), not!(a!(proof_type.is_non_existing_account_proof, offset)) => {
                    require!(a!(address_rlc, offset) => a!(accs.key.rlc, offset));
                }}

                // Account delete
                // We need to make sure there is no leaf when account is deleted. Two possible
                // cases:
                // - 1. Account leaf is deleted and there is a nil object in
                // branch. In this case we have a placeholder leaf.
                // - 2. Account leaf is deleted from a branch with two leaves, the remaining
                // leaf moves one level up and replaces the branch. In this case we
                // have a branch placeholder. So we need to check there is a
                // placeholder branch when we have the second case. Note: we do not
                // need to cover the case when the (only) branch dissapears and only one
                // leaf remains in the trie because there will always be at least two leaves
                // (the genesis account) when account will be deleted,
                // so there will always be a branch / extension node (and thus placeholder
                // branch).
                if !is_s {
                    // Note: this constraint suffices because the proper transition from branch to a
                    // leaf (2. case) is checked by constraints in account_leaf_key_in_added_branch.
                    ifx! {a!(proof_type.is_account_delete_mod, offset) => {
                        require!(or::expr([branch.contains_placeholder_leaf(meta, is_s), branch.is_placeholder()]) => true);
                    }}
                }

                if is_s {
                    ctx_key_data_s = Some(key_data);
                } else {
                    ctx_key_data_c = Some(key_data);
                }

                offset += 1;
            }

            let rot_key_s = offset - 2;
            let rot_key_c = rot_key_s + 1;
            let rot_nonce_s = rot_key_c + 2;
            let rot_nonce_c = rot_nonce_s + 1;
            let rot_storage_s = rot_nonce_c + 1;
            let rot_storage_c = rot_storage_s + 1;
            let account = AccountLeafInfo::new(meta, ctx.clone(), rot_key_s);
            // Make sure is_wrong_leaf is boolean
            require!(account.is_wrong_leaf(meta, true) => bool);

            ifx! {a!(proof_type.is_non_existing_account_proof, offset) => {
                let key_data = KeyData::load(&mut cb.base, &ctx.memory[key_memory(true)], 1.expr());
                ifx! {account.is_wrong_leaf(meta, true) => {
                    // Calculate the key and check it's the address as requested in the lookup
                    let key_rlc_wrong = key_data.rlc.expr() + account.key_rlc(meta, &mut cb.base, key_data.mult.expr(), key_data.is_odd.expr(), 1.expr(), offset - rot_key_s);
                    require!(a!(address_rlc, offset) => key_rlc_wrong);
                    // Now make sure this address is different than the one of the leaf
                    let diff_inv = cb.base.query_cell();
                    require!((a!(address_rlc, offset) - a!(accs.key.rlc, rot_key_s)) * diff_inv.expr() => 1);
                    // Make sure the lengths of the keys are the same
                    let account_wrong = AccountLeafInfo::new(meta, ctx.clone(), offset);
                    require!(account_wrong.key_len(meta) => account.key_len(meta));
                    // RLC bytes zero check
                    let leaf = AccountLeafInfo::new(meta, ctx.clone(), offset);
                    let num_bytes = leaf.num_bytes_on_key_row(meta);
                    //cb.set_length(num_bytes);
                    ctx_diff_inv = diff_inv;
                } elsex {
                    // In case when there is no wrong leaf, we need to check there is a nil object in the parent branch.
                    require!(key_data.is_placeholder_leaf_s => true);
                }}
                ctx_key_data_w = Some(key_data);
            } elsex {
                // is_wrong_leaf needs to be false when not in non_existing_account proof
                require!(account.is_wrong_leaf(meta, true) => false);
            }};

            offset += 1;

            ifx! {f!(ctx.position_cols.q_not_first) => {
                for is_s in [true, false] {
                    let rot_key = offset - 3;
                    let rot_s = if is_s { offset } else { offset - 1 };
                    let account = AccountLeafInfo::new(meta, ctx.clone(), rot_key);

                    // The two string RLP bytes stored in the s RLP bytes.
                    // The two list RLP bytes are stored in the c RLP bytes.
                    // The RLP bytes of nonce/balance are stored bytes[0].

                    // RLC calculation for nonce/balance
                    let nonce = DataTransition::new_with_rot(meta, accs.s_mod_node_rlc, offset - 1, offset);
                    let balance = DataTransition::new_with_rot(meta, accs.c_mod_node_rlc, offset - 1, offset);
                    let mult_diff_nonce = a!(accs.acc_c.rlc, offset);
                    let mult_diff_balance = a!(accs.key.mult, offset);
                    let mut calc_rlc = |data: Expression<F>,
                                        is_long: Expression<F>,
                                        mult_diff: Expression<F>,
                                        mult_offset: u64,
                                        is_s: bool| {
                        // The is_long selector needs to be boolean
                        require!(is_long => bool);
                        // Calculate the RLC
                        let (num_bytes, value_rlc) = ifx! {is_long => {
                            let num_bytes = get_num_bytes_short::expr(a!(ctx.main(is_s).bytes[0], offset));
                            let value_rlc = ctx.main(is_s).bytes(meta, offset)[1..].to_vec().rlc(&r);
                            (num_bytes, value_rlc)
                        } elsex {
                            (1.expr(), a!(ctx.main(is_s).bytes[0], offset))
                        }};
                        require!(data => value_rlc);
                        // RLC bytes zero check (+2 because data starts at bytes[0])
                        //cb.set_length_sc(is_s, 2.expr() + num_bytes.expr());
                        // Get the correct multiplier for the length
                        require!((FixedTableTag::RMult, num_bytes.expr() + mult_offset.expr(), mult_diff) => @format!("fixed"));

                        // Go from the value rlc to the data rlc
                        let rlc = account.to_data_rlc(meta, ctx.main(is_s), value_rlc, is_long, offset);
                        (rlc, num_bytes)
                    };
                    let (nonce_rlc, nonce_num_bytes) = calc_rlc(
                        nonce.expr(),
                        account.is_nonce_long(),
                        mult_diff_nonce.expr(),
                        4,
                        true,
                    );
                    let (balance_rlc, balance_num_bytes) = calc_rlc(
                        balance.expr(),
                        account.is_balance_long(),
                        mult_diff_balance.expr(),
                        0,
                        false,
                    );

                    // Calculate and store the combined nonce + balance multipliers
                    let account_rlc = DataTransition::new_with_rot(meta, accs.acc_s.rlc, rot_key, offset);
                    let mult_prev = a!(accs.acc_s.mult, rot_key);
                    // Multipliers
                    let mult_after_nonce = a!(accs.acc_c.mult, offset);
                    let mult_diff_balance = a!(accs.key.mult, offset);
                    let acc_mult_final = a!(accs.acc_s.mult, offset);
                    require!(mult_after_nonce => mult_prev.expr() * mult_diff_nonce.expr());
                    require!(acc_mult_final => mult_after_nonce.expr() * mult_diff_balance.expr());
                    // Store the RLP bytes + nonce + balance RLC.
                    let rlc = account_rlc.prev()
                        + account.nonce_balance_rlc(
                            meta,
                            nonce_rlc.expr(),
                            balance_rlc.expr(),
                            mult_prev.expr(),
                            mult_diff_nonce.expr(),
                            offset,
                        );
                    require!(account_rlc => rlc);

                    // Check the RLP encoding consistency.
                    // RlP encoding: account = [key, [nonce, balance, storage, codehash]]
                    // The only exception is when `is_non_existing_account_proof = 1` &
                    // `is_wrong_leaf = 0`. In this case the value does not matter as
                    // the account leaf is only a placeholder and does not use
                    // `s_main.rlp1` and `s_main.rlp2`.
                    //  TODO(Brecht): Can we remove this if by just making this pass in this special
                    // case?
                    ifx! {not!(and::expr(&[a!(proof_type.is_non_existing_account_proof, offset), not!(account.is_wrong_leaf(meta, is_s))])) => {
                        // We always store between 55 and 256 bytes of data in the values list.
                        require!(a!(s_main.rlp1, offset) => RLP_LONG + 1);
                        // The RLP encoded list always has 2 RLP bytes (the c RLP bytes).
                        require!(a!(s_main.rlp2, offset) => a!(c_main.rlp2, offset) + 2.expr());
                        // `c_main.rlp1` always needs to be RLP_LIST_LONG + 1.
                        require!(a!(c_main.rlp1, offset) => RLP_LIST_LONG + 1);
                        // The length of the list is `#(nonce bytes) + #(balance bytes) + 2 * (1 + #(hash))`.
                        require!(a!(c_main.rlp2, offset) => nonce_num_bytes.expr() + balance_num_bytes.expr() + (2 * (1 + 32)).expr());
                        // Now check that the the key and value list length matches the account length.
                        let len = account.num_bytes(meta);
                        let key_num_bytes = account.num_bytes_on_key_row(meta);
                        // The RLP encoded string always has 2 RLP bytes (the s RLP bytes).
                        let value_list_num_bytes = a!(s_main.rlp2, offset) + 2.expr();
                        // Account length needs to equal all key bytes and all values list bytes.
                        require!(len => key_num_bytes + value_list_num_bytes);
                    }}

                    // To enable lookups we need to have the previous/current nonce/balance on the
                    // same row
                    if !is_s {
                        require!(a!(value_prev, rot_s) => nonce.prev());
                        require!(a!(value, rot_s) => nonce);
                        require!(a!(value_prev, offset) => balance.prev());
                        require!(a!(value, offset) => balance);
                    }

                    // Check that there is only one modification.
                    if !is_s {
                        // Note: For `is_non_existing_account_proof` we do not need this constraint,
                        // `S` and `C` proofs are the same and we need to do a lookup into only one
                        // (the other one could really be whatever).
                        ifx! {not!(a!(proof_type.is_account_delete_mod, offset)) => {
                            // Nonce needs to remain the same when not modifying the nonce
                            ifx!{not!(a!(proof_type.is_nonce_mod, offset)) => {
                                require!(nonce => nonce.prev());
                            }}
                            // Balance needs to remain the same when not modifying the balance
                            ifx!{not!(a!(proof_type.is_balance_mod, offset)) => {
                                require!(balance => balance.prev());
                            }}
                        }}
                    }

                    offset += 1;
                }

                for is_s in [true, false] {
                    let rot_key = offset - 5;
                    let rot_nonce_balance = offset - 2;
                    let rot_s = if is_s { offset } else { offset - 1 };
                    // rlp1 is not used, rlp2 is used to store the first RLP byte.
                    let account = AccountLeafInfo::new(meta, ctx.clone(), rot_key);

                    // When non_existing_account_proof and not wrong leaf there is only a placeholder account leaf
                    // and the constraints in this gate are not triggered. In that case it is checked
                    // that there is nil in the parent branch at the proper position (see `account_non_existing.rs`), note
                    // that we need (placeholder) account leaf for lookups and to know when to check that parent branch
                    // has a nil.
                    // TODO(Brecht): Can we remove this if by just making this pass in this special case?
                    ifx! {not!(and::expr(&[a!(proof_type.is_non_existing_account_proof, offset), not!(account.is_wrong_leaf(meta, is_s))])) => {
                        // Storage root and codehash are always 32-byte hashes.
                        require!(a!(s_main.rlp2, offset) => RLP_HASH_VALUE);
                        require!(a!(c_main.rlp2, offset) => RLP_HASH_VALUE);
                    }}

                    // RLC calculation
                    let account_rlc = DataTransition::new_with_rot(meta, accs.acc_s.rlc, rot_nonce_balance, offset);
                    let mult_prev = a!(accs.acc_s.mult, rot_nonce_balance);
                    // - Storage root
                    let storage_root = DataTransition::new_with_rot(meta, accs.s_mod_node_rlc, offset - 1, offset);
                    require!(storage_root => s_main.bytes(meta, offset).rlc(&r));
                    // - Codehash
                    let codehash = DataTransition::new_with_rot(meta, accs.c_mod_node_rlc, offset - 1, offset);
                    require!(codehash => c_main.bytes(meta, offset).rlc(&r));
                    // The full account leaf RLC
                    let rlc = account_rlc.prev() + account.storage_codehash_rlc(meta, storage_root.expr(), codehash.expr(), mult_prev.expr(), offset);
                    require!(account_rlc => rlc);

                    // Check if the account is in its parent.
                    let branch = BranchNodeInfo::new(meta, ctx.clone(), is_s, rot_branch_init);
                    let parent_data = ParentData::load("storage load", &mut cb.base, &ctx.memory[parent_memory(is_s)], 0.expr());
                    // Check is skipped for placeholder leafs which are dummy leafs
                    ifx!{not!(and::expr(&[a!(ctx.position_cols.not_first_level, offset), not!(branch.is_placeholder()), branch.contains_placeholder_leaf(meta, is_s)])) => {
                        let account = AccountLeafInfo::new(meta, ctx.clone(), rot_key);
                        require!((1, account_rlc, account.num_bytes(meta), parent_data.rlc) => @"keccak");
                    }}
                    // Store the new parent
                    ParentData::store(&mut cb.base, &ctx.memory[parent_memory(is_s)], [storage_root.expr(), true.expr()]);
                    if is_s {
                        ctx_parent_data_s = Some(parent_data);
                    } else {
                        ctx_parent_data_c = Some(parent_data);
                    }

                    if !is_s {
                        // To enable lookups we need to have the previous/current storage root/code hash on the same row.
                        require!(a!(value_prev, rot_s) => storage_root.prev());
                        require!(a!(value, rot_s) => storage_root);
                        require!(a!(value_prev, offset) => codehash.prev());
                        require!(a!(value, offset) => codehash);

                        // Check that there is only one modification (except when the account is being deleted).
                        ifx!{not!(a!(proof_type.is_account_delete_mod, offset)) => {
                            // Storage root needs to remain the same when not modifying the storage root
                            ifx!{not!(a!(proof_type.is_storage_mod, offset)) => {
                                require!(storage_root => storage_root.prev());
                            }}
                            // Codehash root needs to remain the same when not modifying the codehash
                            ifx!{not!(a!(proof_type.is_codehash_mod, offset)) => {
                                require!(codehash => codehash.prev());
                            }}
                        }}
                    }

                    offset += 1;
                }

                ifx! {a!(ctx.position_cols.not_first_level) => {
                    let branch = BranchNodeInfo::new(meta, ctx.clone(), true, rot_branch_init);
                    let drifted_account = AccountLeafInfo::new(meta, ctx.clone(), offset);

                    // A drifted leaf appears only when there is a placeholder branch
                    ifx! {branch.is_placeholder_s_or_c() => {
                        // Calculate and store the leaf RLC (RLP + key)
                        let drifted_rlc = a!(accs.acc_s.rlc, offset);
                        require!(drifted_rlc => ctx.rlc(meta, 0..36, offset));

                        // `s_rlp1` is always RLP_LIST_LONG + 1 because the account leaf is always > 55 bytes (and < 256)
                        require!(a!(s_main.rlp1, offset) => RLP_LIST_LONG + 1);

                        // The key RLC of the drifted leaf needs to be the same as the key RLC of the leaf before
                        // the drift - the nibbles are the same in both cases, the difference is that before the
                        // drift some nibbles are stored in the leaf key, while after the drift these nibbles are used as
                        // position in a branch or/and nibbles of the extension node.
                        let is_branch_in_first_level = not!(a!(not_first_level, rot_branch_init));
                        let (key_rlc_prev, key_mult_prev) = get_parent_rlc_state(meta, ctx.clone(), is_branch_in_first_level, rot_parent);

                        // Load the last key values
                        let key_data = KeyData::load(&mut cb.base, &ctx.memory[key_memory(true)], 2.expr());

                        // TODO(Brecht): make this work with loaded key data when extension node is separate
                        ifx! {not!(branch.is_extension()) => {
                            require!(key_data.rlc => key_rlc_prev);
                            require!(key_data.mult => key_mult_prev);
                        }}

                        // Calculate the drifted key RLC
                        let drifted_key_rlc = key_rlc_prev +
                            branch.drifted_nibble_rlc(meta, &mut cb.base, key_mult_prev.expr()) +
                            drifted_account.key_rlc(meta, &mut cb.base, key_mult_prev.expr(), branch.is_key_odd(), r[0].expr(), 0);

                        // RLC bytes zero check
                        let num_bytes = drifted_account.num_bytes_on_key_row(meta);
                        cb.set_length(num_bytes.expr());
                        // Update `mult_diff`
                        let mult = a!(accs.acc_s.mult, offset);
                        require!((FixedTableTag::RMult, num_bytes.expr(), mult) => @"mult");

                        // Check that the drifted leaf is unchanged and is stored at `drifted_index`.
                        let calc_rlc = |is_s, meta: &mut VirtualCells<'_, F>, cb: &mut ConstraintBuilder<F>| {
                            circuit!([meta, cb], {
                                let rot_key = if is_s { rot_key_s } else { rot_key_c };
                                let rot_nonce = if is_s { rot_nonce_s } else { rot_nonce_c };
                                let rot_storage = if is_s { rot_storage_s } else { rot_storage_c };

                                let account = AccountLeafInfo::new(meta, ctx.clone(), rot_key);

                                // Calculate the drifted leaf rlc
                                // Nonce data rlc
                                let nonce_stored = a!(accs.s_mod_node_rlc, rot_nonce);
                                let nonce_rlc = account.to_data_rlc(meta, ctx.s_main, nonce_stored, account.is_nonce_long(), rot_nonce);
                                // Balance data rlc
                                let balance_stored = a!(accs.c_mod_node_rlc, rot_nonce);
                                let balance_rlc = account.to_data_rlc(meta, ctx.c_main, balance_stored, account.is_balance_long(), rot_nonce);
                                let mult_nonce = a!(accs.acc_c.rlc, rot_nonce);
                                let mult_balance = a!(accs.key.mult, rot_nonce);
                                let rlc = drifted_rlc.expr() + account.nonce_balance_rlc(meta, nonce_rlc.expr(), balance_rlc.expr(), mult.expr(), mult_nonce.expr(), rot_nonce);
                                // Add storage/codehash rlc
                                let storage_rlc = a!(accs.s_mod_node_rlc, rot_storage);
                                let codehash_rlc = a!(accs.c_mod_node_rlc, rot_storage);
                                let mult_prev = mult.expr() * mult_nonce.expr() * mult_balance.expr();
                                let rlc = rlc + account.storage_codehash_rlc(meta, storage_rlc.expr(), codehash_rlc.expr(), mult_prev.expr(), rot_storage);

                                (true.expr(), a!(accs.key.rlc, rot_key), rlc, a!(accs.mod_node_rlc(is_s), rot_first_child))
                            })
                        };
                        let (do_checks, key_rlc, drifted_rlc, mod_hash) = matchx! {
                            branch.is_placeholder_s() => {
                                // Neighbour leaf in the added branch
                                // - `leaf_key_s_rlc` is the key RLC of the leaf before it drifted down
                                // in a new branch.
                                // - `s_mod_node_rlc` in the placeholder branch stores the hash of a neighbour leaf.
                                // This is because `c_mod_node_rlc` in the added branch stores the hash of
                                // `modified_index` (the leaf that has been added).
                                calc_rlc(true, meta, &mut cb.base)
                            },
                            branch.is_placeholder_c() => {
                                // Neighbour leaf in the deleted branch
                                // -`leaf_key_c_rlc` is the key RLC of the leaf after its neighbour leaf
                                // has been deleted (and there were only two leaves, so the branch was deleted).
                                // - `c_mod_node_hash_rlc` in the placeholder branch stores the hash of a neighbour leaf.
                                // This is because `s_mod_node_rlc` in the deleted branch stores the hash of
                                // `modified_index` (the leaf that is to be deleted).
                                calc_rlc(false, meta, &mut cb.base)
                            },
                            _ => (false.expr(), 0.expr(), 0.expr(), 0.expr()),
                        };
                        ifx! {do_checks => {
                            // The key of the drifted leaf needs to match the key of the leaf
                            require!(key_rlc => drifted_key_rlc);
                            // The drifted leaf needs to be stored in the branch at `drifted_index`.
                            require!((1, drifted_rlc, drifted_account.num_bytes(meta), mod_hash) => @"keccak");
                        }}
                        ctx_key_data_d = Some(key_data);
                    }}
                }}
            }}
        });

        AccountLeafConfig {
            key_data_s: ctx_key_data_s.unwrap(),
            key_data_c: ctx_key_data_c.unwrap(),
            key_data_w: ctx_key_data_w.unwrap(),
            key_data_d: ctx_key_data_d.unwrap(),
            parent_data_s: ctx_parent_data_s.unwrap(),
            parent_data_c: ctx_parent_data_c.unwrap(),
            diff_inv: ctx_diff_inv,
        }
    }

    pub fn assign(
        &self,
        region: &mut Region<'_, F>,
        mpt_config: &MPTConfig<F>,
        witness: &[MptWitnessRow<F>],
        pv: &mut ProofValues<F>,
        offset: usize,
    ) -> Result<(), Error> {
        let base_offset = offset;
        let mut offset = offset - 1;

        /* KEY */

        for is_s in [true, false] {
            let row = &witness[offset];

            // account leaf key S & C
            let mut acc = F::zero();
            let mut acc_mult = F::one();
            // 35 = 2 (leaf rlp) + 1 (key rlp) + key_len
            let key_len = (row.get_byte(2) - 128) as usize;
            for b in row.bytes.iter().take(3 + key_len) {
                acc += F::from(*b as u64) * acc_mult;
                acc_mult *= mpt_config.randomness;
            }

            if row.get_type() == MptWitnessRowType::AccountLeafKeyS {
                pv.acc_account_s = acc;
                pv.acc_mult_account_s = acc_mult;

                if row.get_byte_rev(IS_ACCOUNT_DELETE_MOD_POS) == 1 {
                    region.assign_advice(
                        || "assign lookup enabled".to_string(),
                        mpt_config.proof_type.proof_type,
                        offset,
                        || Value::known(F::from(5_u64)), /* account delete mod lookup enabled in
                                                          * this row if it is is_account_delete
                                                          * proof */
                    )?;
                }
            } else {
                pv.acc_account_c = acc;
                pv.acc_mult_account_c = acc_mult;
            }

            let is_branch_placeholder = if is_s {
                pv.is_branch_s_placeholder
            } else {
                pv.is_branch_c_placeholder
            };
            let load_offset = if is_branch_placeholder { 1 } else { 0 };
            let key_data = if is_s {
                &self.key_data_s
            } else {
                &self.key_data_c
            };
            key_data.witness_load(
                region,
                base_offset,
                &mut pv.memory[key_memory(is_s)],
                load_offset,
            )?;
            key_data.witness_store(
                region,
                base_offset,
                &mut pv.memory[key_memory(is_s)],
                F::zero(),
                F::one(),
                0,
                false,
                false,
            )?;

            // For leaf S and leaf C we need to start with the same rlc.
            let mut key_rlc_new = pv.key_rlc;
            let mut key_rlc_mult_new = pv.key_rlc_mult;
            if (pv.is_branch_s_placeholder && row.get_type() == MptWitnessRowType::AccountLeafKeyS)
                || (pv.is_branch_c_placeholder
                    && row.get_type() == MptWitnessRowType::AccountLeafKeyC)
            {
                key_rlc_new = pv.key_rlc_prev;
                key_rlc_mult_new = pv.key_rlc_mult_prev;
            }

            mpt_config.compute_key_rlc(
                &row.bytes,
                &mut key_rlc_new,
                &mut key_rlc_mult_new,
                S_START,
            );
            pv.account_key_rlc = key_rlc_new;
            region.assign_advice(
                || "assign key_rlc".to_string(),
                mpt_config.accumulators.key.rlc,
                offset,
                || Value::known(key_rlc_new),
            )?;

            mpt_config
                .assign_acc(region, acc, acc_mult, F::zero(), F::zero(), offset)
                .ok();

            offset += 1;
        }

        /* NON_EXISTING */
        {
            self.key_data_w
                .witness_load(region, base_offset, &mut pv.memory[key_memory(true)], 1)
                .ok();

            let row = &witness[offset];
            let address_rlc = bytes_into_rlc(row.address_bytes(), mpt_config.randomness);
            let diff_inv = (address_rlc - pv.account_key_rlc)
                .invert()
                .unwrap_or(F::zero());
            self.diff_inv.assign(region, base_offset, diff_inv).ok();

            if row.get_byte_rev(IS_NON_EXISTING_ACCOUNT_POS) == 1 {
                region
                    .assign_advice(
                        || "assign lookup enabled".to_string(),
                        mpt_config.proof_type.proof_type,
                        offset,
                        || Value::known(F::from(4_u64)), /* non existing account lookup enabled
                                                          * in
                                                          * this row if it is
                                                          * non_existing_account
                                                          * proof */
                    )
                    .ok();
            }
        }

        offset += 1;

        /* NONCE/BALANCE */

        for is_s in [true, false] {
            let row = &witness[offset];

            let mut nonce_len: usize = 1;
            // Note: when nonce or balance is 0, the actual value stored in RLP encoding is
            // 128.
            if row.get_byte(S_START) > 128 {
                nonce_len = row.get_byte(S_START) as usize - 128 + 1; // +1 for byte with length info
                region
                    .assign_advice(
                        || "assign sel1".to_string(),
                        mpt_config.denoter.sel1,
                        offset
                            - (ACCOUNT_LEAF_NONCE_BALANCE_S_IND - ACCOUNT_LEAF_KEY_S_IND) as usize,
                        || Value::known(F::one()),
                    )
                    .ok();
            } else {
                region
                    .assign_advice(
                        || "assign sel1".to_string(),
                        mpt_config.denoter.sel1,
                        offset
                            - (ACCOUNT_LEAF_NONCE_BALANCE_C_IND - ACCOUNT_LEAF_KEY_C_IND) as usize,
                        || Value::known(F::zero()),
                    )
                    .ok();
            }

            let mut balance_len: usize = 1;
            if row.get_byte(C_START) > 128 {
                balance_len = row.get_byte(C_START) as usize - 128 + 1; // +1 for byte with length info
                region
                    .assign_advice(
                        || "assign sel2".to_string(),
                        mpt_config.denoter.sel2,
                        offset
                            - (ACCOUNT_LEAF_NONCE_BALANCE_S_IND - ACCOUNT_LEAF_KEY_S_IND) as usize,
                        || Value::known(F::one()),
                    )
                    .ok();
            } else {
                region
                    .assign_advice(
                        || "assign sel2".to_string(),
                        mpt_config.denoter.sel2,
                        offset
                            - (ACCOUNT_LEAF_NONCE_BALANCE_C_IND - ACCOUNT_LEAF_KEY_C_IND) as usize,
                        || Value::known(F::zero()),
                    )
                    .ok();
            }

            // nonce value RLC and balance value RLC:
            pv.rlc1 = F::zero();
            pv.rlc2 = F::zero();
            // Note: Below, it first computes and assigns the nonce RLC and balance RLC
            // without RLP specific byte (there is a RLP specific byte when
            // nonce/balance RLP length > 1).
            if nonce_len == 1 && balance_len == 1 {
                mpt_config
                    .compute_rlc_and_assign(
                        region,
                        &row.bytes,
                        pv,
                        offset,
                        (S_START, HASH_WIDTH),
                        (C_START, HASH_WIDTH),
                    )
                    .ok();
            } else if nonce_len > 1 && balance_len == 1 {
                mpt_config
                    .compute_rlc_and_assign(
                        region,
                        &row.bytes,
                        pv,
                        offset,
                        (S_START + 1, HASH_WIDTH - 1),
                        (C_START, HASH_WIDTH),
                    )
                    .ok();
            } else if nonce_len == 1 && balance_len > 1 {
                mpt_config
                    .compute_rlc_and_assign(
                        region,
                        &row.bytes,
                        pv,
                        offset,
                        (S_START, HASH_WIDTH),
                        (C_START + 1, HASH_WIDTH - 1),
                    )
                    .ok();
            } else if nonce_len > 1 && balance_len > 1 {
                mpt_config
                    .compute_rlc_and_assign(
                        region,
                        &row.bytes,
                        pv,
                        offset,
                        (S_START + 1, HASH_WIDTH - 1),
                        (C_START + 1, HASH_WIDTH - 1),
                    )
                    .ok();
            }

            let mut acc_account;
            let mut acc_mult_account;
            if row.get_type() == MptWitnessRowType::AccountLeafNonceBalanceS {
                pv.nonce_value_s = pv.rlc1;
                pv.balance_value_s = pv.rlc2;

                acc_account = pv.acc_account_s;
                acc_mult_account = pv.acc_mult_account_s;

                if row.get_byte_rev(IS_NONCE_MOD_POS) == 1 {
                    region
                        .assign_advice(
                            || "assign which lookup type enabled".to_string(),
                            mpt_config.proof_type.proof_type,
                            offset,
                            || Value::known(F::from(1_u64)),
                        )
                        .ok();
                }
            } else {
                acc_account = pv.acc_account_c;
                acc_mult_account = pv.acc_mult_account_c;

                let nonce_value_c = pv.rlc1;
                let balance_value_c = pv.rlc2;

                if row.get_byte_rev(IS_BALANCE_MOD_POS) == 1 {
                    region
                        .assign_advice(
                            || "assign which lookup type enabled".to_string(),
                            mpt_config.proof_type.proof_type,
                            offset,
                            || Value::known(F::from(2_u64)),
                        )
                        .ok();
                }

                let offset_s = offset
                    - (ACCOUNT_LEAF_NONCE_BALANCE_C_IND - ACCOUNT_LEAF_NONCE_BALANCE_S_IND)
                        as usize;

                // assign nonce S RLC in ACCOUNT_LEAF_NONCE_BALANCE_S row.
                region
                    .assign_advice(
                        || "assign nonce S".to_string(),
                        mpt_config.value_prev,
                        offset_s,
                        || Value::known(pv.nonce_value_s),
                    )
                    .ok();

                // Assign nonce C RLC in ACCOUNT_LEAF_NONCE_BALANCE_S row.
                region
                    .assign_advice(
                        || "assign nonce C".to_string(),
                        mpt_config.value,
                        offset_s,
                        || Value::known(nonce_value_c),
                    )
                    .ok();

                // assign balance S RLC in ACCOUNT_LEAF_NONCE_BALANCE_C row.
                region
                    .assign_advice(
                        || "assign value_prev".to_string(),
                        mpt_config.value_prev,
                        offset,
                        || Value::known(pv.balance_value_s),
                    )
                    .ok();

                // Assign balance C RLC in ACCOUNT_LEAF_NONCE_BALANCE_C row.
                region
                    .assign_advice(
                        || "assign balance C".to_string(),
                        mpt_config.value,
                        offset,
                        || Value::known(balance_value_c),
                    )
                    .ok();
            }

            // s_rlp1, s_rlp2
            mpt_config.compute_acc_and_mult(
                &row.bytes,
                &mut acc_account,
                &mut acc_mult_account,
                S_START - 2,
                2,
            );
            // c_rlp1, c_rlp2
            mpt_config.compute_acc_and_mult(
                &row.bytes,
                &mut acc_account,
                &mut acc_mult_account,
                C_START - 2,
                2,
            );
            // nonce contribution to leaf RLC:
            /*
            If nonce stream length is 1, it doesn't have
            the first byte with length info. Same for balance.
            There are four possibilities:
                - nonce is short (length 1), balance is short (length 1)
                - nonce is short, balance is long
                - nonce is long, balance is short
                - nonce is long, balance is long
            We put this info in sel1/sel2 in the key row (sel1/sel2 are
                already used for other purposes in nonce balance row):
                - sel1/sel2: 0/0 (how to check: (1-sel1)*(1-sel2))
                - sel1/sel2: 0/1 (how to check: (1-sel1)*sel2)
                - sel1/sel2: 1/0 (how to check: sel1*(1-sel2))
                - sel1/sel2: 1/1 (how to check: sel1*sel2)
            */

            mpt_config.compute_acc_and_mult(
                &row.bytes,
                &mut acc_account,
                &mut acc_mult_account,
                S_START,
                nonce_len,
            );

            let mut mult_diff_s = F::one();
            for _ in 0..nonce_len + 4 {
                // + 4 because of s_rlp1, s_rlp2, c_rlp1, c_rlp2
                mult_diff_s *= mpt_config.randomness;
            }

            // It's easier to constrain (in account_leaf_nonce_balance.rs)
            // the multiplier if we store acc_mult both after nonce and after
            // balance.
            let acc_mult_tmp = acc_mult_account;

            // balance contribution to leaf RLC
            mpt_config.compute_acc_and_mult(
                &row.bytes,
                &mut acc_account,
                &mut acc_mult_account,
                C_START,
                balance_len,
            );

            let mut mult_diff_c = F::one();
            for _ in 0..balance_len {
                mult_diff_c *= mpt_config.randomness;
            }

            mpt_config
                .assign_acc(
                    region,
                    acc_account,
                    acc_mult_account,
                    F::zero(),
                    acc_mult_tmp,
                    offset,
                )
                .ok();

            region
                .assign_advice(
                    || "assign mult diff".to_string(),
                    mpt_config.accumulators.acc_c.rlc, /* assigning key_rlc leads into
                                                        * PoisonedConstraint */
                    offset,
                    || Value::known(mult_diff_s),
                )
                .ok();
            region
                .assign_advice(
                    || "assign mult diff".to_string(),
                    mpt_config.accumulators.key.mult,
                    offset,
                    || Value::known(mult_diff_c),
                )
                .ok();
            if row.get_type() == MptWitnessRowType::AccountLeafNonceBalanceS {
                pv.acc_nonce_balance_s = acc_account;
                pv.acc_mult_nonce_balance_s = acc_mult_account;
            } else {
                pv.acc_nonce_balance_c = acc_account;
                pv.acc_mult_nonce_balance_c = acc_mult_account;
            }

            offset += 1;
        }

        /* STORAGE/CODEHASH */

        for is_s in [true, false] {
            let row = &witness[offset];

            if is_s {
                pv.acc_s = pv.acc_nonce_balance_s;
                pv.acc_mult_s = pv.acc_mult_nonce_balance_s;

                // storage root RLC and code hash RLC
                pv.rlc1 = F::zero();
                pv.rlc2 = F::zero();
                mpt_config
                    .compute_rlc_and_assign(
                        region,
                        &row.bytes,
                        pv,
                        offset,
                        (S_START, HASH_WIDTH),
                        (C_START, HASH_WIDTH),
                    )
                    .ok();
                pv.storage_root_value_s = pv.rlc1;
                pv.codehash_value_s = pv.rlc2;
            } else {
                pv.acc_s = pv.acc_nonce_balance_c;
                pv.acc_mult_s = pv.acc_mult_nonce_balance_c;

                // assign storage root RLC and code hash RLC for this row
                pv.rlc1 = F::zero();
                pv.rlc2 = F::zero();
                mpt_config
                    .compute_rlc_and_assign(
                        region,
                        &row.bytes,
                        pv,
                        offset,
                        (S_START, HASH_WIDTH),
                        (C_START, HASH_WIDTH),
                    )
                    .ok();

                let storage_root_value_c = pv.rlc1;
                let codehash_value_c = pv.rlc2;

                pv.storage_root_value_c = storage_root_value_c;

                if row.get_byte_rev(IS_CODEHASH_MOD_POS) == 1 {
                    region
                        .assign_advice(
                            || "assign lookup enabled".to_string(),
                            mpt_config.proof_type.proof_type,
                            offset,
                            || Value::known(F::from(3_u64)), /* codehash mod lookup enabled in
                                                              * this row if it is
                                                              * is_codehash_mod proof */
                        )
                        .ok();
                }

                let offset_s = offset
                    - (ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND - ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND)
                        as usize;

                // Assign storage root S
                region
                    .assign_advice(
                        || "assign storage root S".to_string(),
                        mpt_config.value_prev,
                        offset_s,
                        || Value::known(pv.storage_root_value_s),
                    )
                    .ok();

                // Assign storage root C
                region
                    .assign_advice(
                        || "assign code hash C".to_string(),
                        mpt_config.value,
                        offset_s,
                        || Value::known(storage_root_value_c),
                    )
                    .ok();

                // Assign code hash S
                region
                    .assign_advice(
                        || "assign code hash S".to_string(),
                        mpt_config.value_prev,
                        offset,
                        || Value::known(pv.codehash_value_s),
                    )
                    .ok();

                // Assign code hash C
                region
                    .assign_advice(
                        || "assign code hash C".to_string(),
                        mpt_config.value,
                        offset,
                        || Value::known(codehash_value_c),
                    )
                    .ok();
            }

            let storage_root = if is_s {
                pv.storage_root_value_s
            } else {
                pv.storage_root_value_c
            };
            let parent_data = if is_s {
                &self.parent_data_s
            } else {
                &self.parent_data_c
            };
            parent_data
                .witness_load(region, base_offset, &mut pv.memory[parent_memory(is_s)], 0)
                .ok();
            parent_data
                .witness_store(
                    region,
                    base_offset,
                    &mut pv.memory[parent_memory(is_s)],
                    storage_root,
                    true,
                )
                .ok();

            // storage
            mpt_config.compute_acc_and_mult(
                &row.bytes,
                &mut pv.acc_s,
                &mut pv.acc_mult_s,
                S_START - 1,
                HASH_WIDTH + 1,
            );
            // code hash
            mpt_config.compute_acc_and_mult(
                &row.bytes,
                &mut pv.acc_s,
                &mut pv.acc_mult_s,
                C_START - 1,
                HASH_WIDTH + 1,
            );
            mpt_config
                .assign_acc(
                    region,
                    pv.acc_s,
                    pv.acc_mult_s,
                    F::zero(),
                    F::zero(),
                    offset,
                )
                .ok();

            offset += 1;
        }

        /* DRIFTED */

        let row = &witness[offset];
        if row.get_byte(1) != 0 {
            pv.acc_s = F::zero();
            pv.acc_mult_s = F::one();
            let len = (row.bytes[2] - 128) as usize + 3;
            mpt_config.compute_acc_and_mult(&row.bytes, &mut pv.acc_s, &mut pv.acc_mult_s, 0, len);

            self.key_data_d
                .witness_load(region, base_offset, &mut pv.memory[key_memory(true)], 2)
                .ok();

            mpt_config
                .assign_acc(
                    region,
                    pv.acc_s,
                    pv.acc_mult_s,
                    F::zero(),
                    F::zero(),
                    offset,
                )
                .ok();
        }

        Ok(())
    }
}
