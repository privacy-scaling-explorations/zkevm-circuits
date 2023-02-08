use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Region, Value},
    plonk::{Error, VirtualCells},
    poly::Rotation,
};

use crate::{
    circuit,
    circuit_tools::{CellManager, DataTransition, RLCable, RLCChainable, ConstraintBuilder, CellType, Cell},
    mpt_circuit::{
        helpers::BranchNodeInfo,
        param::{BRANCH_ROWS_NUM, S_START},
    },
    mpt_circuit::{
        helpers::{KeyData, MPTConstraintBuilder, StorageLeafInfo, get_num_bytes_short, ParentData, parent_memory, get_parent_rlc_state, key_memory},
        param::{KEY_LEN_IN_NIBBLES, EMPTY_TRIE_HASH, HASH_WIDTH, IS_STORAGE_MOD_POS, LEAF_NON_EXISTING_IND, LEAF_KEY_C_IND, IS_NON_EXISTING_STORAGE_POS},
        FixedTableTag,
    },
    mpt_circuit::{
        witness_row::{MptWitnessRow, MptWitnessRowType},
        MPTContext,
    },
    mpt_circuit::{MPTConfig, ProofValues},
};

#[derive(Clone, Debug)]
pub(crate) struct LeafCombinedConfig<F> {
    key_data_s: KeyData<F>,
    key_data_c: KeyData<F>,
    key_data_w: KeyData<F>,
    parent_data_s: ParentData<F>,
    parent_data_c: ParentData<F>,
    diff_inv: Cell<F>,
}

impl<F: FieldExt> LeafCombinedConfig<F> {
    pub fn configure(
        meta: &mut VirtualCells<'_, F>,
        cb: &mut MPTConstraintBuilder<F>,
        ctx: MPTContext<F>,
    ) -> Self {
        let is_s = true;
        let accs = ctx.accumulators;
        let value_prev = ctx.value_prev;
        let value = ctx.value;
        let s_main = ctx.s_main;
        let r = ctx.r.clone();

        let rot_parent = -1;
        let rot_branch_init = rot_parent - (BRANCH_ROWS_NUM - 1);
        let rot_branch_child = rot_branch_init + 1;

        let rot_key_s = 0;
        let rot_value_s = 1;
        let rot_key_c = 2;
        let rot_value_c = 3;

        let mut cm = CellManager::new(meta, 1, &ctx.managed_columns, 0);
        let mut ctx_key_data_c: Option<KeyData<F>> = None;
        let mut ctx_key_data_s: Option<KeyData<F>> = None;
        let mut ctx_key_data_w: Option<KeyData<F>> = None;
        let mut ctx_parent_data_s: Option<ParentData<F>> = None;
        let mut ctx_parent_data_c: Option<ParentData<F>> = None;
        let mut ctx_diff_inv: Option<Cell<F>> = None;


        circuit!([meta, cb.base], {
            let mut branch = BranchNodeInfo::new(meta, ctx.clone(), is_s, rot_branch_init);

            let mut offset = 0;
            for is_s in [true, false] {
                let storage = StorageLeafInfo::new(meta, ctx.clone(), is_s, offset);
                branch.set_is_s(is_s);

                // Load the last key values, which depends on the branch being a placeholder.
                let is_branch_placeholder = ifx! {not!(storage.is_below_account(meta)) => { branch.is_placeholder() }};
                let load_offset = ifx! {is_branch_placeholder => { 1.expr() }};
                let key_data = KeyData::load(&mut cb.base, &mut cm, &ctx.memory[key_memory(is_s)], load_offset);

                // The two flag values need to be boolean.
                require!(storage.flag1 => bool);
                require!(storage.flag2 => bool);

                // Calculate and store the leaf data RLC
                require!(a!(accs.acc_s.rlc, offset) => ctx.rlc(meta, 0..36, offset));

                // Calculate and store the key RLC.
                let key_rlc = key_data.rlc.expr()
                    + storage.key_rlc(
                        meta,
                        &mut cb.base,
                        key_data.mult.expr(),
                        key_data.is_odd.expr(),
                        1.expr(),
                        true,
                        0,
                    );
                require!(a!(accs.key.rlc, offset) => key_rlc);

                // Total number of nibbles needs to be KEY_LEN_IN_NIBBLES (except in a
                // placeholder leaf).
                // TODO(Brecht): why not in placeholder leaf?
                ifx! {not!(storage.is_placeholder(meta)) => {
                    let num_nibbles = storage.num_key_nibbles(meta, key_data.is_odd.expr());
                    require!(key_data.num_nibbles.expr() + num_nibbles => KEY_LEN_IN_NIBBLES);
                }}

                // Num bytes used in RLC
                let num_bytes = storage.num_bytes_on_key_row(meta);
                // Multiplier is number of bytes
                require!((FixedTableTag::RMult, num_bytes.expr(), a!(accs.acc_s.mult, offset)) => @"fixed");
                // RLC bytes zero check
                //cb.set_length(num_bytes.expr());

                // Key done, set the default values
                KeyData::store(&mut cb.base, &ctx.memory[key_memory(is_s)], KeyData::default_values());

                if is_s {
                    ctx_key_data_s = Some(key_data);
                } else {
                    ctx_key_data_c = Some(key_data);
                }

                offset += 1;

                let is_long = a!(accs.s_mod_node_rlc, offset);
                let is_short = a!(accs.c_mod_node_rlc, offset);

                // We need to ensure `is_long` and `is_short` are boolean.
                require!(is_short => bool);
                require!(is_long => bool);
                // `is_short` or `is_long` needs to be true.
                require!(sum::expr([is_short.expr(), is_long.expr()]) => 1);

                let rot_s = offset + if is_s { 0 } else { -2 };
                let rot_key = offset - 1;

                // We need to ensure that the stored leaf RLC and value RLC is the same as the
                // computed one.
                let leaf_rlc = DataTransition::new_with_rot(meta, accs.acc_s.rlc, offset - 1, offset);
                let value_rlc = DataTransition::new_with_rot(meta, accs.acc_c.rlc, rot_s, offset);
                let mult_prev = a!(accs.acc_s.mult, rot_key);
                let (new_value_rlc, leaf_rlc_part) = ifx! {is_short => {
                    (a!(s_main.rlp1, offset), a!(s_main.rlp1, offset) * mult_prev.expr())
                } elsex {
                    let value_rlc = s_main.bytes(meta, offset).rlc(&r);
                    let leaf_rlc = (0.expr(), mult_prev.expr()).rlc_chain([a!(s_main.rlp1, offset), a!(s_main.rlp2, offset), value_rlc.expr()].rlc(&r));
                    (value_rlc, leaf_rlc)
                }};
                require!(value_rlc => new_value_rlc);
                require!(leaf_rlc => leaf_rlc.prev() + leaf_rlc_part);

                // To enable external lookups we need to have the key and the previous/current
                // value on the same row.
                if !is_s {
                    require!(a!(accs.key.mult, offset) => a!(accs.key.rlc, rot_key));
                    require!(a!(value_prev, offset) => value_rlc.prev());
                    require!(a!(value, offset) => value_rlc);
                }

                // Get the number of bytes used by the value
                let value_num_bytes = matchx! {
                    is_short => 1.expr(),
                    is_long => 1.expr() + get_num_bytes_short(a!(s_main.rlp2, offset)),
                };

                // If `is_modified_node_empty = 1`, which means an empty child, we need to
                // ensure that the value is set to 0 in the placeholder leaf. For
                // example when adding a new storage leaf to the trie, we have an empty child in
                // `S` proof and non-empty in `C` proof.
                ifx! {branch.contains_placeholder_leaf(meta, is_s) => {
                    require!(a!(s_main.rlp1, offset) => 0);
                }}

                // Make sure the RLP encoding is correct.
                // storage = [key, value]
                let num_bytes = storage.num_bytes(meta);
                // TODO(Brecht): modify the witness for empty placeholder leafs to have valid
                // RLP encoding
                ifx! {not!(branch.contains_placeholder_leaf(meta, is_s)) => {
                    let key_num_bytes = storage.num_bytes_on_key_row(meta);
                    require!(num_bytes => key_num_bytes.expr() + value_num_bytes.expr());
                }};

                // Check if the account is in its parent.
                let branch = BranchNodeInfo::new(meta, ctx.clone(), is_s, rot_branch_init);
                let parent_data = ParentData::load(
                    "leaf load",
                    &mut cb.base,
                    &mut cm,
                    &ctx.memory[parent_memory(is_s)],
                    0.expr(),
                );
                // Check is skipped for placeholder leafs which are dummy leafs
                ifx! {storage.is_below_account(meta), storage.is_placeholder_without_branch(meta) => {
                    // TODO(Brecht): Add this to the keccak table when necessary instead?
                    // Hash of the only storage leaf which is placeholder requires empty storage root
                    let empty_root_rlc = EMPTY_TRIE_HASH.iter().map(|v| v.expr()).collect::<Vec<_>>().rlc(&r);
                    require!(parent_data.rlc => empty_root_rlc);
                } elsex {
                    ifx!{not!(and::expr(&[not!(storage.is_below_account(meta)), branch.contains_placeholder_leaf(meta, is_s)])) => {
                        let is_not_hashed = a!(accs.acc_c.rlc, offset-1);
                        ifx!{or::expr(&[parent_data.force_hashed.expr(), not!(is_not_hashed)]) => {
                            // Hashed branch hash in parent branch
                            require!((1, leaf_rlc, num_bytes, parent_data.rlc) => @"keccak");
                        } elsex {
                            // Non-hashed branch hash in parent branch
                            require!(leaf_rlc => parent_data.rlc);
                        }}
                    }}
                }}
                // Store the new parent
                ParentData::store(
                    &mut cb.base,
                    &ctx.memory[parent_memory(is_s)],
                    [0.expr(), true.expr()],
                );

                // Set the number of bytes used
                //cb.set_length_s(value_num_bytes);

                offset += 1;

                if is_s {
                    ctx_parent_data_s = Some(parent_data);
                } else {
                    ctx_parent_data_c = Some(parent_data);
                }
            }


            let storage = StorageLeafInfo::new(meta, ctx.clone(), true, 0);
            ifx! {not!(storage.is_below_account(meta)) => {
                let branch = BranchNodeInfo::new(meta, ctx.clone(), true, rot_branch_init);
                let drifted_storage = StorageLeafInfo::new(meta, ctx.clone(), true, offset);

                // The two flag values need to be boolean.
                require!(drifted_storage.flag1 => bool);
                require!(drifted_storage.flag2 => bool);

                // Calculate and store the leaf RLC (RLP + key)
                let drifted_rlc = a!(accs.acc_s.rlc, offset);
                require!(drifted_rlc => ctx.rlc(meta, 0..36, offset));

                // We need the intermediate key RLC right before `drifted_index` is added to it.
                // If the branch parallel to the placeholder branch is an extension node,
                // we have the intermediate RLC stored in the extension node `accs.key.rlc`.
                let is_branch_in_first_level = branch.is_below_account(meta);
                let (key_rlc_prev, key_mult_prev) = get_parent_rlc_state(meta, ctx.clone(), is_branch_in_first_level, rot_parent);
                // Calculate the drifted key RLC
                let drifted_key_rlc = key_rlc_prev.expr() +
                    branch.drifted_nibble_rlc(meta, &mut cb.base, key_mult_prev.expr()) +
                    drifted_storage.key_rlc(meta, &mut cb.base, key_mult_prev, branch.is_key_odd(), r[0].expr(), true, 0);

                // Check zero bytes and mult_diff
                let mult = a!(accs.acc_s.mult, offset);
                ifx!{branch.is_placeholder_s_or_c() => {
                    // Num bytes used in RLC
                    let num_bytes = drifted_storage.num_bytes_on_key_row(meta);
                    // Multiplier is number of bytes
                    require!((FixedTableTag::RMult, num_bytes.expr(), mult) => @"fixed");
                    // RLC bytes zero check
                    //cb.set_length(num_bytes.expr());
                }}

                // Check that the drifted leaf is unchanged and is stored at `drifted_index`.
                let calc_rlc = |is_s, meta: &mut VirtualCells<'_, F>, cb: &mut ConstraintBuilder<F>| {
                    circuit!([meta, cb], {
                        let rot_key = if is_s { rot_key_s } else { rot_key_c };
                        let rot_value = if is_s { rot_value_s } else { rot_value_c };
                        // Complete the drifted leaf rlc by adding the bytes on the value row
                        let drifted_rlc = (drifted_rlc.expr(), mult.expr()).rlc_chain(s_main.rlc(meta, rot_value, &r));
                        (true.expr(), a!(accs.key.rlc, rot_key), drifted_rlc, a!(accs.mod_node_rlc(is_s), rot_branch_child))
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
                    require!((1, drifted_rlc, drifted_storage.num_bytes(meta), mod_hash) => @"keccak");
                }}
            }}

            offset += 1;

            let storage = StorageLeafInfo::new(meta, ctx.clone(), true, rot_key_c);
            let is_wrong_leaf = a!(s_main.rlp1, offset);

            // Make sure is_wrong_leaf is boolean
            require!(is_wrong_leaf => bool);

            let diff_inv = cm.query_cell(CellType::Storage);
            ifx! {a!(ctx.proof_type.is_non_existing_storage_proof, offset) => {
                // Get the previous key RLC data
                let key_data = KeyData::load(&mut cb.base, &mut cm, &ctx.memory[key_memory(true)], 1.expr());
                ifx! {is_wrong_leaf => {
                    // Calculate the key and check it's the address as requested in the lookup
                    let key_rlc_wrong = key_data.rlc.expr() + storage.key_rlc(meta, &mut cb.base, key_data.mult.expr(), key_data.is_odd.expr(), 1.expr(), false, offset - rot_key_c);
                    require!(a!(accs.key.mult, offset) => key_rlc_wrong);
                    // Now make sure this address is different than the one of the leaf
                    require!((a!(accs.key.mult, offset) - a!(accs.key.rlc, rot_key_c)) * diff_inv.expr() => 1);
                    // Make sure the lengths of the keys are the same
                    let mut storage_wrong = StorageLeafInfo::new(meta, ctx.clone(), true, rot_key_c);
                    storage_wrong.set_rot_key(0);
                    require!(storage_wrong.key_len(meta) => storage.key_len(meta));
                    // RLC bytes zero check
                    let num_bytes = storage.num_bytes_on_key_row(meta);
                    //cb.set_length(num_bytes);
                } elsex {
                    // In case when there is no wrong leaf, we need to check there is a nil object in the parent branch.
                    require!(key_data.is_placeholder_leaf_c => true);
                }}
                ctx_key_data_w = Some(key_data);
            } elsex {
                // is_wrong_leaf needs to be false when not in non_existing_account proof
                require!(is_wrong_leaf => false);
            }}
            ctx_diff_inv = Some(diff_inv);
        });

        LeafCombinedConfig {
            key_data_s: ctx_key_data_s.unwrap(),
            key_data_c: ctx_key_data_c.unwrap(),
            key_data_w: ctx_key_data_w.unwrap(),
            parent_data_s: ctx_parent_data_s.unwrap(),
            parent_data_c: ctx_parent_data_c.unwrap(),
            diff_inv: ctx_diff_inv.unwrap(),
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

        println!("offset: {}", offset);

        let base_offset = offset;
        let mut offset = offset;

        for is_s in [true, false] {

            /* KEY */

            {
                let row = &witness[offset];

                // Info whether leaf rlp is long or short:
                //  - long means the key length is at position 2.
                //  - short means the key length is at position 1.
                let mut typ = "short";
                if row.get_byte(0) == 248 {
                    typ = "long";
                } else if row.get_byte(1) == 32 {
                    typ = "last_level";
                } else if row.get_byte(1) < 128 {
                    typ = "one_nibble";
                }
                mpt_config.assign_long_short(region, typ, offset).ok();

                pv.acc_s = F::zero();
                pv.acc_mult_s = F::one();
                let len: usize;
                if typ == "long" {
                    len = (row.get_byte(2) - 128) as usize + 3;
                } else if typ == "short" {
                    len = (row.get_byte(1) - 128) as usize + 2;
                } else {
                    // last_level or one_nibble
                    len = 2
                }
                mpt_config.compute_acc_and_mult(&row.bytes, &mut pv.acc_s, &mut pv.acc_mult_s, 0, len);

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

                // note that this assignment needs to be after assign_acc call
                if row.get_byte(0) < 223 {
                    // when shorter than 32 bytes, the node doesn't get hashed
                    // not_hashed
                    region
                        .assign_advice(
                            || "assign not_hashed".to_string(),
                            mpt_config.accumulators.acc_c.rlc,
                            offset,
                            || Value::known(F::one()),
                        )
                        .ok();
                }

                // TODO: handle if branch or extension node is added
                let mut start = S_START - 1;
                if row.get_byte(0) == 248 {
                    // long RLP
                    start = S_START;
                }

                let is_branch_placeholder = if is_s {
                    pv.is_branch_s_placeholder
                } else {
                    pv.is_branch_c_placeholder
                };
                let load_offset = if is_branch_placeholder { 1 } else { 0 };

                let key_data = if is_s { &self.key_data_s } else { &self.key_data_c };
                key_data
                    .witness_load(region, base_offset, &mut pv.memory[key_memory(is_s)], load_offset)?;
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
                if (pv.is_branch_s_placeholder && row.get_type() == MptWitnessRowType::StorageLeafSKey)
                    || (pv.is_branch_c_placeholder && row.get_type() == MptWitnessRowType::StorageLeafCKey)
                {
                    key_rlc_new = pv.key_rlc_prev;
                    key_rlc_mult_new = pv.key_rlc_mult_prev;
                }
                if typ != "last_level" && typ != "one_nibble" {
                    // If in last level or having only one nibble,
                    // the key RLC is already computed using the first two bytes above.
                    mpt_config.compute_key_rlc(&row.bytes, &mut key_rlc_new, &mut key_rlc_mult_new, start);
                }
                region.assign_advice(
                    || "assign key_rlc".to_string(),
                    mpt_config.accumulators.key.rlc,
                    offset,
                    || Value::known(key_rlc_new),
                )?;
                pv.storage_key_rlc = key_rlc_new;

                // Store key_rlc into rlc2 to be later set in leaf value C row (to enable
                // lookups):
                pv.rlc2 = key_rlc_new;
            }



            /* VALUE */

            offset += 1;
            println!("offset value: {}", offset);

            {

                let row_prev = &witness[offset - 1];
                let row = &witness[offset];

                // Info whether leaf value is 1 byte or more:
                let mut is_long = false;
                if row_prev.get_byte(0) == 248 {
                    // whole leaf is in long format (3 RLP meta bytes)
                    let key_len = row_prev.get_byte(2) - 128;
                    if row_prev.get_byte(1) - key_len - 1 > 1 {
                        is_long = true;
                    }
                } else if row_prev.get_byte(1) < 128 {
                    // last_level or one_nibble
                    let leaf_len = row_prev.get_byte(0) - 192;
                    if leaf_len - 1 > 1 {
                        is_long = true;
                    }
                } else {
                    let leaf_len = row_prev.get_byte(0) - 192;
                    let key_len = row_prev.get_byte(1) - 128;
                    if leaf_len - key_len - 1 > 1 {
                        is_long = true;
                    }
                }
                // Short means there is only one byte for value (no RLP specific bytes).
                // Long means there is more than one byte for value which brings two
                // RLP specific bytes, like: 161 160 ... for 32-long value.
                let mut typ = "short";
                if is_long {
                    typ = "long";
                }
                mpt_config.assign_long_short(region, typ, offset).ok();

                // Leaf RLC
                mpt_config.compute_acc_and_mult(
                    &row.bytes,
                    &mut pv.acc_s,
                    &mut pv.acc_mult_s,
                    0,
                    HASH_WIDTH + 2,
                );

                pv.acc_c = F::zero();
                pv.acc_mult_c = F::one();
                // Leaf value RLC
                let mut start = 0;
                if is_long {
                    start = 2;
                }
                mpt_config.compute_acc_and_mult(
                    &row.bytes,
                    &mut pv.acc_c,
                    &mut pv.acc_mult_c,
                    start,
                    HASH_WIDTH + 2,
                );

                let empty_trie_hash: Vec<u8> = vec![
                    86, 232, 31, 23, 27, 204, 85, 166, 255, 131, 69, 230, 146, 192, 248, 110, 91, 72, 224,
                    27, 153, 108, 173, 192, 1, 98, 47, 181, 227, 99, 180, 33,
                ];
                if is_s {
                    // Store leaf value RLC into rlc1 to be later set in leaf value C row (to enable
                    // lookups):
                    pv.rlc1 = pv.acc_c;

                    /*
                    account leaf storage codehash S <- rotate here
                    account leaf storage codehash C
                    account leaf in added branch
                    leaf key S
                    leaf value S <- we are here
                    leaf key C
                    leaf value C
                    */
                    let row_prev = &witness[offset - 4];
                    if row_prev.get_type() == MptWitnessRowType::AccountLeafRootCodehashS
                        && row_prev.s_hash_bytes() == empty_trie_hash
                    {
                        // Leaf is without branch and it is just a placeholder.
                        region
                            .assign_advice(
                                || "assign sel1".to_string(),
                                mpt_config.denoter.sel1,
                                offset,
                                || Value::known(F::one()),
                            )
                            .ok();
                    }
                } else {
                    region
                        .assign_advice(
                            || "assign key_rlc into key_rlc_mult".to_string(),
                            mpt_config.accumulators.key.mult,
                            offset,
                            || Value::known(pv.rlc2),
                        )
                        .ok();
                    region
                        .assign_advice(
                            || "assign leaf value S into value_prev".to_string(),
                            mpt_config.value_prev,
                            offset,
                            || Value::known(pv.rlc1),
                        )
                        .ok();

                    /*
                    account leaf storage codehash S
                    account leaf storage codehash C <- rotate here
                    account leaf in added branch
                    leaf key S
                    leaf value S
                    leaf key C
                    leaf value C <- we are here
                    */
                    let row_prev = &witness[offset - 5];
                    if row_prev.get_type() == MptWitnessRowType::AccountLeafRootCodehashC
                        && row_prev.s_hash_bytes() == empty_trie_hash
                    {
                        // Leaf is without branch and it is just a placeholder.
                        region
                            .assign_advice(
                                || "assign sel2".to_string(),
                                mpt_config.denoter.sel2,
                                offset,
                                || Value::known(F::one()),
                            )
                            .ok();
                    }
                }

                let parent_data = if is_s { &self.parent_data_s } else { &self.parent_data_c };
                parent_data
                    .witness_load(region, base_offset, &mut pv.memory[parent_memory(is_s)], 0)
                    .ok();
                parent_data
                    .witness_store(
                        region,
                        base_offset,
                        &mut pv.memory[parent_memory(is_s)],
                        F::zero(),
                        true,
                    )
                    .ok();

                mpt_config
                    .assign_acc(
                        region,
                        pv.acc_s, // leaf RLC
                        pv.acc_mult_s,
                        pv.acc_c, // leaf value RLC
                        F::zero(),
                        offset,
                    )
                    .ok();

                region
                    .assign_advice(
                        || "assign leaf value C into value".to_string(),
                        mpt_config.value,
                        offset,
                        || Value::known(pv.acc_c),
                    )
                    .ok();

                if !is_s && row.get_byte_rev(IS_STORAGE_MOD_POS) == 1 {
                    region
                        .assign_advice(
                            || "assign lookup enabled".to_string(),
                            mpt_config.proof_type.proof_type,
                            offset,
                            || Value::known(F::from(6_u64)), /* storage mod lookup enabled in this row
                                                            * if it is is_storage_mod proof */
                        )
                        .ok();
                }
            }

            offset += 1;
        }

        {
            let row = &witness[offset];

            /*
            row[1] != 0 just to avoid usize problems below (when row doesn't
            need to be assigned) Info whether leaf rlp is long or short.
            */
            /*
            Info whether leaf rlp is long or short:
            - long means the key length is at position 2.
            - short means the key length is at position 1.
            */
            let mut typ = "short";
            if row.get_byte(0) == 248 {
                typ = "long";
            } else if row.get_byte(1) == 32 {
                typ = "last_level";
            } else if row.get_byte(1) < 128 {
                typ = "one_nibble";
            }
            mpt_config.assign_long_short(region, typ, offset).ok();

            pv.acc_s = F::zero();
            pv.acc_mult_s = F::one();
            let len: usize;
            if typ == "long" {
                len = (row.get_byte(2) - 128) as usize + 3;
            } else if typ == "short" {
                len = (row.get_byte(1) - 128) as usize + 2;
            } else {
                // last_level or one_nibble
                len = 2
            }
            mpt_config.compute_acc_and_mult(&row.bytes, &mut pv.acc_s, &mut pv.acc_mult_s, 0, len);

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

        {
            self.key_data_w
                .witness_load(region, base_offset, &mut pv.memory[key_memory(true)], 1)
                .ok();

            let row = &witness[offset];
            if row.get_byte_rev(IS_NON_EXISTING_STORAGE_POS) == 1 {
                let row_key_c = &witness[offset - (LEAF_NON_EXISTING_IND - LEAF_KEY_C_IND) as usize];
                let mut start = S_START - 1;
                if row_key_c.get_byte(0) == 248 {
                    start = S_START;
                }
                let mut key_rlc_new = pv.key_rlc;
                let mut key_rlc_mult_new = pv.key_rlc_mult;
                mpt_config.compute_key_rlc(&row.bytes, &mut key_rlc_new, &mut key_rlc_mult_new, start);
                region
                    .assign_advice(
                        || "assign key_rlc".to_string(),
                        mpt_config.accumulators.key.mult, // lookup uses `key.mult`
                        offset,
                        || Value::known(key_rlc_new),
                    )
                    .ok();

                let diff_inv = (key_rlc_new - pv.storage_key_rlc)
                    .invert()
                    .unwrap_or(F::zero());
                self.diff_inv
                    .assign(region, base_offset, Value::known(diff_inv))
                    .ok();

                if row.get_byte_rev(IS_NON_EXISTING_STORAGE_POS) == 1 {
                    region
                        .assign_advice(
                            || "assign lookup enabled".to_string(),
                            mpt_config.proof_type.proof_type,
                            offset,
                            || Value::known(F::from(7_u64)), /* non existing storage lookup enabled in
                                                            * this row if it is non_existing_storage
                                                            * proof */
                        )
                        .ok();
                }
            }
        }

        println!("offset post: {}", offset);

        Ok(())
    }
}
