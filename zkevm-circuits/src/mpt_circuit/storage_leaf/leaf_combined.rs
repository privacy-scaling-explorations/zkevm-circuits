use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Region, Value},
    plonk::{Error, VirtualCells},
    poly::Rotation,
};

use crate::{
    circuit,
    circuit_tools::{CellManager, DataTransition, RLCable, RLCChainable, ConstraintBuilder, CellType},
    mpt_circuit::{
        helpers::BranchNodeInfo,
        param::{BRANCH_ROWS_NUM, S_START},
    },
    mpt_circuit::{
        helpers::{KeyData, MPTConstraintBuilder, StorageLeafInfo, get_num_bytes_short, ParentData, parent_memory, get_parent_rlc_state},
        param::{KEY_LEN_IN_NIBBLES, EMPTY_TRIE_HASH},
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
    key_data: KeyData<F>,
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
        let mut ctx_key_data: Option<KeyData<F>> = None;

        circuit!([meta, cb.base], {
            let mut branch = BranchNodeInfo::new(meta, ctx.clone(), is_s, rot_branch_init);

            let mut offset = 0;
            for is_s in [true, false] {
                //cb.base.set_query_offset(offset);
                let storage = StorageLeafInfo::new(meta, ctx.clone(), is_s, offset);
                //storage.set_is_s(is_s);
                //storage.set_rot_key(offset);
                branch.set_is_s(is_s);

                // Load the last key values, which depends on the branch being a placeholder.
                let is_branch_placeholder = ifx! {not!(storage.is_below_account(meta)) => { branch.is_placeholder() }};
                let load_offset = ifx! {is_branch_placeholder => { 1.expr() }};
                let key_data = KeyData::load(&mut cb.base, &mut cm, &ctx.memory["key"], load_offset);

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
                /*ParentData::store(
                    &mut cb.base,
                    &ctx.memory[parent_memory(is_s)],
                    [0.expr(), true.expr()],
                );
                ctx_parent_data = Some(parent_data);

                // Set the number of bytes used
                cb.set_length_s(value_num_bytes);*/

                offset += 1;

                ctx_key_data = Some(key_data);
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
                let key_data = KeyData::load(&mut cb.base, &mut cm, &ctx.memory["key"], 2.expr());
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
                ctx_key_data = Some(key_data);
            } elsex {
                // is_wrong_leaf needs to be false when not in non_existing_account proof
                require!(is_wrong_leaf => false);
            }}

            // Key done, set the default values
            //KeyData::store(&mut cb.base, &ctx.memory["key"], KeyData::default_values());

            cb.base.set_query_offset(0);
        });

        LeafCombinedConfig {
            key_data: ctx_key_data.unwrap(),
        }
    }
}
