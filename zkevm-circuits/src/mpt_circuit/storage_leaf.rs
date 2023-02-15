use eth_types::Field;
use gadgets::util::Scalar;
use halo2_proofs::plonk::{Advice, Column, ConstraintSystem};
use halo2_proofs::{
    circuit::{Region, Value},
    plonk::{Error, VirtualCells},
    poly::Rotation,
};
use std::marker::PhantomData;

use crate::circuit_tools::cell_manager::Cell;
use crate::circuit_tools::constraint_builder::{ConstraintBuilder, RLCChainable, RLCable};
use crate::circuit_tools::gadgets::{LtGadget, RequireNotZeroGadget, IsEqualGadget};
use crate::table::ProofType;
use crate::{
    assign,
    circuit,
    mpt_circuit::{
        helpers::BranchNodeInfo,
        param::{BRANCH_ROWS_NUM},
    },
    mpt_circuit::{
        helpers::{
            get_parent_rlc_state, key_memory, parent_memory, KeyData, MPTConstraintBuilder,
            ParentData, StorageLeafInfo,
        },
        param::{
            EMPTY_TRIE_HASH, HASH_WIDTH, IS_NON_EXISTING_STORAGE_POS, IS_STORAGE_MOD_POS,
            KEY_LEN_IN_NIBBLES, LEAF_KEY_C_IND, LEAF_NON_EXISTING_IND,
        },
        FixedTableTag,
    },
    mpt_circuit::{
        witness_row::{MptWitnessRow, MptWitnessRowType},
        MPTContext,
    },
    mpt_circuit::{MPTConfig, ProofValues},
};

use super::helpers::{Indexable, LeafKeyGadget, RLPValueGadget, bytes_into_rlc};

#[derive(Clone, Debug)]
pub(crate) struct StorageLeafCols<F> {
    pub(crate) is_s_key: Column<Advice>,
    pub(crate) is_s_value: Column<Advice>,
    pub(crate) is_c_key: Column<Advice>,
    pub(crate) is_c_value: Column<Advice>,
    /** it is at drifted_pos position in added branch,
     * note that this row could be omitted when there
     * is no added branch but then it would open a
     * vulnerability because the attacker could omit
     * these row in cases when it is needed too (and
     * constraints happen in this row) */
    pub(crate) is_in_added_branch: Column<Advice>,
    pub(crate) is_non_existing: Column<Advice>,
    _marker: PhantomData<F>,
}

impl<F: Field> StorageLeafCols<F> {
    pub(crate) fn new(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            is_s_key: meta.advice_column(),
            is_s_value: meta.advice_column(),
            is_c_key: meta.advice_column(),
            is_c_value: meta.advice_column(),
            is_in_added_branch: meta.advice_column(),
            is_non_existing: meta.advice_column(),
            _marker: PhantomData,
        }
    }

    pub(crate) fn is_key(&self, is_s: bool) -> Column<Advice> {
        if is_s {
            self.is_s_key
        } else {
            self.is_c_key
        }
    }

    pub(crate) fn is_value(&self, is_s: bool) -> Column<Advice> {
        if is_s {
            self.is_s_value
        } else {
            self.is_c_value
        }
    }
}

#[derive(Default, Debug)]
pub(crate) struct StorageLeaf {
    pub(crate) is_s_key: bool,
    pub(crate) is_s_value: bool,
    pub(crate) is_c_key: bool,
    pub(crate) is_c_value: bool,
    pub(crate) is_in_added_branch: bool,
    pub(crate) is_non_existing: bool,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct StorageLeafConfig<F> {
    key_data: [KeyData<F>; 2],
    key_data_w: KeyData<F>,
    parent_data: [ParentData<F>; 2],
    mult: [Cell<F>; 2],
    drifted_mult: Cell<F>,
    rlp_key: [LeafKeyGadget<F>; 2],
    rlp_value: [RLPValueGadget<F>; 2],
    drifted_rlp_key: LeafKeyGadget<F>,
    wrong_rlp_key: LeafKeyGadget<F>,
    is_wrong_leaf: Cell<F>,
    check_is_wrong_leaf: RequireNotZeroGadget<F>,
    is_not_hashed: [LtGadget<F, 1>; 2],
    is_in_empty_trie: [IsEqualGadget<F>; 2],
    is_in_empty_branch: [IsEqualGadget<F>; 2],
}

impl<F: Field> StorageLeafConfig<F> {
    pub fn configure(
        meta: &mut VirtualCells<'_, F>,
        cb: &mut MPTConstraintBuilder<F>,
        ctx: MPTContext<F>,
    ) -> Self {
        let is_s = true;
        let accs = ctx.accumulators;
        let s_main = ctx.s_main;
        let r = ctx.r.clone();

        let rot_parent = -1;
        let rot_branch_init = rot_parent - (BRANCH_ROWS_NUM - 1);
        let rot_branch_child = rot_branch_init + 1;

        cb.base.cell_manager.as_mut().unwrap().reset();
        let mut config = StorageLeafConfig::default();

        circuit!([meta, cb.base], {
            let mut branch = BranchNodeInfo::new(meta, ctx.clone(), is_s, rot_branch_init);

            let mut offset = 0;
            let mut key_rlc = vec![0.expr(); 2];
            let mut value_rlc = vec![0.expr(); 2];
            let mut leaf_rlc_value = vec![0.expr(); 2];
            for is_s in [true, false] {
                // Parent data
                let parent_data = &mut config.parent_data[is_s.idx()];
                *parent_data = ParentData::load(
                    "leaf load",
                    &mut cb.base,
                    &ctx.memory[parent_memory(is_s)],
                    0.expr(),
                );

                branch.set_is_s(is_s);

                // Key data
                let is_branch_placeholder = ifx! {not!(parent_data.is_root) => { branch.is_placeholder() }};
                let load_offset = ifx! {is_branch_placeholder => { 1.expr() }};
                let key_data = &mut config.key_data[is_s.idx()];
                *key_data = KeyData::load(&mut cb.base, &ctx.memory[key_memory(is_s)], load_offset);

                // Placeholder checks
                let empty_root_rlc = EMPTY_TRIE_HASH.iter().map(|v| v.expr()).collect::<Vec<_>>().rlc(&r);
                config.is_in_empty_trie[is_s.idx()] = IsEqualGadget::construct(&mut cb.base, parent_data.rlc.expr(), empty_root_rlc.expr());
                config.is_in_empty_branch[is_s.idx()] = IsEqualGadget::construct(&mut cb.base, parent_data.rlc.expr(), 128.expr());
                let is_placeholder = or::expr(&[config.is_in_empty_trie[is_s.idx()].expr(), config.is_in_empty_branch[is_s.idx()].expr()]);

                // Calculate and store the leaf data RLC
                let leaf_rlc_key = ctx.rlc(meta, 0..36, offset);

                let rlp_key = &mut config.rlp_key[is_s.idx()];
                *rlp_key = LeafKeyGadget::construct(&mut cb.base, &ctx.expr(meta, offset));

                key_rlc[is_s.idx()] = key_data.rlc.expr()
                    + rlp_key.key_rlc(
                        &mut cb.base,
                        key_data.mult.expr(),
                        key_data.is_odd.expr(),
                        1.expr(),
                        true,
                        &r,
                    );

                // Total number of nibbles needs to be KEY_LEN_IN_NIBBLES (except in a
                // placeholder leaf).
                // TODO(Brecht): why not in placeholder leaf?
                ifx! {not!(is_placeholder) => {
                    let num_nibbles = rlp_key.num_key_nibbles(key_data.is_odd.expr());
                    require!(key_data.num_nibbles.expr() + num_nibbles => KEY_LEN_IN_NIBBLES);
                }}

                // Num bytes used in RLC
                let num_bytes = rlp_key.num_bytes_on_key_row();
                // Multiplier is number of bytes
                config.mult[is_s.idx()] = cb.base.query_cell();
                require!((FixedTableTag::RMult, num_bytes.expr(), config.mult[is_s.idx()].expr()) => @"fixed");
                // RLC bytes zero check
                //cb.set_length(num_bytes.expr());

                // Key done, set the default values
                KeyData::store(
                    &mut cb.base,
                    &ctx.memory[key_memory(is_s)],
                    KeyData::default_values(),
                );

                offset += 1;

                let rlp_value = &mut config.rlp_value[is_s.idx()];
                *rlp_value = RLPValueGadget::construct(&mut cb.base, &s_main.expr(meta, offset));
                (value_rlc[is_s.idx()], leaf_rlc_value[is_s.idx()]) = rlp_value.rlc(&r);
                let leaf_rlc = (leaf_rlc_key, config.mult[is_s.idx()].expr())
                    .rlc_chain(leaf_rlc_value[is_s.idx()].expr());

                // If `is_modified_node_empty = 1`, which means an empty child, we need to
                // ensure that the value is set to 0 in the placeholder leaf. For
                // example when adding a new storage leaf to the trie, we have an empty child in
                // `S` proof and non-empty in `C` proof.
                ifx! {is_placeholder => {
                    require!(value_rlc[is_s.idx()] => 0);
                }}

                // Number of bytes used by the leaf in total
                let num_bytes = rlp_key.num_bytes();
                // Get the number of bytes used by the value
                let value_num_bytes = rlp_value.num_bytes();

                // Make sure the RLP encoding is correct.
                // storage = [key, value]
                // TODO(Brecht): modify the witness for empty placeholder leafs to have valid
                // RLP encoding
                ifx! {not!(is_placeholder) => {
                    let key_num_bytes = rlp_key.num_bytes_on_key_row();
                    require!(num_bytes => key_num_bytes.expr() + value_num_bytes.expr());
                }};

                // Check if the account is in its parent.
                // Check is skipped for placeholder leafs which are dummy leafs
                ifx! {not!(is_placeholder) => {
                    config.is_not_hashed[is_s.idx()] = LtGadget::construct(&mut cb.base, num_bytes.expr(), 32.expr());
                    ifx!{or::expr(&[parent_data.is_root.expr(), not!(config.is_not_hashed[is_s.idx()])]) => {
                        // Hashed branch hash in parent branch
                        require!((1, leaf_rlc, num_bytes, parent_data.rlc) => @"keccak");
                    } elsex {
                        // Non-hashed branch hash in parent branch
                        require!(leaf_rlc => parent_data.rlc);
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
            }

            // Put the data in the lookup table
            require!(a!(ctx.mpt_table.key_rlc, offset-1) => key_rlc[false.idx()]);
            require!(a!(ctx.mpt_table.value_prev, offset-1) => value_rlc[true.idx()]);
            require!(a!(ctx.mpt_table.value, offset-1) => value_rlc[false.idx()]);

            // Drifted leaf
            let storage = StorageLeafInfo::new(ctx.clone(), true, 0);
            ifx! {branch.is_placeholder_s_or_c(), not!(storage.is_below_account(meta)) => {
                config.drifted_rlp_key = LeafKeyGadget::construct(&mut cb.base, &ctx.expr(meta, offset));

                // Calculate and store the leaf RLC (RLP + key)
                let drifted_rlc_key = ctx.rlc(meta, 0..36, offset);

                // We need the intermediate key RLC right before `drifted_index` is added to it.
                // If the branch parallel to the placeholder branch is an extension node,
                // we have the intermediate RLC stored in the extension node `accs.key.rlc`.
                let is_branch_in_first_level = branch.is_below_account(meta);
                let (key_rlc_prev, key_mult_prev) = get_parent_rlc_state(meta, ctx.clone(), is_branch_in_first_level, rot_parent);
                // Calculate the drifted key RLC
                let drifted_key_rlc = key_rlc_prev.expr() +
                    branch.drifted_nibble_rlc(meta, &mut cb.base, key_mult_prev.expr()) +
                    config.drifted_rlp_key.key_rlc(&mut cb.base, key_mult_prev, branch.is_key_odd(), r[0].expr(), true, &r);

                // Check zero bytes and mult_diff
                config.drifted_mult = cb.base.query_cell();
                // Num bytes used in RLC
                let num_bytes = config.drifted_rlp_key.num_bytes_on_key_row();
                // Multiplier is number of bytes
                require!((FixedTableTag::RMult, num_bytes.expr(), config.drifted_mult.expr()) => @"fixed");
                // RLC bytes zero check
                //cb.set_length(num_bytes.expr());

                // Check that the drifted leaf is unchanged and is stored at `drifted_index`.
                let calc_rlc = |is_s: bool, meta: &mut VirtualCells<'_, F>, cb: &mut ConstraintBuilder<F>| {
                    circuit!([meta, cb], {
                        // Complete the drifted leaf rlc by adding the bytes on the value row
                        let drifted_rlc = (drifted_rlc_key.expr(), config.drifted_mult.expr()).rlc_chain(leaf_rlc_value[is_s.idx()].expr());
                        (key_rlc[is_s.idx()].expr(), drifted_rlc, a!(accs.mod_node_rlc(is_s), rot_branch_child))
                    })
                };
                let (key_rlc, drifted_rlc, mod_hash) = matchx! {
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
                };
                // The key of the drifted leaf needs to match the key of the leaf
                require!(key_rlc => drifted_key_rlc);
                // The drifted leaf needs to be stored in the branch at `drifted_index`.
                require!((1, drifted_rlc, config.drifted_rlp_key.num_bytes(), mod_hash) => @"keccak");
            }}

            offset += 1;

            config.is_wrong_leaf = cb.base.query_cell();
            // Make sure is_wrong_leaf is boolean
            require!(config.is_wrong_leaf => bool);
            ifx! {a!(ctx.proof_type.is_non_existing_storage_proof, offset) => {
                // Get the previous key RLC data
                config.key_data_w = KeyData::load(&mut cb.base, &ctx.memory[key_memory(true)], 1.expr());
                ifx! {config.is_wrong_leaf => {
                    config.wrong_rlp_key = LeafKeyGadget::construct(&mut cb.base, &ctx.expr(meta, offset));
                    // Calculate the key and check it's the address as requested in the lookup
                    let key_rlc_wrong = config.key_data_w.rlc.expr() + config.wrong_rlp_key.key_rlc(
                        &mut cb.base,
                        config.key_data_w.mult.expr(),
                        config.key_data_w.is_odd.expr(),
                        1.expr(),
                        false,
                        &ctx.r,
                    );
                    // TODO(Brecht): only checks the key, not prev_value/value?
                    let key_rlc_lookup = a!(ctx.mpt_table.key_rlc, offset);
                    require!(key_rlc_lookup => key_rlc_wrong);

                    // Now make sure this address is different than the one of the leaf
                    config.check_is_wrong_leaf = RequireNotZeroGadget::construct(&mut cb.base, key_rlc_lookup - key_rlc[false.idx()].expr());
                    // Make sure the lengths of the keys are the same
                    require!(config.wrong_rlp_key.key_len() => config.rlp_key[false.idx()].key_len());
                    // RLC bytes zero check
                    let num_bytes = config.wrong_rlp_key.num_bytes_on_key_row();
                    //cb.set_length(num_bytes);
                } elsex {
                    // In case when there is no wrong leaf, we need to check there is a nil object in the parent branch.
                    require!(config.key_data_w.is_placeholder_leaf_c => true);
                }}
            } elsex {
                // is_wrong_leaf needs to be false when not in non_existing_account proof
                require!(config.is_wrong_leaf => false);
            }}
        });

        config
    }

    pub fn assign(
        &self,
        region: &mut Region<'_, F>,
        ctx: &MPTConfig<F>,
        witness: &[MptWitnessRow<F>],
        pv: &mut ProofValues<F>,
        offset: usize,
    ) -> Result<(), Error> {
        let base_offset = offset;
        let mut offset = offset;

        let mut key_rlc = vec![0.scalar(); 2];
        let mut value_rlc = vec![0.scalar(); 2];
        for is_s in [true, false] {
            /* KEY */
            {
                let key_row = &witness[offset];

                let rlp_key_witness = self.rlp_key[is_s.idx()]
                    .assign(region, base_offset, &key_row.bytes)
                    .ok()
                    .unwrap();

                pv.acc_s = F::zero();
                pv.acc_mult_s = F::one();
                ctx.compute_acc_and_mult(
                    &key_row.bytes,
                    &mut pv.acc_s,
                    &mut pv.acc_mult_s,
                    0,
                    rlp_key_witness.num_bytes_on_key_row() as usize,
                );

                self.mult[is_s.idx()]
                    .assign(region, base_offset, pv.acc_mult_s)
                    .ok();

                self.is_not_hashed[is_s.idx()]
                    .assign(
                        region,
                        base_offset,
                        F::from(rlp_key_witness.num_bytes()),
                        F::from(32),
                    )
                    .ok();

                let is_branch_placeholder = if is_s {
                    pv.is_branch_s_placeholder
                } else {
                    pv.is_branch_c_placeholder
                };
                let load_offset = if is_branch_placeholder { 1 } else { 0 };
                self.key_data[is_s.idx()].witness_load(
                    region,
                    base_offset,
                    &mut pv.memory[key_memory(is_s)],
                    load_offset,
                )?;
                self.key_data[is_s.idx()].witness_store(
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
                if (pv.is_branch_s_placeholder
                    && key_row.get_type() == MptWitnessRowType::StorageLeafSKey)
                    || (pv.is_branch_c_placeholder
                        && key_row.get_type() == MptWitnessRowType::StorageLeafCKey)
                {
                    key_rlc_new = pv.key_rlc_prev;
                    key_rlc_mult_new = pv.key_rlc_mult_prev;
                }
                if rlp_key_witness.num_bytes_on_key_row() != 2 {
                    // If in last level or having only one nibble,
                    // the key RLC is already computed using the first two bytes above.
                    ctx.compute_key_rlc(
                        &key_row.bytes,
                        &mut key_rlc_new,
                        &mut key_rlc_mult_new,
                        rlp_key_witness.num_rlp_bytes_list() as usize,
                    );
                }
                key_rlc[is_s.idx()] = key_rlc_new;
            }

            /* VALUE */

            offset += 1;

            {
                let value_row = &witness[offset];

                let value_witness = self.rlp_value[is_s.idx()]
                    .assign(region, base_offset, &value_row.bytes)
                    .ok()
                    .unwrap();

                // Leaf RLC
                ctx.compute_acc_and_mult(
                    &value_row.bytes,
                    &mut pv.acc_s,
                    &mut pv.acc_mult_s,
                    0,
                    HASH_WIDTH + 2,
                );

                pv.acc_c = F::zero();
                pv.acc_mult_c = F::one();
                ctx.compute_acc_and_mult(
                    &value_row.bytes,
                    &mut pv.acc_c,
                    &mut pv.acc_mult_c,
                    value_witness.num_rlp_bytes() as usize,
                    HASH_WIDTH + 2,
                );

                value_rlc[is_s.idx()] = pv.acc_c;

                let parent_values = self.parent_data[is_s.idx()]
                    .witness_load(region, base_offset, &mut pv.memory[parent_memory(is_s)], 0)
                    .ok().unwrap();
                self.parent_data[is_s.idx()]
                    .witness_store(
                        region,
                        base_offset,
                        &mut pv.memory[parent_memory(is_s)],
                        F::zero(),
                        true,
                    )
                    .ok();

                self.is_in_empty_trie[is_s.idx()].assign(region, base_offset, parent_values[0], bytes_into_rlc(&EMPTY_TRIE_HASH, ctx.randomness)).ok();
                self.is_in_empty_branch[is_s.idx()].assign(region, base_offset, parent_values[0], 128.scalar()).ok();

                if !is_s && value_row.get_byte_rev(IS_STORAGE_MOD_POS) == 1 {
                    assign!(region, (ctx.proof_type.proof_type, offset) => ProofType::StorageChanged.scalar()).ok();
                }
            }

            offset += 1;
        }

        // Put the data in the lookup table
        assign!(region, (ctx.mpt_table.key_rlc, offset - 1) => key_rlc[false.idx()]).ok();
        assign!(region, (ctx.mpt_table.value_prev, offset - 1) => value_rlc[true.idx()]).ok();
        assign!(region, (ctx.mpt_table.value, offset - 1) => value_rlc[false.idx()]).ok();

        // Drifted leaf handling
        if pv.is_branch_s_placeholder || pv.is_branch_c_placeholder {
            let row = &witness[offset];

            let drifted_key_witness = self
                .drifted_rlp_key
                .assign(region, base_offset, &row.bytes)
                .ok()
                .unwrap();

            pv.acc_s = F::zero();
            pv.acc_mult_s = F::one();
            ctx.compute_acc_and_mult(
                &row.bytes,
                &mut pv.acc_s,
                &mut pv.acc_mult_s,
                0,
                drifted_key_witness.num_bytes_on_key_row() as usize,
            );

            self.drifted_mult
                .assign(region, base_offset, pv.acc_mult_s)
                .ok();
        }
        offset += 1;

        {
            let row = &witness[offset];
            if row.get_byte_rev(IS_NON_EXISTING_STORAGE_POS) == 1 {
                self.key_data_w
                    .witness_load(region, base_offset, &mut pv.memory[key_memory(true)], 1)
                    .ok();

                // TODO(Brecht): Change how the witness is generated
                let is_wrong = row.bytes[0] != 0;
                self.is_wrong_leaf
                    .assign(region, base_offset, F::from(is_wrong))
                    .ok();

                let row_key_c =
                    &witness[offset - (LEAF_NON_EXISTING_IND - LEAF_KEY_C_IND) as usize];
                let mut row_bytes = row.bytes.clone();
                row_bytes[0] = row_key_c.bytes[0];

                let wrong_witness = self
                    .wrong_rlp_key
                    .assign(region, base_offset, &row_bytes)
                    .ok()
                    .unwrap();

                let mut key_rlc_new = pv.key_rlc;
                let mut key_rlc_mult_new = pv.key_rlc_mult;
                ctx.compute_key_rlc(
                    &row.bytes,
                    &mut key_rlc_new,
                    &mut key_rlc_mult_new,
                    wrong_witness.num_rlp_bytes_list() as usize,
                );
                assign!(region, (ctx.mpt_table.key_rlc, offset) => key_rlc_new).ok();

                self.check_is_wrong_leaf
                    .assign(region, base_offset, key_rlc_new - key_rlc[false.idx()])
                    .ok();

                assign!(region, (ctx.proof_type.proof_type, offset) => ProofType::StorageDoesNotExist.scalar()).ok();
            }
        }

        Ok(())
    }
}
