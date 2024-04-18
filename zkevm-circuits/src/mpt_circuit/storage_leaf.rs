use eth_types::{Field, OpsIdentity, U256};
use gadgets::util::Scalar;
use halo2_proofs::{
    circuit::Value,
    plonk::{Error, Expression, VirtualCells},
};
use itertools::Itertools;

use crate::{
    circuit,
    circuit_tools::{
        cached_region::CachedRegion,
        cell_manager::Cell,
        constraint_builder::{RLCChainableRev, RLCable},
        gadgets::{IsEqualGadget, LtGadget},
    },
    mpt_circuit::{
        helpers::{
            key_memory, main_memory, num_nibbles, parent_memory, DriftedGadget,
            IsPlaceholderLeafGadget, KeyData, MPTConstraintBuilder, MainData, ParentData,
            ParentDataWitness, WrongExtNodeGadget, KECCAK,
        },
        param::{EMPTY_TRIE_HASH, KEY_LEN_IN_NIBBLES},
        MPTConfig, MPTContext, MptMemory, RlpItemType,
    },
    table::MPTProofType,
    util::word::WordLoHi,
    witness::MptUpdateRow,
};

use super::{
    helpers::{Indexable, KeyDataWitness, ListKeyGadget, WrongLeafGadget},
    mod_extension::ModExtensionGadget,
    rlp_gadgets::{RLPItemWitness, RLPValueGadget},
    witness_row::{Node, StorageRowType},
};

#[derive(Clone, Debug, Default)]
pub(crate) struct StorageLeafConfig<F> {
    main_data: MainData<F>,
    key_data: [KeyData<F>; 2],
    key_data_prev: KeyData<F>,
    parent_data: [ParentData<F>; 2],
    rlp_key: [ListKeyGadget<F>; 2],
    value_rlp_bytes: [[Cell<F>; 1]; 2],
    rlp_value: [RLPValueGadget<F>; 2],
    is_wrong_leaf: Cell<F>,
    is_not_hashed: [LtGadget<F, 1>; 2],
    is_placeholder_leaf: [IsPlaceholderLeafGadget<F>; 2],
    drifted: DriftedGadget<F>,
    wrong_leaf: WrongLeafGadget<F>,
    wrong_ext_node: WrongExtNodeGadget<F>,
    is_storage_mod_proof: IsEqualGadget<F>,
    is_non_existing_storage_proof: IsEqualGadget<F>,
    is_mod_extension: [Cell<F>; 2],
    mod_extension: ModExtensionGadget<F>,
}

impl<F: Field> StorageLeafConfig<F> {
    pub fn configure(
        meta: &mut VirtualCells<'_, F>,
        cb: &mut MPTConstraintBuilder<F>,
        ctx: &mut MPTContext<F>,
    ) -> Self {
        let mut config = StorageLeafConfig::default();

        circuit!([meta, cb], {
            let key_items = [
                ctx.rlp_item(meta, cb, StorageRowType::KeyS as usize, RlpItemType::Key),
                ctx.rlp_item(meta, cb, StorageRowType::KeyC as usize, RlpItemType::Key),
            ];
            config.value_rlp_bytes = [cb.base.query_bytes(), cb.base.query_bytes()];
            let value_item = [
                ctx.rlp_item(
                    meta,
                    cb,
                    StorageRowType::ValueS as usize,
                    RlpItemType::Value,
                ),
                ctx.rlp_item(
                    meta,
                    cb,
                    StorageRowType::ValueC as usize,
                    RlpItemType::Value,
                ),
            ];
            let drifted_item =
                ctx.rlp_item(meta, cb, StorageRowType::Drifted as usize, RlpItemType::Key);
            let expected_item =
                ctx.rlp_item(meta, cb, StorageRowType::Wrong as usize, RlpItemType::Key);
            let address_item = ctx.rlp_item(
                meta,
                cb,
                StorageRowType::Address as usize,
                RlpItemType::Hash,
            );
            let key_item = ctx.rlp_item(meta, cb, StorageRowType::Key as usize, RlpItemType::Hash);

            for is_s in [true, false] {
                config.is_mod_extension[is_s.idx()] = cb.query_bool();
            }

            config.main_data = MainData::load(cb, &mut ctx.memory[main_memory()], 0.expr());

            // Storage leaves always need to be below accounts
            require!(config.main_data.is_below_account => true);

            let mut key_rlc = vec![0.expr(); 2];
            let mut value_word = vec![WordLoHi::zero(); 2];
            let mut value_rlp_rlc = vec![0.expr(); 2];
            let mut value_rlp_rlc_mult = vec![0.expr(); 2];

            let parent_data = &mut config.parent_data;
            parent_data[0] = ParentData::load(cb, &mut ctx.memory[parent_memory(true)], 0.expr());
            parent_data[1] = ParentData::load(cb, &mut ctx.memory[parent_memory(false)], 0.expr());

            config.key_data_prev = KeyData::load(cb, &mut ctx.memory[key_memory(false)], 1.expr());

            let key_data = &mut config.key_data;
            key_data[0] = KeyData::load(cb, &mut ctx.memory[key_memory(true)], 0.expr());
            key_data[1] = KeyData::load(cb, &mut ctx.memory[key_memory(false)], 0.expr());

            // Proof types
            config.is_storage_mod_proof = IsEqualGadget::construct(
                &mut cb.base,
                config.main_data.proof_type.expr(),
                MPTProofType::StorageChanged.expr(),
            );
            config.is_non_existing_storage_proof = IsEqualGadget::construct(
                &mut cb.base,
                config.main_data.proof_type.expr(),
                MPTProofType::StorageDoesNotExist.expr(),
            );

            let is_wrong_ext_case = parent_data[1].is_last_level_and_wrong_ext_case.expr();

            for is_s in [true, false] {
                ifx! {not!(config.is_mod_extension[is_s.idx()].expr()) => {
                    // Placeholder leaf checks
                    config.is_placeholder_leaf[is_s.idx()] =
                        IsPlaceholderLeafGadget::construct(cb, parent_data[is_s.idx()].hash.expr());
                    let is_placeholder_leaf = config.is_placeholder_leaf[is_s.idx()].expr();

                    let rlp_key = &mut config.rlp_key[is_s.idx()];
                    *rlp_key = ListKeyGadget::construct(cb, &key_items[is_s.idx()]);
                    config.rlp_value[is_s.idx()] = RLPValueGadget::construct(
                        cb,
                        &config.value_rlp_bytes[is_s.idx()]
                            .iter()
                            .map(|c| c.expr())
                            .collect::<Vec<_>>(),
                    );

                    // Because the storage value is an rlp encoded string inside another rlp encoded
                    // string (leaves are always encoded as [key, value], with
                    // `value` here containing a single stored value) the stored
                    // value is either stored directly in the RLP encoded string if short, or stored
                    // wrapped inside another RLP encoded string if long.
                    let rlp_value = config.rlp_value[is_s.idx()].rlc_value(&cb.key_r);
                    let rlp_value_rlc_mult =
                        config.rlp_value[is_s.idx()].rlc_rlp_only_rev(&cb.keccak_r);
                    let value_lo;
                    let value_hi;
                    (
                        value_lo,
                        value_hi,
                        value_rlp_rlc[is_s.idx()],
                        value_rlp_rlc_mult[is_s.idx()],
                    ) = ifx! {config.rlp_value[is_s.idx()].is_short() => {
                        (rlp_value, 0.expr(), rlp_value_rlc_mult.0.expr(), rlp_value_rlc_mult.1.expr())
                    } elsex {
                        let value = value_item[is_s.idx()].word();
                        let value_rlp_rlc = rlp_value_rlc_mult.0.rlc_chain_rev(value_item[is_s.idx()].rlc_chain_data());
                        require!(config.rlp_value[is_s.idx()].num_bytes() => value_item[is_s.idx()].num_bytes() + 1.expr());
                        (value.lo(), value.hi(), value_rlp_rlc, rlp_value_rlc_mult.1 * value_item[is_s.idx()].mult())
                    }};
                    value_word[is_s.idx()] = WordLoHi::<Expression<F>>::new([value_lo, value_hi]);

                    let leaf_rlc = rlp_key.rlc2(&cb.keccak_r).rlc_chain_rev((
                        value_rlp_rlc[is_s.idx()].expr(),
                        value_rlp_rlc_mult[is_s.idx()].expr(),
                    ));

                    // Key
                    key_rlc[is_s.idx()] = key_data[is_s.idx()].rlc.expr()
                        + rlp_key.key.expr(
                            cb,
                            rlp_key.key_value.clone(),
                            key_data[is_s.idx()].mult.expr(),
                            key_data[is_s.idx()].is_odd.expr(),
                            &cb.key_r.expr(),
                        );
                    // Total number of nibbles needs to be KEY_LEN_IN_NIBBLES
                    let num_nibbles =
                        num_nibbles::expr(rlp_key.key_value.len(), key_data[is_s.idx()].is_odd.expr());
                    ifx! {not!(is_wrong_ext_case) => {
                        require!(key_data[is_s.idx()].num_nibbles.expr() + num_nibbles => KEY_LEN_IN_NIBBLES);
                    }}

                    // Placeholder leaves default to value `0`.
                    ifx! {is_placeholder_leaf => {
                        require!(value_word[is_s.idx()] => WordLoHi::<Expression<F>>::zero());
                    }}

                    // Make sure the RLP encoding is correct.
                    // storage = [key, "value"]
                    ifx! {not!(is_wrong_ext_case) => {
                        require!(rlp_key.rlp_list.len() => key_items[is_s.idx()].num_bytes() + config.rlp_value[is_s.idx()].num_bytes());
                    }}

                    // Check if the leaf is in its parent.
                    // Check is skipped for placeholder leaves which are dummy leaves.
                    // Note that the constraint works for the case when there is the placeholder branch above
                    // the leaf too - in this case `parent_data.hash` contains the hash of the node above the placeholder
                    // branch.
                    ifx! {not!(or::expr(&[config.is_placeholder_leaf[is_s.idx()].expr(), is_wrong_ext_case.clone()])) => {
                        config.is_not_hashed[is_s.idx()] = LtGadget::construct(&mut cb.base, rlp_key.rlp_list.num_bytes(), 32.expr());
                        ifx!{or::expr(&[parent_data[is_s.idx()].is_root.expr(), not!(config.is_not_hashed[is_s.idx()])]) => {
                            // Hashed leaf in parent branch
                            let hash = parent_data[is_s.idx()].hash.expr();
                            require!((1.expr(), leaf_rlc.expr(), rlp_key.rlp_list.num_bytes(), hash.lo(), hash.hi()) =>> @KECCAK);
                        } elsex {
                            // Non-hashed leaf in parent branch
                            require!(leaf_rlc => parent_data[is_s.idx()].rlc.expr());
                        }}
                    } elsex {
                        // For NonExistingStorageProof prove there is no leaf.

                        // When there is only one leaf in the trie, `getProof` will always return this leaf - so we will have
                        // either the required leaf or the wrong leaf, so for NonExistingStorageProof we don't handle this
                        // case here (handled by WrongLeaf gadget).
                        ifx! {config.is_non_existing_storage_proof.expr() => {
                            ifx! {parent_data[is_s.idx()].is_root.expr() => {
                                // If leaf is placeholder and the parent is root (no branch above leaf) and the proof is NonExistingStorageProof,
                                // the trie needs to be empty.
                                let empty_hash = WordLoHi::<F>::from(U256::from_big_endian(&EMPTY_TRIE_HASH));
                                let hash = parent_data[is_s.idx()].hash.expr();
                                require!(hash.lo() => Expression::Constant(empty_hash.lo()));
                                require!(hash.hi() => Expression::Constant(empty_hash.hi()));
                            } elsex {
                                // For NonExistingStorageProof we need to prove that there is nil in the parent branch
                                // at the `modified_pos` position.
                                // Note that this does not hold when there is NonExistingStorageProof wrong leaf scenario,
                                // in this case there is a non-nil leaf. However, in this case the leaf is not a placeholder,
                                // so the check below is not triggered.
                                ifx! {not!(is_wrong_ext_case) => {
                                    require!(parent_data[is_s.idx()].rlc.expr() => 128.expr());
                                }}
                            }}

                        }}
                    }}
                }};

                // Key done, set the default values
                KeyData::store_defaults(cb, &mut ctx.memory[key_memory(is_s)]);
                // Store the new parent
                ParentData::store(
                    cb,
                    &mut ctx.memory[parent_memory(is_s)],
                    WordLoHi::zero(),
                    0.expr(),
                    true.expr(),
                    false.expr(),
                    false.expr(),
                    false.expr(),
                    WordLoHi::zero(),
                );
            }

            ifx! {or::expr(&[config.is_mod_extension[0].clone(), config.is_mod_extension[1].clone()]) => {
                config.mod_extension = ModExtensionGadget::configure(
                    meta,
                    cb,
                    ctx.clone(),
                    parent_data,
                    key_data,
                );
            }};

            // Drifted leaf handling
            config.drifted = DriftedGadget::construct(
                cb,
                &config
                    .rlp_value
                    .iter()
                    .map(|value| value.num_bytes())
                    .collect_vec(),
                &config.parent_data,
                &config.key_data,
                &key_rlc,
                &value_rlp_rlc,
                &value_rlp_rlc_mult,
                &drifted_item,
                &config.is_mod_extension,
                &cb.key_r.expr(),
            );

            let is_wrong_leaf_case = and::expr(&[
                config.is_non_existing_storage_proof.expr(),
                not!(config.parent_data[1].is_extension),
                not!(config.is_placeholder_leaf[1].expr()),
            ]);

            // When non-existing-proof, it needs to be one of the following cases:
            // (1) wrong leaf, (2) wrong extension node, (3) nil leaf - we need to check the sum of
            // these three cases is 1.
            ifx! {config.is_non_existing_storage_proof => {
                require!(is_wrong_ext_case.clone() + is_wrong_leaf_case.clone() + config.is_placeholder_leaf[1].expr() => 1.expr());
            }}

            // When is_last_level_and_wrong_ext_case, the proof type needs to be non-existing
            ifx! {is_wrong_ext_case => {
                require!(config.is_non_existing_storage_proof.expr() => 1.expr());
            }}

            // Wrong leaf handling
            config.wrong_leaf = WrongLeafGadget::construct(
                cb,
                key_item.hash_rlc(),
                is_wrong_leaf_case,
                &config.rlp_key[1].key_value, // C proof is used for non-existing proof
                &key_rlc[1],
                &expected_item,
                config.key_data[1].clone(),
                &cb.key_r.expr(),
            );

            // Wrong extension node handling
            let wrong_ext_middle = ctx.rlp_item(
                meta,
                cb,
                StorageRowType::LongExtNodeKey as usize,
                RlpItemType::Key,
            );
            let wrong_ext_middle_nibbles = ctx.rlp_item(
                meta,
                cb,
                StorageRowType::LongExtNodeNibbles as usize,
                RlpItemType::Nibbles,
            );
            let wrong_ext_after = ctx.rlp_item(
                meta,
                cb,
                StorageRowType::ShortExtNodeKey as usize,
                RlpItemType::Key,
            );
            let wrong_ext_after_nibbles = ctx.rlp_item(
                meta,
                cb,
                StorageRowType::ShortExtNodeNibbles as usize,
                RlpItemType::Nibbles,
            );

            // The extension_branch in the last level needs has `is_last_level_and_wrong_ext_case =
            // true` in the case of wrong extension node.
            // All other extension_branches (above it) need to have it `false` (constraint in
            // extension_branch.rs)

            config.wrong_ext_node = WrongExtNodeGadget::construct(
                cb,
                key_item.hash_rlc(),
                is_wrong_ext_case,
                &wrong_ext_middle,
                &wrong_ext_middle_nibbles,
                &wrong_ext_after,
                &wrong_ext_after_nibbles,
                config.key_data[1].clone(), /* C proof should be used everywhere for
                                             * non-existing proof */
                config.key_data_prev.clone(),
            );

            // Reset the main memory
            // This need to be the last node for this proof
            MainData::store(
                cb,
                &mut ctx.memory[main_memory()],
                [
                    MPTProofType::Disabled.expr(),
                    false.expr(),
                    0.expr(),
                    0.expr(),
                    0.expr(),
                    0.expr(),
                    0.expr(),
                ],
            );

            // For non-existing proofs the tree needs to remain the same
            ifx! {config.is_non_existing_storage_proof => {
                require!(config.main_data.new_root => config.main_data.old_root);
                require!(key_rlc[true.idx()] => key_rlc[false.idx()]);
            }}

            // Put the data in the lookup table
            let proof_type = matchx! {(
                config.is_storage_mod_proof => MPTProofType::StorageChanged.expr(),
                config.is_non_existing_storage_proof => MPTProofType::StorageDoesNotExist.expr(),
                _ => MPTProofType::Disabled.expr(),
            )};
            ifx! {not!(config.is_non_existing_storage_proof) => {
                let key_rlc = ifx!{not!(config.parent_data[true.idx()].is_placeholder) => {
                    key_rlc[true.idx()].expr()
                } elsex {
                    key_rlc[false.idx()].expr()
                }};
                // Check that the key item contains the correct key for the path that was taken
                require!(key_item.hash_rlc() => key_rlc);
                // Check if the key is correct for the given address
                if ctx.params.is_preimage_check_enabled() {
                    let key = key_item.word();
                    require!((1.expr(), address_item.bytes_le()[1..33].rlc(&cb.keccak_r), 32.expr(), key.lo(), key.hi()) =>> @KECCAK);
                }
            }};

            ifx! {not!(config.is_non_existing_storage_proof) => {
                let key_rlc = ifx!{not!(config.parent_data[true.idx()].is_placeholder) => {
                    key_rlc[true.idx()].expr()
                } elsex {
                    key_rlc[false.idx()].expr()
                }};
                // Check that the key item contains the correct key for the path that was taken
                require!(key_item.hash_rlc() => key_rlc);
                // Check if the key is correct for the given address
                if ctx.params.is_preimage_check_enabled() {
                    let key = key_item.word();
                    require!((1.expr(), address_item.bytes_le()[1..33].rlc(&cb.keccak_r), 32.expr(), key.lo(), key.hi()) =>> @KECCAK);
                }
            }};

            ifx! {not!(config.parent_data[false.idx()].is_placeholder) => {
                ifx! {not!(config.is_non_existing_storage_proof) => {
                    ctx.mpt_table.constrain(
                        meta,
                        &mut cb.base,
                        config.main_data.address.expr(),
                        proof_type.clone(),
                        address_item.word(),
                        config.main_data.new_root.expr(),
                        config.main_data.old_root.expr(),
                        value_word[false.idx()].clone(),
                        value_word[true.idx()].clone(),
                    );
                } elsex {
                    // Non-existing proof doesn't have the value set to 0 in the case of a wrong leaf - we set it to 0
                    // below to enable lookups with the value set to 0 (as in the case of a non-wrong non-existing proof).
                    ctx.mpt_table.constrain(
                        meta,
                        &mut cb.base,
                        config.main_data.address.expr(),
                        proof_type.clone(),
                        address_item.word(),
                        config.main_data.new_root.expr(),
                        config.main_data.old_root.expr(),
                        WordLoHi::<Expression<F>>::new([0.expr(), 0.expr()]),
                        WordLoHi::<Expression<F>>::new([0.expr(), 0.expr()]),
                    );
                }};
            } elsex {
                // When the value is set to 0, the leaf is deleted, and if there were only two leaves in the branch,
                // the neighbour leaf moves one level up and replaces the branch. When the lookup is executed with
                // the new value set to 0, the lookup fails (without the code below), because the leaf that is returned
                // is the neighbour node that moved up (because the branch and the old leaf doesn’t exist anymore),
                // but this leaf doesn’t have the zero value.
                ctx.mpt_table.constrain(
                    meta,
                    &mut cb.base,
                    config.main_data.address.expr(),
                    proof_type,
                    address_item.word(),
                    config.main_data.new_root.expr(),
                    config.main_data.old_root.expr(),
                    WordLoHi::zero(),
                    value_word[true.idx()].clone(),
                );
            }};
        });

        config
    }

    #[allow(clippy::too_many_arguments)]
    pub fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        mpt_config: &MPTConfig<F>,
        memory: &mut MptMemory<F>,
        offset: usize,
        node: &Node,
        rlp_values: &[RLPItemWitness],
    ) -> Result<(), Error> {
        let storage = &node.storage.clone().unwrap();

        let key_items = [
            rlp_values[StorageRowType::KeyS as usize].clone(),
            rlp_values[StorageRowType::KeyC as usize].clone(),
        ];
        let value_item = [
            rlp_values[StorageRowType::ValueS as usize].clone(),
            rlp_values[StorageRowType::ValueC as usize].clone(),
        ];
        let drifted_item = rlp_values[StorageRowType::Drifted as usize].clone();
        let expected_item = rlp_values[StorageRowType::Wrong as usize].clone();
        let address_item = rlp_values[StorageRowType::Address as usize].clone();
        let _key_item = rlp_values[StorageRowType::Key as usize].clone();

        let main_data =
            self.main_data
                .witness_load(region, offset, &mut memory[main_memory()], 0)?;

        let mut key_data = vec![KeyDataWitness::default(); 2];
        let mut parent_data = vec![ParentDataWitness::default(); 2];
        let mut key_rlc = vec![0.scalar(); 2];
        let mut value_word = [WordLoHi::zero(); 2];
        for is_s in [true, false] {
            self.is_mod_extension[is_s.idx()].assign(
                region,
                offset,
                storage.is_mod_extension[is_s.idx()].scalar(),
            )?;

            parent_data[is_s.idx()] = self.parent_data[is_s.idx()].witness_load(
                region,
                offset,
                &mut memory[parent_memory(is_s)],
                0,
            )?;

            let rlp_key_witness = self.rlp_key[is_s.idx()].assign(
                region,
                offset,
                &storage.list_rlp_bytes[is_s.idx()],
                &key_items[is_s.idx()],
            )?;

            self.is_not_hashed[is_s.idx()].assign(
                region,
                offset,
                rlp_key_witness.rlp_list.num_bytes().scalar(),
                32.scalar(),
            )?;

            key_data[is_s.idx()] = self.key_data[is_s.idx()].witness_load(
                region,
                offset,
                &mut memory[key_memory(is_s)],
                0,
            )?;
            KeyData::witness_store(
                region,
                offset,
                &mut memory[key_memory(is_s)],
                F::ZERO,
                F::ONE,
                0,
                F::ZERO,
                F::ONE,
                0,
            )?;

            // Key
            (key_rlc[is_s.idx()], _) = rlp_key_witness.key.key(
                rlp_key_witness.key_item.clone(),
                key_data[is_s.idx()].rlc,
                key_data[is_s.idx()].mult,
                region.key_r,
            );

            // Value
            for (cell, byte) in self.value_rlp_bytes[is_s.idx()]
                .iter()
                .zip(storage.value_rlp_bytes[is_s.idx()].iter())
            {
                cell.assign(region, offset, byte.scalar())?;
            }
            let value_witness = self.rlp_value[is_s.idx()].assign(
                region,
                offset,
                &storage.value_rlp_bytes[is_s.idx()],
            )?;
            value_word[is_s.idx()] = if value_witness.is_short() {
                WordLoHi::<F>::new([value_witness.rlc_value(region.key_r), 0.scalar()])
            } else {
                value_item[is_s.idx()].word()
            };

            ParentData::witness_store(
                region,
                offset,
                &mut memory[parent_memory(is_s)],
                WordLoHi::<F>::new([F::ZERO, F::ZERO]),
                F::ZERO,
                true,
                false,
                false,
                false,
                WordLoHi::<F>::new([F::ZERO, F::ZERO]),
            )?;

            self.is_placeholder_leaf[is_s.idx()].assign(
                region,
                offset,
                parent_data[is_s.idx()].hash,
            )?;
        }

        let is_storage_mod_proof = self.is_storage_mod_proof.assign(
            region,
            offset,
            main_data.proof_type.scalar(),
            MPTProofType::StorageChanged.scalar(),
        )? == true.scalar();
        let is_non_existing_proof = self.is_non_existing_storage_proof.assign(
            region,
            offset,
            main_data.proof_type.scalar(),
            MPTProofType::StorageDoesNotExist.scalar(),
        )? == true.scalar();

        // Drifted leaf handling
        self.drifted.assign(
            region,
            offset,
            &parent_data,
            &storage.drifted_rlp_bytes,
            &drifted_item,
            region.key_r,
        )?;

        // Wrong leaf / extension node handling
        let key_data_prev = self.key_data_prev.witness_load(
            region,
            offset,
            &mut memory[key_memory(false)],
            2, // 2 instead of 1 because default values have already been stored above
        )?;
        let (_key_rlc, _) = self.wrong_leaf.assign(
            region,
            offset,
            is_non_existing_proof,
            &key_rlc,
            &storage.wrong_rlp_bytes,
            &expected_item,
            false,
            key_data[1].clone(),
            region.key_r,
        )?;

        let wrong_ext_middle = rlp_values[StorageRowType::LongExtNodeKey as usize].clone();
        let wrong_ext_middle_nibbles =
            rlp_values[StorageRowType::LongExtNodeNibbles as usize].clone();
        self.wrong_ext_node.assign(
            region,
            offset,
            wrong_ext_middle,
            wrong_ext_middle_nibbles,
            key_data[1].clone(),
            key_data_prev.clone(),
        );

        // Reset the main memory
        MainData::witness_store(
            region,
            offset,
            &mut memory[main_memory()],
            MPTProofType::Disabled as usize,
            false,
            F::ZERO,
            WordLoHi::new([F::ZERO, F::ZERO]),
            WordLoHi::new([F::ZERO, F::ZERO]),
        )?;

        // Put the data in the lookup table
        let proof_type = if is_storage_mod_proof {
            MPTProofType::StorageChanged
        } else if is_non_existing_proof {
            MPTProofType::StorageDoesNotExist
        } else {
            MPTProofType::Disabled
        };

        if storage.is_mod_extension[0] || storage.is_mod_extension[1] {
            let mod_list_rlp_bytes: [&[u8]; 2] = [
                &storage.mod_list_rlp_bytes[0],
                &storage.mod_list_rlp_bytes[1],
            ];
            self.mod_extension
                .assign(region, offset, rlp_values, mod_list_rlp_bytes)?;
        }

        let mut new_value = value_word[false.idx()];
        let mut old_value = value_word[true.idx()];
        if parent_data[false.idx()].is_placeholder {
            new_value = WordLoHi::zero();
        } else if is_non_existing_proof {
            new_value = WordLoHi::zero();
            old_value = WordLoHi::zero();
        }
        mpt_config.mpt_table.assign_cached(
            region,
            offset,
            &MptUpdateRow {
                address: Value::known(main_data.address),
                storage_key: address_item.word().into_value(),
                proof_type: Value::known(proof_type.scalar()),
                new_root: main_data.new_root.into_value(),
                old_root: main_data.old_root.into_value(),
                new_value: new_value.into_value(),
                old_value: old_value.into_value(),
            },
        )?;

        Ok(())
    }
}
