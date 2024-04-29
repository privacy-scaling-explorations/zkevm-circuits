use eth_types::{Field, OpsIdentity, U256};
use ethers_core::types::transaction;
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
            ParentDataWitness, KECCAK,
        },
        param::{EMPTY_TRIE_HASH, KEY_LEN_IN_NIBBLES},
        MPTConfig, MPTContext, MptMemory, RlpItemType,
    },
    table::MPTProofType,
    util::word::WordLoHi,
    witness::MptUpdateRow,
};

use super::{
    helpers::{Indexable, KeyDataWitness, ListKeyGadget},
    mod_extension::ModExtensionGadget,
    rlp_gadgets::{RLPItemWitness, RLPValueGadget},
    witness_row::{Node, TransactionRowType},
};

#[derive(Clone, Debug, Default)]
pub(crate) struct TransactionLeafConfig<F> {
    main_data: MainData<F>,
    key_data: [KeyData<F>; 2],
    parent_data: [ParentData<F>; 2],

    rlp_key: [ListKeyGadget<F>; 2],
    value_rlp_bytes: [[Cell<F>; 1]; 2],
    rlp_value: [RLPValueGadget<F>; 2],
    is_placeholder_leaf: [IsPlaceholderLeafGadget<F>; 2],
    drifted: DriftedGadget<F>,
    is_mod_extension: [Cell<F>; 2],
    mod_extension: ModExtensionGadget<F>,
}

impl<F: Field> TransactionLeafConfig<F> {
    pub fn configure(
        meta: &mut VirtualCells<'_, F>,
        cb: &mut MPTConstraintBuilder<F>,
        ctx: &mut MPTContext<F>,
    ) -> Self {
        let mut config = TransactionLeafConfig::default();

        circuit!([meta, cb], {
            let key_items = [
                ctx.rlp_item(
                    meta,
                    cb,
                    TransactionRowType::KeyS as usize,
                    RlpItemType::Key,
                ),
                ctx.rlp_item(
                    meta,
                    cb,
                    TransactionRowType::KeyC as usize,
                    RlpItemType::Key,
                ),
            ];
            config.value_rlp_bytes = [cb.base.query_bytes(), cb.base.query_bytes()];
            let value_item = [
                ctx.rlp_item(
                    meta,
                    cb,
                    TransactionRowType::ValueS as usize,
                    RlpItemType::Value,
                ),
                ctx.rlp_item(
                    meta,
                    cb,
                    TransactionRowType::ValueC as usize,
                    RlpItemType::Value,
                ),
            ];
            let drifted_item = ctx.rlp_item(
                meta,
                cb,
                TransactionRowType::Drifted as usize,
                RlpItemType::Key,
            );

            let key_item = ctx.rlp_item(
                meta,
                cb,
                TransactionRowType::Key as usize,
                RlpItemType::Hash,
            );

            for is_proof_s in [true, false] {
                config.is_mod_extension[is_proof_s.idx()] = cb.query_bool();
            }

            config.main_data = MainData::load(cb, &mut ctx.memory[main_memory()], 0.expr());

            //
            require!(config.main_data.is_below_account => false);

            let mut key_rlc = vec![0.expr(); 2];
            let mut value_word = vec![WordLoHi::zero(); 2];
            let mut value_rlp_rlc = vec![0.expr(); 2];
            let mut value_rlp_rlc_mult = vec![0.expr(); 2];

            let parent_data = &mut config.parent_data;
            parent_data[0] = ParentData::load(cb, &mut ctx.memory[parent_memory(true)], 0.expr());
            parent_data[1] = ParentData::load(cb, &mut ctx.memory[parent_memory(false)], 0.expr());

            let key_data = &mut config.key_data;
            key_data[0] = KeyData::load(cb, &mut ctx.memory[key_memory(true)], 0.expr());
            key_data[1] = KeyData::load(cb, &mut ctx.memory[key_memory(false)], 0.expr());

            for is_proof_s in [true, false] {
                ifx! {not!(config.is_mod_extension[is_proof_s.idx()].expr()) => {
                    // Placeholder leaf checks
                    config.is_placeholder_leaf[is_proof_s.idx()] =
                        IsPlaceholderLeafGadget::construct(cb, parent_data[is_proof_s.idx()].hash.expr());
                    let is_placeholder_leaf = config.is_placeholder_leaf[is_proof_s.idx()].expr();

                    let rlp_key = &mut config.rlp_key[is_proof_s.idx()];
                    *rlp_key = ListKeyGadget::construct(cb, &key_items[is_proof_s.idx()]);
                    config.rlp_value[is_proof_s.idx()] = RLPValueGadget::construct(
                        cb,
                        &config.value_rlp_bytes[is_proof_s.idx()]
                            .iter()
                            .map(|c| c.expr())
                            .collect::<Vec<_>>(),
                    );

                    // Because the storage value is an rlp encoded string inside another rlp encoded
                    // string (leaves are always encoded as [key, value], with
                    // `value` here containing a single stored value) the stored
                    // value is either stored directly in the RLP encoded string if short, or stored
                    // wrapped inside another RLP encoded string if long.
                    let rlp_value = config.rlp_value[is_proof_s.idx()].rlc_value(&cb.key_r);
                    let rlp_value_rlc_mult =
                        config.rlp_value[is_proof_s.idx()].rlc_rlp_only_rev(&cb.keccak_r);
                    let value_lo;
                    let value_hi;
                    (
                        value_lo,
                        value_hi,
                        value_rlp_rlc[is_proof_s.idx()],
                        value_rlp_rlc_mult[is_proof_s.idx()],
                    ) = ifx! {config.rlp_value[is_proof_s.idx()].is_short() => {
                        (rlp_value, 0.expr(), rlp_value_rlc_mult.0.expr(), rlp_value_rlc_mult.1.expr())
                    } elsex {
                        let value = value_item[is_proof_s.idx()].word();
                        let value_rlp_rlc = rlp_value_rlc_mult.0.rlc_chain_rev(value_item[is_proof_s.idx()].rlc_chain_data());
                        require!(config.rlp_value[is_proof_s.idx()].num_bytes() => value_item[is_proof_s.idx()].num_bytes() + 1.expr());
                        (value.lo(), value.hi(), value_rlp_rlc, rlp_value_rlc_mult.1 * value_item[is_proof_s.idx()].mult())
                    }};
                    value_word[is_proof_s.idx()] = WordLoHi::<Expression<F>>::new([value_lo, value_hi]);

                    let leaf_rlc = rlp_key.rlc2(&cb.keccak_r).rlc_chain_rev((
                        value_rlp_rlc[is_proof_s.idx()].expr(),
                        value_rlp_rlc_mult[is_proof_s.idx()].expr(),
                    ));

                    // Key
                    key_rlc[is_proof_s.idx()] = key_data[is_proof_s.idx()].rlc.expr()
                        + rlp_key.key.expr(
                            cb,
                            rlp_key.key_value.clone(),
                            key_data[is_proof_s.idx()].mult.expr(),
                            key_data[is_proof_s.idx()].is_odd.expr(),
                            &cb.key_r.expr(),
                        );
                    // Total number of nibbles needs to be KEY_LEN_IN_NIBBLES
                    let num_nibbles =
                        num_nibbles::expr(rlp_key.key_value.len(), key_data[is_proof_s.idx()].is_odd.expr());
                    require!(key_data[is_proof_s.idx()].num_nibbles.expr() + num_nibbles => KEY_LEN_IN_NIBBLES);

                    // Placeholder leaves default to value `0`.
                    ifx! {is_placeholder_leaf => {
                        require!(value_word[is_proof_s.idx()] => WordLoHi::<Expression<F>>::zero());
                    }}

                    // Make sure the RLP encoding is correct.
                    // storage = [key, "value"]
                    require!(rlp_key.rlp_list.len() => key_items[is_proof_s.idx()].num_bytes() + config.rlp_value[is_proof_s.idx()].num_bytes());

                    // Check if the leaf is in its parent.
                    // Check is skipped for placeholder leaves which are dummy leaves.
                    // Note that the constraint works for the case when there is the placeholder branch above
                    // the leaf too - in this case `parent_data.hash` contains the hash of the node above the placeholder
                    // branch.
                    ifx! {not!(is_placeholder_leaf) => {
                        // config.is_not_hashed[is_proof_s.idx()] = LtGadget::construct(&mut cb.base, rlp_key.rlp_list.num_bytes(), 32.expr());
                        // ifx!{or::expr(&[parent_data[is_proof_s.idx()].is_root.expr(), not!(config.is_not_hashed[is_proof_s.idx()])]) => {
                        ifx!{parent_data[is_proof_s.idx()].is_root.expr() => {
                            // Hashed leaf in parent branch
                            let hash = parent_data[is_proof_s.idx()].hash.expr();
                            require!((1.expr(), leaf_rlc.expr(), rlp_key.rlp_list.num_bytes(), hash.lo(), hash.hi()) =>> @KECCAK);
                        } elsex {
                            // Non-hashed leaf in parent branch
                            require!(leaf_rlc => parent_data[is_proof_s.idx()].rlc.expr());
                        }}
                    } elsex {
                        // For NonExistingStorageProof prove there is no leaf.

                        // When there is only one leaf in the trie, `getProof` will always return this leaf - so we will have
                        // either the required leaf or the wrong leaf, so for NonExistingStorageProof we don't handle this
                        // case here (handled by WrongLeaf gadget).

                            ifx! {parent_data[is_proof_s.idx()].is_root.expr() => {
                                // If leaf is placeholder and the parent is root (no branch above leaf) and the proof is NonExistingStorageProof,
                                // the trie needs to be empty.
                                let empty_hash = WordLoHi::<F>::from(U256::from_big_endian(&EMPTY_TRIE_HASH));
                                let hash = parent_data[is_proof_s.idx()].hash.expr();
                                require!(hash.lo() => Expression::Constant(empty_hash.lo()));
                                require!(hash.hi() => Expression::Constant(empty_hash.hi()));
                            } elsex {
                                // For NonExistingStorageProof we need to prove that there is nil in the parent branch
                                // at the `modified_pos` position.
                                // Note that this does not hold when there is NonExistingStorageProof wrong leaf scenario,
                                // in this case there is a non-nil leaf. However, in this case the leaf is not a placeholder,
                                // so the check below is not triggered.
                                require!(parent_data[is_proof_s.idx()].rlc.expr() => 128.expr());
                            }}

                    }}
                }};

                // Key done, set the default values
                KeyData::store_defaults(cb, &mut ctx.memory[key_memory(is_proof_s)]);
                // Store the new parent
                ParentData::store(
                    cb,
                    &mut ctx.memory[parent_memory(is_proof_s)],
                    WordLoHi::zero(),
                    0.expr(),
                    true.expr(),
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

            // Put the data in the lookup table
            let key_rlc = ifx! {not!(config.parent_data[true.idx()].is_placeholder) => {
                key_rlc[true.idx()].expr()
            } elsex {
                key_rlc[false.idx()].expr()
            }};
            // Check that the key item contains the correct key for the path that was taken
            require!(key_item.hash_rlc() => key_rlc);

            ifx! {not!(config.parent_data[false.idx()].is_placeholder) => {
                    ctx.mpt_table.constrain(
                        meta,
                        &mut cb.base,
                        config.main_data.address.expr(),
                        false.expr(),
                        MPTProofType::TransactionUpdated.expr(),
                        WordLoHi::zero(),
                        config.main_data.new_root.expr(),
                        config.main_data.old_root.expr(),
                        value_word[false.idx()].clone(),
                        value_word[true.idx()].clone(),
                    );
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
                    false.expr(),
                    MPTProofType::TransactionUpdated.expr(),
                    WordLoHi::zero(),
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
            rlp_values[TransactionRowType::KeyS as usize].clone(),
            rlp_values[TransactionRowType::KeyC as usize].clone(),
        ];
        let value_item = [
            rlp_values[TransactionRowType::ValueS as usize].clone(),
            rlp_values[TransactionRowType::ValueC as usize].clone(),
        ];
        let drifted_item = rlp_values[TransactionRowType::Drifted as usize].clone();
        // let _key_item = rlp_values[TransactionRowType::Key as usize].clone();
        let tx_idx = rlp_values[TransactionRowType::Index as usize].clone();

        let main_data =
            self.main_data
                .witness_load(region, offset, &mut memory[main_memory()], 0)?;

        let mut key_data = vec![KeyDataWitness::default(); 2];
        let mut parent_data = vec![ParentDataWitness::default(); 2];
        let mut key_rlc = vec![0.scalar(); 2];
        let mut value_word = [WordLoHi::zero(); 2];
        for is_proof_s in [true, false] {
            self.is_mod_extension[is_proof_s.idx()].assign(
                region,
                offset,
                storage.is_mod_extension[is_proof_s.idx()].scalar(),
            )?;

            parent_data[is_proof_s.idx()] = self.parent_data[is_proof_s.idx()].witness_load(
                region,
                offset,
                &mut memory[parent_memory(is_proof_s)],
                0,
            )?;

            let rlp_key_witness = self.rlp_key[is_proof_s.idx()].assign(
                region,
                offset,
                &storage.list_rlp_bytes[is_proof_s.idx()],
                &key_items[is_proof_s.idx()],
            )?;

            key_data[is_proof_s.idx()] = self.key_data[is_proof_s.idx()].witness_load(
                region,
                offset,
                &mut memory[key_memory(is_proof_s)],
                0,
            )?;
            KeyData::witness_store(
                region,
                offset,
                &mut memory[key_memory(is_proof_s)],
                F::ZERO,
                F::ONE,
                0,
                F::ZERO,
                F::ONE,
                0,
            )?;

            // Key
            (key_rlc[is_proof_s.idx()], _) = rlp_key_witness.key.key(
                rlp_key_witness.key_item.clone(),
                key_data[is_proof_s.idx()].rlc,
                key_data[is_proof_s.idx()].mult,
                region.key_r,
            );

            // Value
            for (cell, byte) in self.value_rlp_bytes[is_proof_s.idx()]
                .iter()
                .zip(storage.value_rlp_bytes[is_proof_s.idx()].iter())
            {
                cell.assign(region, offset, byte.scalar())?;
            }
            let value_witness = self.rlp_value[is_proof_s.idx()].assign(
                region,
                offset,
                &storage.value_rlp_bytes[is_proof_s.idx()],
            )?;
            value_word[is_proof_s.idx()] = if value_witness.is_short() {
                WordLoHi::<F>::new([value_witness.rlc_value(region.key_r), 0.scalar()])
            } else {
                value_item[is_proof_s.idx()].word()
            };

            ParentData::witness_store(
                region,
                offset,
                &mut memory[parent_memory(is_proof_s)],
                WordLoHi::<F>::new([F::ZERO, F::ZERO]),
                F::ZERO,
                true,
                false,
                WordLoHi::<F>::new([F::ZERO, F::ZERO]),
            )?;

            self.is_placeholder_leaf[is_proof_s.idx()].assign(
                region,
                offset,
                parent_data[is_proof_s.idx()].hash,
            )?;
        }

        // Drifted leaf handling
        self.drifted.assign(
            region,
            offset,
            &parent_data,
            &storage.drifted_rlp_bytes,
            &drifted_item,
            region.key_r,
        )?;

        MainData::witness_store(
            region,
            offset,
            &mut memory[main_memory()],
            main_data.proof_type,
            false,
            F::ZERO,
            tx_idx.word().lo(),
            main_data.new_root,
            main_data.old_root,
        )?;

        if storage.is_mod_extension[0] || storage.is_mod_extension[1] {
            let mod_list_rlp_bytes: [&[u8]; 2] = [
                &storage.mod_list_rlp_bytes[0],
                &storage.mod_list_rlp_bytes[1],
            ];
            self.mod_extension
                .assign(region, offset, rlp_values, mod_list_rlp_bytes)?;
        }

        let mut new_value = value_word[false.idx()];
        let old_value = value_word[true.idx()];
        if parent_data[false.idx()].is_placeholder {
            new_value = WordLoHi::zero();
        }
        mpt_config.mpt_table.assign_cached(
            region,
            offset,
            &MptUpdateRow {
                address: Value::known(main_data.address),
                storage_key: WordLoHi::new([Value::known(F::ZERO), Value::known(F::ZERO)]),
                transaction_index: Value::known(F::ZERO),
                proof_type: Value::known(MPTProofType::TransactionUpdated.scalar()),
                new_root: main_data.new_root.into_value(),
                old_root: main_data.old_root.into_value(),
                new_value: new_value.into_value(),
                old_value: old_value.into_value(),
            },
        )?;

        Ok(())
    }
}
