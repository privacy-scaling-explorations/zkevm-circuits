use eth_types::Field;
use gadgets::util::{pow, Scalar};
use halo2_proofs::{
    circuit::Value,
    plonk::{Error, VirtualCells},
    poly::Rotation,
};

use super::{
    helpers::{KeyDataWitness, ListKeyGadget, MainData, ParentDataWitness},
    param::HASH_WIDTH,
    rlp_gadgets::RLPItemWitness,
    witness_row::{AccountRowType, Node},
};
use crate::{
    circuit,
    circuit_tools::{
        cached_region::{CachedRegion, ChallengeSet},
        cell_manager::Cell,
        constraint_builder::{RLCChainable, RLCable, RLCableValue},
        gadgets::IsEqualGadget,
    },
    mpt_circuit::{
        helpers::{
            key_memory, main_memory, num_nibbles, parent_memory, DriftedGadget, Indexable,
            IsEmptyTreeGadget, KeyData, MPTConstraintBuilder, ParentData, WrongGadget, KECCAK,
        },
        param::{KEY_LEN_IN_NIBBLES, RLP_LIST_LONG, RLP_LONG},
        MPTConfig, MPTContext, MPTState,
    },
    table::MPTProofType,
    witness::MptUpdateRow,
};

#[derive(Clone, Debug, Default)]
pub(crate) struct AccountLeafConfig<F> {
    main_data: MainData<F>,
    key_data: [KeyData<F>; 2],
    parent_data: [ParentData<F>; 2],
    rlp_key: [ListKeyGadget<F>; 2],
    value_rlp_bytes: [[Cell<F>; 2]; 2],
    value_list_rlp_bytes: [[Cell<F>; 2]; 2],
    is_in_empty_trie: [IsEmptyTreeGadget<F>; 2],
    drifted: DriftedGadget<F>,
    wrong: WrongGadget<F>,
    is_non_existing_account_proof: IsEqualGadget<F>,
    is_account_delete_mod: IsEqualGadget<F>,
    is_nonce_mod: IsEqualGadget<F>,
    is_balance_mod: IsEqualGadget<F>,
    is_storage_mod: IsEqualGadget<F>,
    is_codehash_mod: IsEqualGadget<F>,
}

impl<F: Field> AccountLeafConfig<F> {
    pub fn configure(
        meta: &mut VirtualCells<'_, F>,
        cb: &mut MPTConstraintBuilder<F>,
        ctx: MPTContext<F>,
    ) -> Self {
        let r = ctx.r.clone();

        cb.base
            .cell_manager
            .as_mut()
            .unwrap()
            .reset(AccountRowType::Count as usize);
        let mut config = AccountLeafConfig::default();

        circuit!([meta, cb], {
            let key_items = [
                ctx.rlp_item(meta, cb, AccountRowType::KeyS as usize, false),
                ctx.rlp_item(meta, cb, AccountRowType::KeyC as usize, false),
            ];
            config.value_rlp_bytes = [cb.query_bytes(), cb.query_bytes()];
            config.value_list_rlp_bytes = [cb.query_bytes(), cb.query_bytes()];
            let nonce_items = [
                ctx.rlp_item(meta, cb, AccountRowType::NonceS as usize, false),
                ctx.rlp_item(meta, cb, AccountRowType::NonceC as usize, false),
            ];
            let balance_items = [
                ctx.rlp_item(meta, cb, AccountRowType::BalanceS as usize, false),
                ctx.rlp_item(meta, cb, AccountRowType::BalanceC as usize, false),
            ];
            let storage_items = [
                ctx.rlp_item(meta, cb, AccountRowType::StorageS as usize, false),
                ctx.rlp_item(meta, cb, AccountRowType::StorageC as usize, false),
            ];
            let codehash_items = [
                ctx.rlp_item(meta, cb, AccountRowType::CodehashS as usize, false),
                ctx.rlp_item(meta, cb, AccountRowType::CodehashC as usize, false),
            ];
            let drifted_bytes = ctx.rlp_item(meta, cb, AccountRowType::Drifted as usize, false);
            let wrong_bytes = ctx.rlp_item(meta, cb, AccountRowType::Wrong as usize, false);

            config.main_data =
                MainData::load("main storage", cb, &ctx.memory[main_memory()], 0.expr());

            // Don't allow an account node to follow an account node
            require!(config.main_data.is_below_account => false);

            let mut key_rlc = vec![0.expr(); 2];
            let mut nonce_rlc = vec![0.expr(); 2];
            let mut balance_rlc = vec![0.expr(); 2];
            let mut storage_rlc = vec![0.expr(); 2];
            let mut codehash_rlc = vec![0.expr(); 2];
            let mut leaf_no_key_rlc = vec![0.expr(); 2];
            for is_s in [true, false] {
                // Key data
                let key_data = &mut config.key_data[is_s.idx()];
                *key_data = KeyData::load(cb, &ctx.memory[key_memory(is_s)], 0.expr());

                // Parent data
                let parent_data = &mut config.parent_data[is_s.idx()];
                *parent_data = ParentData::load(
                    "account load",
                    cb,
                    &ctx.memory[parent_memory(is_s)],
                    0.expr(),
                );

                // Placeholder leaf checks
                config.is_in_empty_trie[is_s.idx()] =
                    IsEmptyTreeGadget::construct(cb, parent_data.rlc.expr(), &r);

                // Calculate the key RLC
                let rlp_key = &mut config.rlp_key[is_s.idx()];
                *rlp_key = ListKeyGadget::construct(cb, &key_items[is_s.idx()]);

                // Storage root and codehash are always 32-byte hashes.
                require!(storage_items[is_s.idx()].len() => HASH_WIDTH);
                require!(codehash_items[is_s.idx()].len() => HASH_WIDTH);

                // Multiplier after list and key
                let mult = rlp_key.rlp_list.rlp_mult(&r) * key_items[is_s.idx()].mult();

                let nonce_rlp_rlc;
                let balance_rlp_rlc;
                let storage_rlp_rlc;
                let codehash_rlp_rlc;
                (nonce_rlc[is_s.idx()], nonce_rlp_rlc) = nonce_items[is_s.idx()].rlc();
                (balance_rlc[is_s.idx()], balance_rlp_rlc) = balance_items[is_s.idx()].rlc();
                (storage_rlc[is_s.idx()], storage_rlp_rlc) = storage_items[is_s.idx()].rlc();
                (codehash_rlc[is_s.idx()], codehash_rlp_rlc) = codehash_items[is_s.idx()].rlc();

                // Calculate the leaf RLC
                let value_rlp_bytes = config.value_rlp_bytes[is_s.idx()].to_expr_vec();
                let value_list_rlp_bytes = config.value_list_rlp_bytes[is_s.idx()].to_expr_vec();
                leaf_no_key_rlc[is_s.idx()] = (value_rlp_bytes.rlc(&r), pow::expr(r.expr(), 2))
                    .rlc_chain(
                        (value_list_rlp_bytes.rlc(&r), pow::expr(r.expr(), 2)).rlc_chain(
                            (nonce_rlp_rlc.expr(), nonce_items[is_s.idx()].mult()).rlc_chain(
                                (balance_rlp_rlc.expr(), balance_items[is_s.idx()].mult())
                                    .rlc_chain(
                                        (storage_rlp_rlc.expr(), pow::expr(r.expr(), 33))
                                            .rlc_chain(codehash_rlp_rlc.expr()),
                                    ),
                            ),
                        ),
                    );
                let leaf_rlc =
                    (rlp_key.rlc(&r), mult.expr()).rlc_chain(leaf_no_key_rlc[is_s.idx()].expr());

                // Key
                key_rlc[is_s.idx()] = key_data.rlc.expr()
                    + rlp_key.key.expr(
                        cb,
                        rlp_key.key_value.clone(),
                        key_data.mult.expr(),
                        key_data.is_odd.expr(),
                        &r,
                    );
                // Total number of nibbles needs to be KEY_LEN_IN_NIBBLES.
                let num_nibbles =
                    num_nibbles::expr(rlp_key.key_value.len(), key_data.is_odd.expr());
                require!(key_data.num_nibbles.expr() + num_nibbles.expr() => KEY_LEN_IN_NIBBLES);

                // Check if the account is in its parent.
                // Check is skipped for placeholder leaves which are dummy leaves
                ifx! {not!(and::expr(&[not!(config.parent_data[is_s.idx()].is_placeholder), config.is_in_empty_trie[is_s.idx()].expr()])) => {
                    require!((1, leaf_rlc, rlp_key.rlp_list.num_bytes(), config.parent_data[is_s.idx()].rlc) => @KECCAK);
                }}

                // Check the RLP encoding consistency.
                // RLP encoding: account = [key, "[nonce, balance, storage, codehash]"]
                // We always store between 55 and 256 bytes of data in the values list.
                require!(value_rlp_bytes[0] => RLP_LONG + 1);
                // The RLP encoded list always has 2 RLP bytes.
                require!(value_rlp_bytes[1] => value_list_rlp_bytes[1].expr() + 2.expr());
                // The first RLP byte of the list is always RLP_LIST_LONG + 1.
                require!(value_list_rlp_bytes[0] => RLP_LIST_LONG + 1);
                // The length of the list is `#(nonce) + #(balance) + 2 * (1 + #(hash))`.
                require!(value_list_rlp_bytes[1] => nonce_items[is_s.idx()].num_bytes() + balance_items[is_s.idx()].num_bytes() + (2 * (1 + 32)).expr());
                // Now check that the the key and value list length matches the account length.
                // The RLP encoded string always has 2 RLP bytes.
                let value_list_num_bytes = value_rlp_bytes[1].expr() + 2.expr();
                // Account length needs to equal all key bytes and all values list bytes.
                require!(config.rlp_key[is_s.idx()].rlp_list.len() => config.rlp_key[is_s.idx()].key_value.num_bytes() + value_list_num_bytes);

                // Key done, set the starting values
                KeyData::store_defaults(cb, &ctx.memory[key_memory(is_s)]);
                // Store the new parent
                ParentData::store(
                    cb,
                    &ctx.memory[parent_memory(is_s)],
                    storage_rlc[is_s.idx()].expr(),
                    true.expr(),
                    false.expr(),
                    storage_rlc[is_s.idx()].expr(),
                );
            }

            // Anything following this node is below the account
            // TODO(Brecht): For non-existing accounts it should be impossible to prove
            // storage leaves unless it's also a non-existing proof?
            MainData::store(
                cb,
                &ctx.memory[main_memory()],
                [
                    config.main_data.proof_type.expr(),
                    true.expr(),
                    key_rlc[true.idx()].expr(),
                    config.main_data.root_prev.expr(),
                    config.main_data.root.expr(),
                ],
            );

            // Proof types
            config.is_non_existing_account_proof = IsEqualGadget::construct(
                &mut cb.base,
                config.main_data.proof_type.expr(),
                MPTProofType::AccountDoesNotExist.expr(),
            );
            config.is_account_delete_mod = IsEqualGadget::construct(
                &mut cb.base,
                config.main_data.proof_type.expr(),
                MPTProofType::AccountDestructed.expr(),
            );
            config.is_nonce_mod = IsEqualGadget::construct(
                &mut cb.base,
                config.main_data.proof_type.expr(),
                MPTProofType::NonceChanged.expr(),
            );
            config.is_balance_mod = IsEqualGadget::construct(
                &mut cb.base,
                config.main_data.proof_type.expr(),
                MPTProofType::BalanceChanged.expr(),
            );
            config.is_storage_mod = IsEqualGadget::construct(
                &mut cb.base,
                config.main_data.proof_type.expr(),
                MPTProofType::StorageChanged.expr(),
            );
            config.is_codehash_mod = IsEqualGadget::construct(
                &mut cb.base,
                config.main_data.proof_type.expr(),
                MPTProofType::CodeHashExists.expr(),
            );

            // Drifted leaf handling
            config.drifted = DriftedGadget::construct(
                cb,
                &config.parent_data,
                &config.key_data,
                &key_rlc,
                &leaf_no_key_rlc,
                &drifted_bytes,
                &ctx.r,
            );

            // Wrong leaf handling
            config.wrong = WrongGadget::construct(
                cb,
                a!(ctx.mpt_table.address_rlc),
                config.is_non_existing_account_proof.expr(),
                &config.rlp_key[true.idx()].key_value,
                &key_rlc[true.idx()],
                &wrong_bytes,
                config.is_in_empty_trie[true.idx()].expr(),
                config.key_data[true.idx()].clone(),
                &ctx.r,
            );

            ifx! {config.is_account_delete_mod => {
                // Account delete
                // We need to make sure there is no leaf when account is deleted. Two possible
                // cases:
                // - 1. Account leaf is deleted and there is a nil object in
                // branch. In this case we have a placeholder leaf.
                // - 2. Account leaf is deleted from a branch with two leaves, the remaining
                // leaf moves one level up and replaces the branch. In this case we
                // have a branch placeholder.
                // TODO(Brecht): For case 2: just having the parent branch be the placeholder seems not enough
                require!(or::expr([
                    config.is_in_empty_trie[false.idx()].expr(),
                    config.parent_data[false.idx()].is_placeholder.expr()
                ]) => true);
            } elsex {
                // Check that there is only one modification (except when the account is being deleted).
                // Nonce needs to remain the same when not modifying the nonce
                ifx!{not!(config.is_nonce_mod) => {
                    require!(nonce_rlc[false.idx()] => nonce_rlc[true.idx()]);
                }}
                // Balance needs to remain the same when not modifying the balance
                ifx!{not!(config.is_balance_mod) => {
                    require!(balance_rlc[false.idx()] => balance_rlc[true.idx()]);
                }}
                // Storage root needs to remain the same when not modifying the storage root
                ifx!{not!(config.is_storage_mod) => {
                    require!(storage_rlc[false.idx()] => storage_rlc[true.idx()]);
                }}
                // Codehash root needs to remain the same when not modifying the codehash
                ifx!{not!(config.is_codehash_mod) => {
                    require!(codehash_rlc[false.idx()] => codehash_rlc[true.idx()]);
                }}
            }}
            ifx! {config.is_non_existing_account_proof => {
                // For non-existing proofs the tree needs to remain the same
                require!(config.main_data.root => config.main_data.root_prev);
                require!(key_rlc[true.idx()] => key_rlc[false.idx()]);
            }}

            // Put the data in the lookup table
            let (proof_type, value_prev, value) = _matchx! {cb,
                config.is_nonce_mod => (MPTProofType::NonceChanged.expr(), nonce_rlc[true.idx()].expr(), nonce_rlc[false.idx()].expr()),
                config.is_balance_mod => (MPTProofType::BalanceChanged.expr(), balance_rlc[true.idx()].expr(), balance_rlc[false.idx()].expr()),
                config.is_storage_mod => (MPTProofType::StorageChanged.expr(), storage_rlc[true.idx()].expr(), storage_rlc[false.idx()].expr()),
                config.is_codehash_mod => (MPTProofType::CodeHashExists.expr(), codehash_rlc[true.idx()].expr(), codehash_rlc[false.idx()].expr()),
                config.is_account_delete_mod => (MPTProofType::AccountDestructed.expr(), 0.expr(), 0.expr()),
                config.is_non_existing_account_proof => (MPTProofType::AccountDoesNotExist.expr(), 0.expr(), 0.expr()),
                _ => (MPTProofType::Disabled.expr(), 0.expr(), 0.expr()),
            };
            let address_rlc = ifx! {config.is_non_existing_account_proof => {
                a!(ctx.mpt_table.address_rlc)
            } elsex {
                ifx!{not!(config.parent_data[true.idx()].is_placeholder) => {
                    key_rlc[true.idx()].expr()
                } elsex {
                    key_rlc[false.idx()].expr()
                }}
            }};
            ctx.mpt_table.constrain(
                meta,
                &mut cb.base,
                address_rlc,
                proof_type,
                0.expr(),
                value_prev,
                value,
                config.main_data.root_prev.expr(),
                config.main_data.root.expr(),
            );
        });

        config
    }

    #[allow(clippy::too_many_arguments)]
    pub fn assign<S: ChallengeSet<F>>(
        &self,
        region: &mut CachedRegion<'_, '_, F, S>,
        _challenges: &S,
        mpt_config: &MPTConfig<F>,
        pv: &mut MPTState<F>,
        offset: usize,
        node: &Node,
        rlp_values: &[RLPItemWitness],
    ) -> Result<(), Error> {
        let account = &node.account.clone().unwrap();

        let key_items = [
            rlp_values[AccountRowType::KeyS as usize].clone(),
            rlp_values[AccountRowType::KeyC as usize].clone(),
        ];
        let nonce_items = [
            rlp_values[AccountRowType::NonceS as usize].clone(),
            rlp_values[AccountRowType::NonceC as usize].clone(),
        ];
        let balance_items = [
            rlp_values[AccountRowType::BalanceS as usize].clone(),
            rlp_values[AccountRowType::BalanceC as usize].clone(),
        ];
        let storage_items = [
            rlp_values[AccountRowType::StorageS as usize].clone(),
            rlp_values[AccountRowType::StorageC as usize].clone(),
        ];
        let codehash_items = [
            rlp_values[AccountRowType::CodehashS as usize].clone(),
            rlp_values[AccountRowType::CodehashC as usize].clone(),
        ];
        let drifted_item = rlp_values[AccountRowType::Drifted as usize].clone();
        let wrong_item = rlp_values[AccountRowType::Wrong as usize].clone();

        let main_data =
            self.main_data
                .witness_load(region, offset, &pv.memory[main_memory()], 0)?;

        // Key
        let mut key_rlc = vec![0.scalar(); 2];
        let mut nonce_rlc = vec![0.scalar(); 2];
        let mut balance_rlc = vec![0.scalar(); 2];
        let mut storage_rlc = vec![0.scalar(); 2];
        let mut codehash_rlc = vec![0.scalar(); 2];
        let mut key_data = vec![KeyDataWitness::default(); 2];
        let mut parent_data = vec![ParentDataWitness::default(); 2];
        for is_s in [true, false] {
            for (cell, byte) in self.value_rlp_bytes[is_s.idx()]
                .iter()
                .zip(account.value_rlp_bytes[is_s.idx()].iter())
            {
                cell.assign(region, offset, byte.scalar())?;
            }

            for (cell, byte) in self.value_list_rlp_bytes[is_s.idx()]
                .iter()
                .zip(account.value_list_rlp_bytes[is_s.idx()].iter())
            {
                cell.assign(region, offset, byte.scalar())?;
            }

            key_data[is_s.idx()] = self.key_data[is_s.idx()].witness_load(
                region,
                offset,
                &pv.memory[key_memory(is_s)],
                0,
            )?;

            parent_data[is_s.idx()] = self.parent_data[is_s.idx()].witness_load(
                region,
                offset,
                &pv.memory[parent_memory(is_s)],
                0,
            )?;

            self.is_in_empty_trie[is_s.idx()].assign(
                region,
                offset,
                parent_data[is_s.idx()].rlc,
                pv.r,
            )?;

            let rlp_key_witness = self.rlp_key[is_s.idx()].assign(
                region,
                offset,
                &account.list_rlp_bytes[is_s.idx()],
                &key_items[is_s.idx()],
            )?;

            nonce_rlc[is_s.idx()] = nonce_items[is_s.idx()].rlc_content(pv.r);
            balance_rlc[is_s.idx()] = balance_items[is_s.idx()].rlc_content(pv.r);
            storage_rlc[is_s.idx()] = storage_items[is_s.idx()].rlc_content(pv.r);
            codehash_rlc[is_s.idx()] = codehash_items[is_s.idx()].rlc_content(pv.r);

            // Key
            (key_rlc[is_s.idx()], _) = rlp_key_witness.key.key(
                rlp_key_witness.key_item.clone(),
                key_data[is_s.idx()].rlc,
                key_data[is_s.idx()].mult,
                pv.r,
            );

            // Update key and parent state
            KeyData::witness_store(
                region,
                offset,
                &mut pv.memory[key_memory(is_s)],
                F::ZERO,
                F::ONE,
                0,
                F::ZERO,
                F::ONE,
                0,
            )?;
            ParentData::witness_store(
                region,
                offset,
                &mut pv.memory[parent_memory(is_s)],
                storage_rlc[is_s.idx()],
                true,
                false,
                storage_rlc[is_s.idx()],
            )?;
        }

        // Anything following this node is below the account
        MainData::witness_store(
            region,
            offset,
            &mut pv.memory[main_memory()],
            main_data.proof_type,
            true,
            account.address.rlc_value(pv.r),
            main_data.root_prev,
            main_data.root,
        )?;

        // Proof types
        let is_non_existing_proof = self.is_non_existing_account_proof.assign(
            region,
            offset,
            main_data.proof_type.scalar(),
            MPTProofType::AccountDoesNotExist.scalar(),
        )? == true.scalar();
        let is_account_delete_mod = self.is_account_delete_mod.assign(
            region,
            offset,
            main_data.proof_type.scalar(),
            MPTProofType::AccountDestructed.scalar(),
        )? == true.scalar();
        let is_nonce_mod = self.is_nonce_mod.assign(
            region,
            offset,
            main_data.proof_type.scalar(),
            MPTProofType::NonceChanged.scalar(),
        )? == true.scalar();
        let is_balance_mod = self.is_balance_mod.assign(
            region,
            offset,
            main_data.proof_type.scalar(),
            MPTProofType::BalanceChanged.scalar(),
        )? == true.scalar();
        let is_storage_mod = self.is_storage_mod.assign(
            region,
            offset,
            main_data.proof_type.scalar(),
            MPTProofType::StorageChanged.scalar(),
        )? == true.scalar();
        let is_codehash_mod = self.is_codehash_mod.assign(
            region,
            offset,
            main_data.proof_type.scalar(),
            MPTProofType::CodeHashExists.scalar(),
        )? == true.scalar();

        // Drifted leaf handling
        self.drifted.assign(
            region,
            offset,
            &parent_data,
            &account.drifted_rlp_bytes,
            &drifted_item,
            pv.r,
        )?;

        // Wrong leaf handling
        self.wrong.assign(
            region,
            offset,
            is_non_existing_proof,
            &key_rlc,
            &account.wrong_rlp_bytes,
            &wrong_item,
            true,
            key_data[true.idx()].clone(),
            pv.r,
        )?;

        // Put the data in the lookup table
        let (proof_type, value) = if is_nonce_mod {
            (MPTProofType::NonceChanged, nonce_rlc)
        } else if is_balance_mod {
            (MPTProofType::BalanceChanged, balance_rlc)
        } else if is_storage_mod {
            (MPTProofType::StorageChanged, storage_rlc)
        } else if is_codehash_mod {
            (MPTProofType::CodeHashExists, codehash_rlc)
        } else if is_account_delete_mod {
            (MPTProofType::AccountDestructed, vec![0.scalar(); 2])
        } else if is_non_existing_proof {
            (MPTProofType::AccountDoesNotExist, vec![0.scalar(); 2])
        } else {
            (MPTProofType::Disabled, vec![0.scalar(); 2])
        };
        mpt_config.mpt_table.assign_cached(
            region,
            offset,
            &MptUpdateRow {
                address_rlc: Value::known(account.address.rlc_value(pv.r)),
                proof_type: Value::known(proof_type.scalar()),
                key_rlc: Value::known(0.scalar()),
                value_prev: Value::known(value[true.idx()]),
                value: Value::known(value[false.idx()]),
                root_prev: Value::known(main_data.root_prev),
                root: Value::known(main_data.root),
            },
        )?;

        Ok(())
    }
}
