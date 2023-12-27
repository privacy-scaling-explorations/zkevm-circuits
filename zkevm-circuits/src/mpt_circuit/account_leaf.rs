use eth_types::Field;
use gadgets::util::{pow, Scalar};
use halo2_proofs::{
    circuit::Value,
    plonk::{Error, Expression, VirtualCells},
};

use super::{
    helpers::{KeyDataWitness, ListKeyGadget, MainData, ParentDataWitness},
    mod_extension::ModExtensionGadget,
    rlp_gadgets::RLPItemWitness,
    witness_row::{AccountRowType, Node},
};
use crate::{
    circuit,
    circuit_tools::{
        cached_region::CachedRegion,
        cell_manager::Cell,
        constraint_builder::{RLCChainableRev, RLCable},
        gadgets::IsEqualGadget,
    },
    evm_circuit::util::from_bytes,
    mpt_circuit::{
        helpers::{
            key_memory, main_memory, num_nibbles, parent_memory, DriftedGadget, Indexable,
            IsPlaceholderLeafGadget, KeyData, MPTConstraintBuilder, ParentData, WrongGadget,
            KECCAK,
        },
        param::{KEY_LEN_IN_NIBBLES, RLP_LIST_LONG, RLP_LONG},
        MPTConfig, MPTContext, MptMemory, RlpItemType,
    },
    table::MPTProofType,
    util::word::{self, Word},
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
    is_placeholder_leaf: [IsPlaceholderLeafGadget<F>; 2],
    drifted: DriftedGadget<F>,
    wrong: WrongGadget<F>,
    is_non_existing_account_proof: IsEqualGadget<F>,
    is_account_delete_mod: IsEqualGadget<F>,
    is_nonce_mod: IsEqualGadget<F>,
    is_balance_mod: IsEqualGadget<F>,
    is_storage_mod: IsEqualGadget<F>,
    is_codehash_mod: IsEqualGadget<F>,
    is_mod_extension: [Cell<F>; 2],
    mod_extension: ModExtensionGadget<F>,
}

impl<F: Field> AccountLeafConfig<F> {
    pub fn configure(
        meta: &mut VirtualCells<'_, F>,
        cb: &mut MPTConstraintBuilder<F>,
        ctx: &mut MPTContext<F>,
    ) -> Self {
        let mut config = AccountLeafConfig::default();

        circuit!([meta, cb], {
            let key_items = [
                ctx.rlp_item(meta, cb, AccountRowType::KeyS as usize, RlpItemType::Key),
                ctx.rlp_item(meta, cb, AccountRowType::KeyC as usize, RlpItemType::Key),
            ];
            config.value_rlp_bytes = [cb.query_bytes(), cb.query_bytes()];
            config.value_list_rlp_bytes = [cb.query_bytes(), cb.query_bytes()];
            let nonce_items = [
                ctx.rlp_item(
                    meta,
                    cb,
                    AccountRowType::NonceS as usize,
                    RlpItemType::Value,
                ),
                ctx.rlp_item(
                    meta,
                    cb,
                    AccountRowType::NonceC as usize,
                    RlpItemType::Value,
                ),
            ];
            let balance_items = [
                ctx.rlp_item(
                    meta,
                    cb,
                    AccountRowType::BalanceS as usize,
                    RlpItemType::Value,
                ),
                ctx.rlp_item(
                    meta,
                    cb,
                    AccountRowType::BalanceC as usize,
                    RlpItemType::Value,
                ),
            ];
            let storage_items = [
                ctx.rlp_item(
                    meta,
                    cb,
                    AccountRowType::StorageS as usize,
                    RlpItemType::Hash,
                ),
                ctx.rlp_item(
                    meta,
                    cb,
                    AccountRowType::StorageC as usize,
                    RlpItemType::Hash,
                ),
            ];
            let codehash_items = [
                ctx.rlp_item(
                    meta,
                    cb,
                    AccountRowType::CodehashS as usize,
                    RlpItemType::Hash,
                ),
                ctx.rlp_item(
                    meta,
                    cb,
                    AccountRowType::CodehashC as usize,
                    RlpItemType::Hash,
                ),
            ];
            let drifted_bytes =
                ctx.rlp_item(meta, cb, AccountRowType::Drifted as usize, RlpItemType::Key);
            let wrong_bytes =
                ctx.rlp_item(meta, cb, AccountRowType::Wrong as usize, RlpItemType::Key);
            let address_item = ctx.rlp_item(
                meta,
                cb,
                AccountRowType::Address as usize,
                RlpItemType::Address,
            );
            let key_item = ctx.rlp_item(meta, cb, AccountRowType::Key as usize, RlpItemType::Hash);

            for is_s in [true, false] {
                config.is_mod_extension[is_s.idx()] = cb.query_bool();
            }

            config.main_data = MainData::load(cb, &mut ctx.memory[main_memory()], 0.expr());

            // Don't allow an account node to follow an account node
            require!(config.main_data.is_below_account => false);

            let mut key_rlc = vec![0.expr(); 2];
            let mut nonce = vec![Word::<Expression<F>>::new([0.expr(), 0.expr()]); 2];
            let mut balance = vec![Word::<Expression<F>>::new([0.expr(), 0.expr()]); 2];
            let mut storage = vec![Word::<Expression<F>>::new([0.expr(), 0.expr()]); 2];
            let mut codehash = vec![Word::<Expression<F>>::new([0.expr(), 0.expr()]); 2];
            let mut leaf_no_key_rlc = vec![0.expr(); 2];
            let mut leaf_no_key_rlc_mult = vec![0.expr(); 2];
            let mut value_list_num_bytes = vec![0.expr(); 2];

            let parent_data = &mut config.parent_data;
            parent_data[0] = ParentData::load(cb, &mut ctx.memory[parent_memory(true)], 0.expr());
            parent_data[1] = ParentData::load(cb, &mut ctx.memory[parent_memory(false)], 0.expr());

            let key_data = &mut config.key_data;
            key_data[0] = KeyData::load(cb, &mut ctx.memory[key_memory(true)], 0.expr());
            key_data[1] = KeyData::load(cb, &mut ctx.memory[key_memory(false)], 0.expr());

            for is_s in [true, false] {
                ifx! {not!(config.is_mod_extension[is_s.idx()].expr()) => {
                    // Placeholder leaf checks
                    config.is_placeholder_leaf[is_s.idx()] =
                        IsPlaceholderLeafGadget::construct(cb, parent_data[is_s.idx()].hash.expr());

                    // Calculate the key RLC
                    let rlp_key = &mut config.rlp_key[is_s.idx()];
                    *rlp_key = ListKeyGadget::construct(cb, &key_items[is_s.idx()]);

                    let nonce_rlp_rlc;
                    let balance_rlp_rlc;
                    let storage_rlp_rlc;
                    let codehash_rlp_rlc;
                    (nonce[is_s.idx()], nonce_rlp_rlc) = (
                        nonce_items[is_s.idx()].word(),
                        nonce_items[is_s.idx()].rlc_chain_data(),
                    );
                    (balance[is_s.idx()], balance_rlp_rlc) = (
                        balance_items[is_s.idx()].word(),
                        balance_items[is_s.idx()].rlc_chain_data(),
                    );
                    (storage[is_s.idx()], storage_rlp_rlc) = (
                        storage_items[is_s.idx()].word(),
                        storage_items[is_s.idx()].rlc_chain_data(),
                    );
                    (codehash[is_s.idx()], codehash_rlp_rlc) = (
                        codehash_items[is_s.idx()].word(),
                        codehash_items[is_s.idx()].rlc_chain_data(),
                    );

                    // Calculate the leaf RLC
                    let keccak_r = &cb.keccak_r;
                    let value_rlp_bytes = config.value_rlp_bytes[is_s.idx()].to_expr_vec();
                    let value_list_rlp_bytes = config.value_list_rlp_bytes[is_s.idx()].to_expr_vec();
                    leaf_no_key_rlc[is_s.idx()] = value_rlp_bytes
                        .rlc_rev(keccak_r)
                        .rlc_chain_rev((
                            value_list_rlp_bytes.rlc_rev(keccak_r),
                            pow::expr(keccak_r.expr(), 2),
                        ))
                        .rlc_chain_rev(nonce_rlp_rlc.clone())
                        .rlc_chain_rev(balance_rlp_rlc.clone())
                        .rlc_chain_rev(storage_rlp_rlc.clone())
                        .rlc_chain_rev(codehash_rlp_rlc.clone());
                    leaf_no_key_rlc_mult[is_s.idx()] = pow::expr(keccak_r.expr(), 4)
                        * nonce_rlp_rlc.1
                        * balance_rlp_rlc.1
                        * storage_rlp_rlc.1
                        * codehash_rlp_rlc.1;
                    let leaf_rlc = rlp_key.rlc2(&cb.keccak_r).rlc_chain_rev((
                        leaf_no_key_rlc[is_s.idx()].expr(),
                        leaf_no_key_rlc_mult[is_s.idx()].expr(),
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
                    // Total number of nibbles needs to be KEY_LEN_IN_NIBBLES.
                    let num_nibbles =
                        num_nibbles::expr(rlp_key.key_value.len(), key_data[is_s.idx()].is_odd.expr());
                    require!(key_data[is_s.idx()].num_nibbles.expr() + num_nibbles.expr() => KEY_LEN_IN_NIBBLES);

                    // Check if the account is in its parent.
                    // Check is skipped for placeholder leaves which are dummy leaves
                    ifx! {not!(and::expr(&[not!(parent_data[is_s.idx()].is_placeholder), config.is_placeholder_leaf[is_s.idx()].expr()])) => {
                        let hash = parent_data[is_s.idx()].hash.expr();
                        require!((1.expr(), leaf_rlc, rlp_key.rlp_list.num_bytes(), hash.lo(), hash.hi()) =>> @KECCAK);
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
                    value_list_num_bytes[is_s.idx()] = value_rlp_bytes[1].expr() + 2.expr();

                    // Account length needs to equal all key bytes and all values list bytes.
                    require!(config.rlp_key[is_s.idx()].rlp_list.len() => config.rlp_key[is_s.idx()].key_value.num_bytes() + value_list_num_bytes[is_s.idx()].expr());
                }};

                // Key done, set the starting values
                KeyData::store_defaults(cb, &mut ctx.memory[key_memory(is_s)]);
                // Store the new parent
                ParentData::store(
                    cb,
                    &mut ctx.memory[parent_memory(is_s)],
                    storage_items[is_s.idx()].word(),
                    0.expr(),
                    true.expr(),
                    false.expr(),
                    storage_items[is_s.idx()].word(),
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
                MPTProofType::CodeHashChanged.expr(),
            );

            // Drifted leaf handling
            config.drifted = DriftedGadget::construct(
                cb,
                &value_list_num_bytes,
                &config.parent_data,
                &config.key_data,
                &key_rlc,
                &leaf_no_key_rlc,
                &leaf_no_key_rlc_mult,
                &drifted_bytes,
                &config.is_mod_extension,
                &cb.key_r.expr(),
            );

            // Wrong leaf handling
            config.wrong = WrongGadget::construct(
                cb,
                key_item.hash_rlc(),
                config.is_non_existing_account_proof.expr(),
                &config.rlp_key[true.idx()].key_value,
                &key_rlc[true.idx()],
                &wrong_bytes,
                config.is_placeholder_leaf[true.idx()].expr(),
                config.key_data[true.idx()].clone(),
                &cb.key_r.expr(),
            );

            // Anything following this node is below the account
            // TODO(Brecht): For non-existing accounts it should be impossible to prove
            // storage leaves unless it's also a non-existing proof?
            MainData::store(
                cb,
                &mut ctx.memory[main_memory()],
                [
                    config.main_data.proof_type.expr(),
                    true.expr(),
                    address_item.word().lo()
                        + address_item.word().hi() * pow::value::<F>(256.scalar(), 16),
                    config.main_data.new_root.lo().expr(),
                    config.main_data.new_root.hi().expr(),
                    config.main_data.old_root.lo().expr(),
                    config.main_data.old_root.hi().expr(),
                ],
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
                require!(or::expr([
                    config.is_placeholder_leaf[false.idx()].expr(),
                    config.parent_data[false.idx()].is_placeholder.expr()
                ]) => true);
            } elsex {
                ifx! {and::expr(&[not!(config.parent_data[true.idx()].is_placeholder), not!(config.parent_data[false.idx()].is_placeholder)]) => {
                    // Check that there is only one modification, except when the account is being deleted or
                    // the parent branch is a placeholder (meaning the account leafs in S are C are different).
                    // Nonce needs to remain the same when not modifying the nonce
                    ifx!{not!(config.is_nonce_mod) => {
                        require!(nonce[false.idx()] => nonce[true.idx()]);
                    }}
                    // Balance needs to remain the same when not modifying the balance
                    ifx!{not!(config.is_balance_mod) => {
                        require!(balance[false.idx()] => balance[true.idx()]);
                    }}
                    // Storage root needs to remain the same when not modifying the storage root
                    ifx!{not!(config.is_storage_mod) => {
                        require!(storage[false.idx()] => storage[true.idx()]);
                    }}
                    // Codehash root needs to remain the same when not modifying the codehash
                    ifx!{not!(config.is_codehash_mod) => {
                        require!(codehash[false.idx()] => codehash[true.idx()]);
                    }}
                }}
            }}
            ifx! {config.is_non_existing_account_proof => {
                // For non-existing proofs the tree needs to remain the same
                require!(config.main_data.new_root => config.main_data.old_root);
                require!(key_rlc[true.idx()] => key_rlc[false.idx()]);
            }}

            // Put the data in the lookup table
            let (proof_type, old_value_lo, old_value_hi, new_value_lo, new_value_hi) = _matchx! {cb, (
                config.is_nonce_mod => (MPTProofType::NonceChanged.expr(), nonce[true.idx()].lo(), nonce[true.idx()].hi(), nonce[false.idx()].lo(), nonce[false.idx()].hi()),
                config.is_balance_mod => (MPTProofType::BalanceChanged.expr(), balance[true.idx()].lo(), balance[true.idx()].hi(), balance[false.idx()].lo(), balance[false.idx()].hi()),
                config.is_storage_mod => (MPTProofType::StorageChanged.expr(), storage[true.idx()].lo(), storage[true.idx()].hi(), storage[false.idx()].lo(), storage[false.idx()].hi()),
                config.is_codehash_mod => (MPTProofType::CodeHashChanged.expr(), codehash[true.idx()].lo(), codehash[true.idx()].hi(), codehash[false.idx()].lo(), codehash[false.idx()].hi()),
                config.is_account_delete_mod => (MPTProofType::AccountDestructed.expr(), 0.expr(), 0.expr(), 0.expr(), 0.expr()),
                config.is_non_existing_account_proof => (MPTProofType::AccountDoesNotExist.expr(), 0.expr(), 0.expr(), 0.expr(), 0.expr()),
                _ => (MPTProofType::Disabled.expr(), 0.expr(), 0.expr(), 0.expr(), 0.expr()),
            )};
            ifx! {not!(config.is_non_existing_account_proof) => {
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
                    require!((1.expr(), address_item.bytes_le()[1..21].rlc(&cb.keccak_r), 20.expr(), key.lo(), key.hi()) =>> @KECCAK);
                }
            }};
            let to_hi = Expression::<F>::Constant(pow::value::<F>(256.scalar(), 16));
            let lo = address_item.word().lo();
            let hi = address_item.word().hi() * to_hi;
            let address = lo + hi;

            ifx! {not!(config.parent_data[false.idx()].is_placeholder) => {
                ctx.mpt_table.constrain(
                    meta,
                    &mut cb.base,
                    address.clone(),
                    proof_type.clone(),
                    Word::<Expression<F>>::new([0.expr(), 0.expr()]),
                    config.main_data.new_root.expr(),
                    config.main_data.old_root.expr(),
                    Word::<Expression<F>>::new([new_value_lo, new_value_hi]),
                    Word::<Expression<F>>::new([old_value_lo.clone(), old_value_hi.clone()]),
                );
            } elsex {
                ctx.mpt_table.constrain(
                    meta,
                    &mut cb.base,
                    address,
                    proof_type,
                    Word::<Expression<F>>::new([0.expr(), 0.expr()]),
                    config.main_data.new_root.expr(),
                    config.main_data.old_root.expr(),
                    Word::<Expression<F>>::new([0.expr(), 0.expr()]),
                    Word::<Expression<F>>::new([old_value_lo, old_value_hi]),
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
        let expected_item = rlp_values[AccountRowType::Wrong as usize].clone();
        let address_item = rlp_values[AccountRowType::Address as usize].clone();
        let _key_item = rlp_values[AccountRowType::Key as usize].clone();

        let main_data =
            self.main_data
                .witness_load(region, offset, &mut memory[main_memory()], 0)?;

        // Key
        let mut key_rlc = vec![0.scalar(); 2];
        let mut nonce = vec![Word::<F>::new([0.scalar(), 0.scalar()]); 2];
        let mut balance = vec![Word::<F>::new([0.scalar(), 0.scalar()]); 2];
        let mut storage = vec![Word::<F>::new([0.scalar(), 0.scalar()]); 2];
        let mut codehash = vec![Word::<F>::new([0.scalar(), 0.scalar()]); 2];
        let mut key_data = vec![KeyDataWitness::default(); 2];
        let mut parent_data = vec![ParentDataWitness::default(); 2];
        for is_s in [true, false] {
            self.is_mod_extension[is_s.idx()].assign(
                region,
                offset,
                account.is_mod_extension[is_s.idx()].scalar(),
            )?;

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
                &mut memory[key_memory(is_s)],
                0,
            )?;

            parent_data[is_s.idx()] = self.parent_data[is_s.idx()].witness_load(
                region,
                offset,
                &mut memory[parent_memory(is_s)],
                0,
            )?;

            self.is_placeholder_leaf[is_s.idx()].assign(
                region,
                offset,
                parent_data[is_s.idx()].hash,
            )?;

            let rlp_key_witness = self.rlp_key[is_s.idx()].assign(
                region,
                offset,
                &account.list_rlp_bytes[is_s.idx()],
                &key_items[is_s.idx()],
            )?;

            nonce[is_s.idx()] = nonce_items[is_s.idx()].word();
            balance[is_s.idx()] = balance_items[is_s.idx()].word();
            storage[is_s.idx()] = storage_items[is_s.idx()].word();
            codehash[is_s.idx()] = codehash_items[is_s.idx()].word();

            // Key
            (key_rlc[is_s.idx()], _) = rlp_key_witness.key.key(
                rlp_key_witness.key_item.clone(),
                key_data[is_s.idx()].rlc,
                key_data[is_s.idx()].mult,
                region.key_r,
            );

            // Update key and parent state
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
            ParentData::witness_store(
                region,
                offset,
                &mut memory[parent_memory(is_s)],
                storage_items[is_s.idx()].word(),
                0.scalar(),
                true,
                false,
                storage_items[is_s.idx()].word(),
            )?;
        }

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
            MPTProofType::CodeHashChanged.scalar(),
        )? == true.scalar();
        // Drifted leaf handling
        self.drifted.assign(
            region,
            offset,
            &parent_data,
            &account.drifted_rlp_bytes,
            &drifted_item,
            region.key_r,
        )?;

        // Wrong leaf handling
        self.wrong.assign(
            region,
            offset,
            is_non_existing_proof,
            &key_rlc,
            &account.wrong_rlp_bytes,
            &expected_item,
            true,
            key_data[true.idx()].clone(),
            region.key_r,
        )?;

        // Anything following this node is below the account
        let lo = address_item.word::<F>().lo();
        let hi: F = address_item.word::<F>().hi() * pow::value::<F>(256.scalar(), 16);
        let address = lo + hi;
        MainData::witness_store(
            region,
            offset,
            &mut memory[main_memory()],
            main_data.proof_type,
            true,
            address,
            main_data.new_root,
            main_data.old_root,
        )?;

        // Put the data in the lookup table
        let (proof_type, value) = if is_nonce_mod {
            (MPTProofType::NonceChanged, nonce)
        } else if is_balance_mod {
            (MPTProofType::BalanceChanged, balance)
        } else if is_storage_mod {
            (MPTProofType::StorageChanged, storage)
        } else if is_codehash_mod {
            (MPTProofType::CodeHashChanged, codehash)
        } else if is_account_delete_mod {
            (
                MPTProofType::AccountDestructed,
                vec![Word::<F>::new([0.scalar(), 0.scalar()]); 2],
            )
        } else if is_non_existing_proof {
            (
                MPTProofType::AccountDoesNotExist,
                vec![Word::<F>::new([0.scalar(), 0.scalar()]); 2],
            )
        } else {
            (
                MPTProofType::Disabled,
                vec![Word::<F>::new([0.scalar(), 0.scalar()]); 2],
            )
        };

        if account.is_mod_extension[0] || account.is_mod_extension[1] {
            let mod_list_rlp_bytes: [&[u8]; 2] = [
                &account.mod_list_rlp_bytes[0],
                &account.mod_list_rlp_bytes[1],
            ];
            self.mod_extension
                .assign(region, offset, rlp_values, mod_list_rlp_bytes)?;
        }

        let mut new_value = value[false.idx()];
        if parent_data[false.idx()].is_placeholder {
            new_value = word::Word::<F>::new([0.scalar(), 0.scalar()]);
        }
        mpt_config.mpt_table.assign_cached(
            region,
            offset,
            &MptUpdateRow {
                address: Value::known(from_bytes::value(
                    &account.address.iter().cloned().rev().collect::<Vec<_>>(),
                )),
                storage_key: word::Word::<F>::new([0.scalar(), 0.scalar()]).into_value(),
                proof_type: Value::known(proof_type.scalar()),
                new_root: main_data.new_root.into_value(),
                old_root: main_data.old_root.into_value(),
                new_value: new_value.into_value(),
                old_value: value[true.idx()].into_value(),
            },
        )?;

        Ok(())
    }
}

mod tests {
    use std::marker::PhantomData;

    use crate::util::Challenges;

    use super::*;
    use gadgets::util::Expr;
    use halo2_proofs::{
        circuit::SimpleFloorPlanner,
        dev::MockProver,
        halo2curves::bn256::Fr,
        plonk::{Circuit, ConstraintSystem},
    };
    #[test]
    fn test_ifx() {
        #[derive(Clone, Default)]
        struct InnerConfig<F: Field> {
            _marker: PhantomData<F>,
        }

        impl<F: Field> InnerConfig<F> {
            fn configure(meta: &mut ConstraintSystem<F>, cb: &mut MPTConstraintBuilder<F>) -> Self {
                // meta.create_gate("foo", |meta| vec![100.expr()]);
                meta.create_gate("main", |meta| {
                    circuit!([meta, cb], {
                        cb.require_equal("definitely fail", true.expr(), false.expr());
                    });
                    cb.base.build_constraints()
                });

                Self::default()
            }
        }
        #[derive(Default)]
        struct DummyParam {}

        #[derive(Default)]
        struct OutterCircuit<F: Field> {
            _marker: PhantomData<F>,
        }

        impl<F: Field> Circuit<F> for OutterCircuit<F> {
            type Config = (InnerConfig<F>, Challenges);

            type FloorPlanner = SimpleFloorPlanner;

            type Params = DummyParam;

            fn without_witnesses(&self) -> Self {
                Self::default()
            }

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                let challenges = Challenges::construct(meta);
                let challenges_expr = challenges.exprs(meta);
                let mut cb = MPTConstraintBuilder::new(5, Some(challenges_expr), None);
                let config = InnerConfig::configure(meta, &mut cb);
                (config, challenges)
            }

            fn synthesize(
                &self,
                config: Self::Config,
                layouter: impl halo2_proofs::circuit::Layouter<F>,
            ) -> Result<(), Error> {
                Ok(())
            }
        }

        let k = 10;
        let circuit = OutterCircuit::<Fr>::default();

        let prover = MockProver::run(k, &circuit, vec![]).unwrap();

        // Question 1: Can the config inside ifx be confugured?
        assert!(prover.verify().is_err());

        // Question 2: Can the constraints inside ifx activated?
    }
}
