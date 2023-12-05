use eth_types::Field;
use gadgets::util::{pow, Scalar};
use halo2_proofs::{
    circuit::Value,
    plonk::{Error, Expression, VirtualCells},
};

use super::{
    helpers::{
        KeyDataWitness, ListKeyGadget, MainData, MptCellType, ParentDataWitness, RLPItemView,
    },
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
pub(crate) struct ProofX<F> {
    is_s: bool,
    key_data: KeyData<F>,
    parent_data: ParentData<F>,
    rlp_key: ListKeyGadget<F>,
    value_rlp_bytes: [Cell<F>; 2],
    value_list_rlp_bytes: [Cell<F>; 2],
    is_placeholder_leaf: IsPlaceholderLeafGadget<F>,
    is_mod_extension: Cell<F>,
    nonce: RLPItemView<F>,
    balance: RLPItemView<F>,
    storage: RLPItemView<F>,
    codehash: RLPItemView<F>,
}
impl<F: Field> ProofX<F> {
    pub fn configure(
        meta: &mut VirtualCells<'_, F>,
        cb: &mut MPTConstraintBuilder<F>,
        ctx: &mut MPTContext<F>,
        is_s: bool,
    ) -> Self {
        let mut config = Self::default();
        circuit!([meta, cb], {
            config.is_s = is_s;
            config.value_rlp_bytes = cb.query_bytes();
            config.value_list_rlp_bytes = cb.query_bytes();
            config.is_mod_extension = cb.query_bool();
            config.parent_data =
                ParentData::load(cb, &mut ctx.memory[parent_memory(is_s)], 0.expr());
            config.key_data = KeyData::load(cb, &mut ctx.memory[key_memory(is_s)], 0.expr());

            let key_items = ctx.rlp_item(
                meta,
                cb,
                if is_s {
                    AccountRowType::KeyS
                } else {
                    AccountRowType::KeyC
                } as usize,
                RlpItemType::Key,
            );
            let nonce_items = ctx.rlp_item(
                meta,
                cb,
                if is_s {
                    AccountRowType::NonceS
                } else {
                    AccountRowType::NonceC
                } as usize,
                RlpItemType::Value,
            );
            let balance_items = ctx.rlp_item(
                meta,
                cb,
                if is_s {
                    AccountRowType::BalanceS
                } else {
                    AccountRowType::BalanceC
                } as usize,
                RlpItemType::Value,
            );
            let storage_items = ctx.rlp_item(
                meta,
                cb,
                if is_s {
                    AccountRowType::StorageS
                } else {
                    AccountRowType::StorageC
                } as usize,
                RlpItemType::Value,
            );
            let codehash_items = ctx.rlp_item(
                meta,
                cb,
                if is_s {
                    AccountRowType::CodehashS
                } else {
                    AccountRowType::CodehashC
                } as usize,
                RlpItemType::Value,
            );
            ifx! {not!(config.is_mod_extension.expr()) => {
                // Placeholder leaf checks
                config.is_placeholder_leaf =
                    IsPlaceholderLeafGadget::construct(cb, config.parent_data.hash.expr());

                // Calculate the key RLC
                let rlp_key = ListKeyGadget::construct(cb, &key_items);


                let (nonce, nonce_rlp_rlc) = (
                    nonce_items.word(),
                    nonce_items.rlc_chain_data(),
                );
                let (balance, balance_rlp_rlc) = (
                    balance_items.word(),
                    balance_items.rlc_chain_data(),
                );
                let (storage, storage_rlp_rlc) = (
                    storage_items.word(),
                    storage_items.rlc_chain_data(),
                );
                let (codehash, codehash_rlp_rlc) = (
                    codehash_items.word(),
                    codehash_items.rlc_chain_data(),
                );

                // Calculate the leaf RLC
                let keccak_r = &cb.keccak_r;
                let value_rlp_bytes = config.value_rlp_bytes.to_expr_vec();
                let value_list_rlp_bytes = config.value_list_rlp_bytes.to_expr_vec();
                let leaf_no_key_rlc = value_rlp_bytes
                    .rlc_rev(keccak_r)
                    .rlc_chain_rev((
                        value_list_rlp_bytes.rlc_rev(keccak_r),
                        pow::expr(keccak_r.expr(), 2),
                    ))
                    .rlc_chain_rev(nonce_rlp_rlc.clone())
                    .rlc_chain_rev(balance_rlp_rlc.clone())
                    .rlc_chain_rev(storage_rlp_rlc.clone())
                    .rlc_chain_rev(codehash_rlp_rlc.clone());
                let leaf_no_key_rlc_mult = pow::expr(keccak_r.expr(), 4)
                    * nonce_rlp_rlc.1
                    * balance_rlp_rlc.1
                    * storage_rlp_rlc.1
                    * codehash_rlp_rlc.1;
                let leaf_rlc = rlp_key.rlc2(&cb.keccak_r).rlc_chain_rev((
                    leaf_no_key_rlc.expr(),
                    leaf_no_key_rlc_mult.expr(),
                ));

                // Key
                let key_rlc = config.key_data.rlc.expr()
                    + rlp_key.key.expr(
                        cb,
                        rlp_key.key_value.clone(),
                        config.key_data.mult.expr(),
                        config.key_data.is_odd.expr(),
                        &cb.key_r.expr(),
                    );
                // Total number of nibbles needs to be KEY_LEN_IN_NIBBLES.
                let num_nibbles =
                    num_nibbles::expr(rlp_key.key_value.len(), config.key_data.is_odd.expr());
                require!(config.key_data.num_nibbles.expr() + num_nibbles.expr() => KEY_LEN_IN_NIBBLES);

                // Check if the account is in its parent.
                // Check is skipped for placeholder leaves which are dummy leaves
                ifx! {not!(and::expr(&[not!(config.parent_data.is_placeholder), config.is_placeholder_leaf.expr()])) => {
                    let hash = config.parent_data.hash.expr();
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
                require!(value_list_rlp_bytes[1] => nonce_items.num_bytes() + balance_items.num_bytes() + (2 * (1 + 32)).expr());
                // Now check that the the key and value list length matches the account length.
                // The RLP encoded string always has 2 RLP bytes.
                let value_list_num_bytes = value_rlp_bytes[1].expr() + 2.expr();

                // Account length needs to equal all key bytes and all values list bytes.
                require!(config.rlp_key.rlp_list.len() => config.rlp_key.key_value.num_bytes() + value_list_num_bytes.expr());
            }};
            // Key done, set the starting values
            KeyData::store_defaults(cb, &mut ctx.memory[key_memory(is_s)]);
            // Store the new parent
            ParentData::store(
                cb,
                &mut ctx.memory[parent_memory(is_s)],
                storage_items.word(),
                0.expr(),
                true.expr(),
                false.expr(),
                storage_items.word(),
            );
        });
        config
    }
    fn nonce(self) -> word::Word<Expression<F>> {
        self.nonce.word()
    }
    fn balance(self) -> word::Word<Expression<F>> {
        self.balance.word()
    }
    fn storage(self) -> word::Word<Expression<F>> {
        self.storage.word()
    }
    fn codehash(self) -> word::Word<Expression<F>> {
        self.codehash.word()
    }
    fn key_rlc(self) -> Expression<F> {
        todo!()
    }
    pub fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        mpt_config: &MPTConfig<F>,
        memory: &mut MptMemory<F>,
        offset: usize,
        account: &AccountNode,
        rlp_values: &[RLPItemWitness],
    ) -> Result<(), Error> {



    }
}
#[derive(Clone, Debug, Default)]
pub(crate) struct AccountLeafConfig<F> {
    main_data: MainData<F>,
    drifted: DriftedGadget<F>,
    wrong: WrongGadget<F>,
    is_non_existing_account_proof: IsEqualGadget<F>,
    is_account_delete_mod: IsEqualGadget<F>,
    is_nonce_mod: IsEqualGadget<F>,
    is_balance_mod: IsEqualGadget<F>,
    is_storage_mod: IsEqualGadget<F>,
    is_codehash_mod: IsEqualGadget<F>,
    mod_extension: ModExtensionGadget<F>,
    proofC: ProofX<F>,
    proofS: ProofX<F>,
}

impl<F: Field> AccountLeafConfig<F> {
    pub fn configure(
        meta: &mut VirtualCells<'_, F>,
        cb: &mut MPTConstraintBuilder<F>,
        ctx: &mut MPTContext<F>,
    ) -> Self {
        let mut config = AccountLeafConfig::default();

        circuit!([meta, cb], {
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

            config.main_data = MainData::load(cb, &mut ctx.memory[main_memory()], 0.expr());

            // Don't allow an account node to follow an account node
            require!(config.main_data.is_below_account => false);

            let proofS = ProofX::configure(meta, cb, ctx, true);
            let proofC = ProofX::configure(meta, cb, ctx, false);

            config.proofS = proofS;
            config.proofC = proofC;

            ifx! {or::expr(&[proofS.is_mod_extension.clone(), proofC.is_mod_extension.clone()]) => {
                config.mod_extension = ModExtensionGadget::configure(
                    meta,
                    cb,
                    ctx.clone(),
                    &mut [proofS.parent_data, proofC.parent_data],
                    &mut [proofS.key_data, proofC.key_data],
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
            config.drifted =
                DriftedGadget::construct(cb, proofS, proofC, &drifted_bytes, &cb.key_r.expr());

            // Wrong leaf handling
            config.wrong = WrongGadget::construct(
                cb,
                key_item.hash_rlc(),
                config.is_non_existing_account_proof.expr(),
                &proofS.rlp_key.key_value,
                &proofS.key_rlc(),
                &wrong_bytes,
                proofS.is_placeholder_leaf.expr(),
                proofS.key_data.clone(),
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
                    proofC.is_placeholder_leaf.expr(),
                    proofC.parent_data.is_placeholder.expr()
                ]) => true);
            } elsex {
                ifx! {and::expr(&[not!(proofS.parent_data.is_placeholder), not!(proofC.parent_data.is_placeholder)]) => {
                    // Check that there is only one modification, except when the account is being deleted or
                    // the parent branch is a placeholder (meaning the account leafs in S are C are different).
                    // Nonce needs to remain the same when not modifying the nonce
                    ifx!{not!(config.is_nonce_mod) => {
                        require!(proofS.nonce() => proofC.nonce());
                    }}
                    // Balance needs to remain the same when not modifying the balance
                    ifx!{not!(config.is_balance_mod) => {
                        require!(proofS.balance() => proofC.balance());
                    }}
                    // Storage root needs to remain the same when not modifying the storage root
                    ifx!{not!(config.is_storage_mod) => {
                        require!(proofS.storage() => proofC.storage());
                    }}
                    // Codehash root needs to remain the same when not modifying the codehash
                    ifx!{not!(config.is_codehash_mod) => {
                        require!(proofS.codehash() => proofC.codehash());
                    }}
                }}
            }}
            ifx! {config.is_non_existing_account_proof => {
                // For non-existing proofs the tree needs to remain the same
                require!(config.main_data.new_root => config.main_data.old_root);
                require!(proofS.key_rlc() => proofC.key_rlc());
            }}

            // Put the data in the lookup table
            let (proof_type, old_value, new_value) = _matchx! {cb, (
                config.is_nonce_mod => (MPTProofType::NonceChanged.expr(), proofS.nonce(), proofC.nonce()),
                config.is_balance_mod => (MPTProofType::BalanceChanged.expr(), proofS.balance(), proofC.balance()),
                config.is_storage_mod => (MPTProofType::StorageChanged.expr(), proofS.storage(), proofC.storage()),
                config.is_codehash_mod => (MPTProofType::CodeHashChanged.expr(), proofS.codehash(), proofC.codehash()),
                config.is_account_delete_mod => (MPTProofType::AccountDestructed.expr(), word::Word::zero(), word::Word::zero()),
                config.is_non_existing_account_proof => (MPTProofType::AccountDoesNotExist.expr(), word::Word::zero(), word::Word::zero()),
                _ => (MPTProofType::Disabled.expr(), 0.expr(), 0.expr(), 0.expr(), 0.expr()),
            )};
            ifx! {not!(config.is_non_existing_account_proof) => {
                let key_rlc = ifx!{not!(proofS.parent_data.is_placeholder) => {
                    proofS.key_rlc()
                } elsex {
                    proofC.key_rlc()
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

            ifx! {not!(proofC.parent_data.is_placeholder) => {
                ctx.mpt_table.constrain(
                    meta,
                    &mut cb.base,
                    address.clone(),
                    proof_type.clone(),
                    Word::zero(),
                    config.main_data.new_root.expr(),
                    config.main_data.old_root.expr(),
                    new_value,
                    old_value,
                );
            } elsex {
                ctx.mpt_table.constrain(
                    meta,
                    &mut cb.base,
                    address,
                    proof_type,
                    Word::zero(),
                    config.main_data.new_root.expr(),
                    config.main_data.old_root.expr(),
                    Word::<Expression<F>>::zero(),
                    old_value,
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
