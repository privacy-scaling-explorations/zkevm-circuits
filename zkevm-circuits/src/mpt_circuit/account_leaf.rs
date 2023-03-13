use eth_types::Field;
use gadgets::util::Scalar;
use halo2_proofs::{
    circuit::Region,
    plonk::{Error, VirtualCells},
    poly::Rotation,
};

use super::{
    helpers::ParentDataWitness,
    rlp_gadgets::RLPValueGadget,
    witness_row::{AccountRowType, Node},
};
use super::{
    helpers::{KeyDataWitness, ListKeyGadget, MainData},
    param::HASH_WIDTH,
};
use crate::{
    circuit,
    circuit_tools::cell_manager::Cell,
    circuit_tools::constraint_builder::RLCable,
    mpt_circuit::MPTContext,
    mpt_circuit::{
        helpers::{
            key_memory, num_nibbles, parent_memory, KeyData, MPTConstraintBuilder, ParentData,
        },
        param::{KEY_LEN_IN_NIBBLES, RLP_LIST_LONG, RLP_LONG},
        FixedTableTag,
    },
    mpt_circuit::{MPTConfig, MPTState},
};
use crate::{
    circuit_tools::constraint_builder::RLCChainable,
    mpt_circuit::helpers::{DriftedGadget, WrongGadget},
};
use crate::{
    circuit_tools::{constraint_builder::RLCableValue, gadgets::IsEqualGadget},
    mpt_circuit::helpers::{main_memory, Indexable, IsEmptyTreeGadget},
};
use crate::{table::ProofType, witness::MptUpdateRow};

#[derive(Clone, Debug, Default)]
pub(crate) struct AccountLeafConfig<F> {
    main_data: MainData<F>,
    key_data: [KeyData<F>; 2],
    parent_data: [ParentData<F>; 2],
    rlp_key: [ListKeyGadget<F>; 2],
    key_mult: [Cell<F>; 2],
    value_rlp_bytes: [[Cell<F>; 4]; 2],
    rlp_nonce: [RLPValueGadget<F>; 2],
    rlp_balance: [RLPValueGadget<F>; 2],
    rlp_storage: [RLPValueGadget<F>; 2],
    rlp_codehash: [RLPValueGadget<F>; 2],
    nonce_mult: [Cell<F>; 2],
    balance_mult: [Cell<F>; 2],
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

        cb.base.cell_manager.as_mut().unwrap().reset();
        let mut config = AccountLeafConfig::default();

        circuit!([meta, cb.base], {
            let key_bytes = [
                ctx.s(meta, AccountRowType::KeyS as i32).to_owned(),
                ctx.s(meta, AccountRowType::KeyC as i32).to_owned(),
            ];
            config.value_rlp_bytes = [cb.base.query_bytes(), cb.base.query_bytes()];
            let nonce_bytes = [
                ctx.s(meta, AccountRowType::NonceS as i32).to_owned(),
                ctx.s(meta, AccountRowType::NonceC as i32).to_owned(),
            ];
            let balance_bytes = [
                ctx.s(meta, AccountRowType::BalanceS as i32).to_owned(),
                ctx.s(meta, AccountRowType::BalanceC as i32).to_owned(),
            ];
            let storage_bytes = [
                ctx.s(meta, AccountRowType::StorageS as i32).to_owned(),
                ctx.s(meta, AccountRowType::StorageC as i32).to_owned(),
            ];
            let codehash_bytes = [
                ctx.s(meta, AccountRowType::CodehashS as i32).to_owned(),
                ctx.s(meta, AccountRowType::CodehashC as i32).to_owned(),
            ];
            let drifted_bytes = ctx.s(meta, AccountRowType::Drifted as i32).to_owned();
            let wrong_bytes = ctx.s(meta, AccountRowType::Wrong as i32).to_owned();

            config.main_data = MainData::load(
                "main storage",
                &mut cb.base,
                &ctx.memory[main_memory()],
                0.expr(),
            );

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
                *key_data = KeyData::load(&mut cb.base, &ctx.memory[key_memory(is_s)], 0.expr());

                // Parent data
                let parent_data = &mut config.parent_data[is_s.idx()];
                *parent_data = ParentData::load(
                    "account load",
                    &mut cb.base,
                    &ctx.memory[parent_memory(is_s)],
                    0.expr(),
                );

                // Placeholder leaf checks
                config.is_in_empty_trie[is_s.idx()] =
                    IsEmptyTreeGadget::construct(&mut cb.base, parent_data.rlc.expr(), &r);

                // Calculate the key RLC
                let rlp_key = &mut config.rlp_key[is_s.idx()];
                *rlp_key = ListKeyGadget::construct(&mut cb.base, &key_bytes[is_s.idx()]);
                config.rlp_nonce[is_s.idx()] =
                    RLPValueGadget::construct(&mut cb.base, &nonce_bytes[is_s.idx()]);
                config.rlp_balance[is_s.idx()] =
                    RLPValueGadget::construct(&mut cb.base, &balance_bytes[is_s.idx()]);
                config.rlp_storage[is_s.idx()] =
                    RLPValueGadget::construct(&mut cb.base, &storage_bytes[is_s.idx()]);
                config.rlp_codehash[is_s.idx()] =
                    RLPValueGadget::construct(&mut cb.base, &codehash_bytes[is_s.idx()]);

                // Storage root and codehash are always 32-byte hashes.
                require!(config.rlp_storage[is_s.idx()].len() => HASH_WIDTH);
                require!(config.rlp_codehash[is_s.idx()].len() => HASH_WIDTH);

                config.key_mult[is_s.idx()] = cb.base.query_cell();
                config.nonce_mult[is_s.idx()] = cb.base.query_cell();
                config.balance_mult[is_s.idx()] = cb.base.query_cell();
                require!((FixedTableTag::RMult, rlp_key.num_bytes_on_key_row(), config.key_mult[is_s.idx()].expr()) => @"fixed");
                require!((FixedTableTag::RMult, config.rlp_nonce[is_s.idx()].num_bytes() + 4.expr(), config.nonce_mult[is_s.idx()].expr()) => @format!("fixed"));
                require!((FixedTableTag::RMult, config.rlp_balance[is_s.idx()].num_bytes(), config.balance_mult[is_s.idx()].expr()) => @format!("fixed"));

                // RLC bytes zero check
                cb.set_length(rlp_key.num_bytes_on_key_row());

                let nonce_rlp_rlc;
                let balance_rlp_rlc;
                let storage_rlp_rlc;
                let codehash_rlp_rlc;
                (nonce_rlc[is_s.idx()], nonce_rlp_rlc) = config.rlp_nonce[is_s.idx()].rlc(&r);
                (balance_rlc[is_s.idx()], balance_rlp_rlc) = config.rlp_balance[is_s.idx()].rlc(&r);
                (storage_rlc[is_s.idx()], storage_rlp_rlc) = config.rlp_storage[is_s.idx()].rlc(&r);
                (codehash_rlc[is_s.idx()], codehash_rlp_rlc) =
                    config.rlp_codehash[is_s.idx()].rlc(&r);

                // Calculate the leaf RLC
                leaf_no_key_rlc[is_s.idx()] = (0.expr(), 1.expr()).rlc_chain(
                    (
                        [
                            config.value_rlp_bytes[is_s.idx()]
                                .clone()
                                .iter()
                                .map(|c| c.expr())
                                .collect::<Vec<_>>(),
                            vec![nonce_rlp_rlc],
                        ]
                        .concat()
                        .rlc(&r),
                        config.nonce_mult[is_s.idx()].expr(),
                    )
                        .rlc_chain(
                            (balance_rlp_rlc, config.balance_mult[is_s.idx()].expr()).rlc_chain(
                                (storage_rlp_rlc, r[32].expr()).rlc_chain(codehash_rlp_rlc),
                            ),
                        ),
                );
                let leaf_rlc = (rlp_key.rlc(&r), config.key_mult[is_s.idx()].expr())
                    .rlc_chain(leaf_no_key_rlc[is_s.idx()].expr());

                // Key
                key_rlc[is_s.idx()] = key_data.rlc.expr()
                    + rlp_key.key.expr(
                        &mut cb.base,
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
                    require!((1, leaf_rlc, rlp_key.rlp_list.num_bytes(), config.parent_data[is_s.idx()].rlc) => @"keccak");
                }}

                // Check the RLP encoding consistency.
                // RlP encoding: account = [key, [nonce, balance, storage, codehash]]
                // We always store between 55 and 256 bytes of data in the values list.
                require!(config.value_rlp_bytes[is_s.idx()][0] => RLP_LONG + 1);
                // The RLP encoded list always has 2 RLP bytes.
                require!(config.value_rlp_bytes[is_s.idx()][1] => config.value_rlp_bytes[is_s.idx()][3].expr() + 2.expr());
                // The first RLP byte of the list is always RLP_LIST_LONG + 1.
                require!(config.value_rlp_bytes[is_s.idx()][2] => RLP_LIST_LONG + 1);
                // The length of the list is `#(nonce) + #(balance) + 2 * (1 + #(hash))`.
                require!(config.value_rlp_bytes[is_s.idx()][3] => config.rlp_nonce[is_s.idx()].num_bytes() + config.rlp_balance[is_s.idx()].num_bytes() + (2 * (1 + 32)).expr());
                // Now check that the the key and value list length matches the account length.
                // The RLP encoded string always has 2 RLP bytes.
                let value_list_num_bytes = config.value_rlp_bytes[is_s.idx()][1].expr() + 2.expr();
                // Account length needs to equal all key bytes and all values list bytes.
                require!(config.rlp_key[is_s.idx()].rlp_list.len() => config.rlp_key[is_s.idx()].key_value.num_bytes() + value_list_num_bytes);

                // Key done, set the starting values
                KeyData::store(
                    &mut cb.base,
                    &ctx.memory[key_memory(is_s)],
                    KeyData::default_values_expr(),
                );
                // Store the new parent
                ParentData::store(
                    &mut cb.base,
                    &ctx.memory[parent_memory(is_s)],
                    [
                        storage_rlc[is_s.idx()].expr(),
                        true.expr(),
                        false.expr(),
                        storage_rlc[is_s.idx()].expr(),
                    ],
                );
            }

            // Anything following this node is below the account
            // TODO(Brecht): For non-existing accounts it should be impossible to prove
            // storage leafs unless it's also a non-existing proof?
            MainData::store(
                &mut cb.base,
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
                ProofType::AccountDoesNotExist.expr(),
            );
            config.is_account_delete_mod = IsEqualGadget::construct(
                &mut cb.base,
                config.main_data.proof_type.expr(),
                ProofType::AccountDestructed.expr(),
            );
            config.is_nonce_mod = IsEqualGadget::construct(
                &mut cb.base,
                config.main_data.proof_type.expr(),
                ProofType::NonceChanged.expr(),
            );
            config.is_balance_mod = IsEqualGadget::construct(
                &mut cb.base,
                config.main_data.proof_type.expr(),
                ProofType::BalanceChanged.expr(),
            );
            config.is_storage_mod = IsEqualGadget::construct(
                &mut cb.base,
                config.main_data.proof_type.expr(),
                ProofType::StorageChanged.expr(),
            );
            config.is_codehash_mod = IsEqualGadget::construct(
                &mut cb.base,
                config.main_data.proof_type.expr(),
                ProofType::CodeHashExists.expr(),
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
            let (proof_type, value_prev, value) = _matchx! {cb.base,
                config.is_nonce_mod => (ProofType::NonceChanged.expr(), nonce_rlc[true.idx()].expr(), nonce_rlc[false.idx()].expr()),
                config.is_balance_mod => (ProofType::BalanceChanged.expr(), balance_rlc[true.idx()].expr(), balance_rlc[false.idx()].expr()),
                config.is_storage_mod => (ProofType::StorageChanged.expr(), storage_rlc[true.idx()].expr(), storage_rlc[false.idx()].expr()),
                config.is_codehash_mod => (ProofType::CodeHashExists.expr(), codehash_rlc[true.idx()].expr(), codehash_rlc[false.idx()].expr()),
                config.is_account_delete_mod => (ProofType::AccountDestructed.expr(), 0.expr(), 0.expr()),
                config.is_non_existing_account_proof => (ProofType::AccountDoesNotExist.expr(), 0.expr(), 0.expr()),
                _ => (ProofType::Disabled.expr(), 0.expr(), 0.expr()),
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

    pub fn assign(
        &self,
        region: &mut Region<'_, F>,
        ctx: &MPTConfig<F>,
        pv: &mut MPTState<F>,
        offset: usize,
        node: &Node,
    ) -> Result<(), Error> {
        let account = &node.account.clone().unwrap();

        let key_bytes = [
            node.values[AccountRowType::KeyS as usize].clone(),
            node.values[AccountRowType::KeyC as usize].clone(),
        ];
        let nonce_bytes = [
            node.values[AccountRowType::NonceS as usize].clone(),
            node.values[AccountRowType::NonceC as usize].clone(),
        ];
        let balance_bytes = [
            node.values[AccountRowType::BalanceS as usize].clone(),
            node.values[AccountRowType::BalanceC as usize].clone(),
        ];
        let storage_bytes = [
            node.values[AccountRowType::StorageS as usize].clone(),
            node.values[AccountRowType::StorageC as usize].clone(),
        ];
        let codehash_bytes = [
            node.values[AccountRowType::CodehashS as usize].clone(),
            node.values[AccountRowType::CodehashC as usize].clone(),
        ];
        let drifted_bytes = node.values[AccountRowType::Drifted as usize].clone();
        let wrong_bytes = node.values[AccountRowType::Wrong as usize].clone();

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

            key_data[is_s.idx()] = self.key_data[is_s.idx()].witness_load(
                region,
                offset,
                &mut pv.memory[key_memory(is_s)],
                0,
            )?;

            parent_data[is_s.idx()] = self.parent_data[is_s.idx()].witness_load(
                region,
                offset,
                &mut pv.memory[parent_memory(is_s)],
                0,
            )?;

            self.is_in_empty_trie[is_s.idx()].assign(
                region,
                offset,
                parent_data[is_s.idx()].rlc,
                ctx.r,
            )?;

            let rlp_key_witness = self.rlp_key[is_s.idx()].assign(
                region,
                offset,
                &account.list_rlp_bytes[is_s.idx()],
                &key_bytes[is_s.idx()],
            )?;
            let nonce_witness =
                self.rlp_nonce[is_s.idx()].assign(region, offset, &nonce_bytes[is_s.idx()])?;
            let balance_witness =
                self.rlp_balance[is_s.idx()].assign(region, offset, &balance_bytes[is_s.idx()])?;
            let storage_witness =
                self.rlp_storage[is_s.idx()].assign(region, offset, &storage_bytes[is_s.idx()])?;
            let codehash_witness = self.rlp_codehash[is_s.idx()].assign(
                region,
                offset,
                &codehash_bytes[is_s.idx()],
            )?;

            nonce_rlc[is_s.idx()] = nonce_witness.rlc_value(ctx.r);
            balance_rlc[is_s.idx()] = balance_witness.rlc_value(ctx.r);
            storage_rlc[is_s.idx()] = storage_witness.rlc_value(ctx.r);
            codehash_rlc[is_s.idx()] = codehash_witness.rlc_value(ctx.r);

            // + 4 because of s_rlp1, s_rlp2, c_rlp1, c_rlp2
            let mut mult_nonce = F::one();
            for _ in 0..nonce_witness.num_bytes() + 4 {
                mult_nonce *= ctx.r;
            }
            let mut mult_balance = F::one();
            for _ in 0..balance_witness.num_bytes() {
                mult_balance *= ctx.r;
            }
            self.nonce_mult[is_s.idx()].assign(region, offset, mult_nonce)?;
            self.balance_mult[is_s.idx()].assign(region, offset, mult_balance)?;

            // Key
            (key_rlc[is_s.idx()], _) = rlp_key_witness.key.key(
                rlp_key_witness.key_value.clone(),
                key_data[is_s.idx()].rlc,
                key_data[is_s.idx()].mult,
                ctx.r,
            );

            let mut key_mult = F::one();
            for _ in 0..rlp_key_witness.num_bytes_on_key_row() {
                key_mult *= ctx.r;
            }
            self.key_mult[is_s.idx()].assign(region, offset, key_mult)?;

            // Update key and parent state
            KeyData::witness_store(
                region,
                offset,
                &mut pv.memory[key_memory(is_s)],
                F::zero(),
                F::one(),
                0,
                false,
                F::zero(),
                F::one(),
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
            account.address.rlc_value(ctx.r),
            main_data.root_prev,
            main_data.root,
        )?;

        // Proof types
        let is_non_existing_proof = self.is_non_existing_account_proof.assign(
            region,
            offset,
            main_data.proof_type.scalar(),
            ProofType::AccountDoesNotExist.scalar(),
        )? == true.scalar();
        let is_account_delete_mod = self.is_account_delete_mod.assign(
            region,
            offset,
            main_data.proof_type.scalar(),
            ProofType::AccountDestructed.scalar(),
        )? == true.scalar();
        let is_nonce_mod = self.is_nonce_mod.assign(
            region,
            offset,
            main_data.proof_type.scalar(),
            ProofType::NonceChanged.scalar(),
        )? == true.scalar();
        let is_balance_mod = self.is_balance_mod.assign(
            region,
            offset,
            main_data.proof_type.scalar(),
            ProofType::BalanceChanged.scalar(),
        )? == true.scalar();
        let is_storage_mod = self.is_storage_mod.assign(
            region,
            offset,
            main_data.proof_type.scalar(),
            ProofType::StorageChanged.scalar(),
        )? == true.scalar();
        let is_codehash_mod = self.is_codehash_mod.assign(
            region,
            offset,
            main_data.proof_type.scalar(),
            ProofType::CodeHashExists.scalar(),
        )? == true.scalar();

        // Drifted leaf handling
        self.drifted.assign(
            region,
            offset,
            &parent_data,
            &account.drifted_rlp_bytes,
            &drifted_bytes,
            ctx.r,
        )?;

        // Wrong leaf handling
        self.wrong.assign(
            region,
            offset,
            is_non_existing_proof,
            &key_rlc,
            &account.wrong_rlp_bytes,
            &wrong_bytes,
            true,
            key_data[true.idx()].clone(),
            ctx.r,
        )?;

        // Put the data in the lookup table
        let (proof_type, value) = if is_nonce_mod {
            (ProofType::NonceChanged, nonce_rlc)
        } else if is_balance_mod {
            (ProofType::BalanceChanged, balance_rlc)
        } else if is_storage_mod {
            (ProofType::StorageChanged, storage_rlc)
        } else if is_codehash_mod {
            (ProofType::CodeHashExists, codehash_rlc)
        } else if is_account_delete_mod {
            (ProofType::AccountDestructed, vec![0.scalar(); 2])
        } else if is_non_existing_proof {
            (ProofType::AccountDoesNotExist, vec![0.scalar(); 2])
        } else {
            (ProofType::Disabled, vec![0.scalar(); 2])
        };
        ctx.mpt_table.assign(
            region,
            offset,
            &MptUpdateRow {
                address_rlc: account.address.rlc_value(ctx.r),
                proof_type: proof_type.scalar(),
                key_rlc: 0.scalar(),
                value_prev: value[true.idx()],
                value: value[false.idx()],
                root_prev: main_data.root_prev,
                root: main_data.root,
            },
        )?;

        Ok(())
    }
}
