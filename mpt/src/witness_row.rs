use std::{convert::{TryFrom, TryInto}, marker::PhantomData};
use halo2_proofs::{circuit::Region, plonk::Error, arithmetic::FieldExt};
use num_enum::TryFromPrimitive;

use crate::{param::{NOT_FIRST_LEVEL_POS, IS_NON_EXISTING_ACCOUNT_POS, COUNTER_WITNESS_LEN, HASH_WIDTH, IS_STORAGE_MOD_POS, S_START, C_START, RLP_NUM, WITNESS_ROW_WIDTH, S_RLP_START, C_RLP_START, IS_NONCE_MOD_POS, IS_BALANCE_MOD_POS, IS_ACCOUNT_DELETE_MOD_POS, IS_CODEHASH_MOD_POS}, account_leaf::AccountLeaf, storage_leaf::StorageLeaf, branch::Branch, mpt::{MPTConfig, ProofVariables}, helpers::bytes_into_rlc};

#[derive(Eq, PartialEq, TryFromPrimitive)]
#[repr(u8)]
pub(crate) enum MptWitnessRowType {
    InitBranch = 0,
    BranchChild = 1,
    StorageLeafSKey = 2,
    StorageLeafCKey = 3,
    HashToBeComputed = 5,
    AccountLeafKeyS = 6,
    AccountLeafKeyC = 4,
    AccountLeafNonceBalanceS = 7,
    AccountLeafNonceBalanceC = 8,
    AccountLeafRootCodehashS = 9,
    AccountLeafNeighbouringLeaf = 10,
    AccountLeafRootCodehashC = 11,
    StorageLeafSValue = 13,
    StorageLeafCValue = 14,
    NeighbouringStorageLeaf = 15, 
    ExtensionNodeS = 16,
    ExtensionNodeC = 17,
    AccountNonExisting = 18
}

pub(crate) struct MptWitnessRow<F>{
    pub(crate) bytes: Vec<u8>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> MptWitnessRow<F> {
    pub(crate) fn new(bytes: Vec<u8>) -> Self {
        Self {
            bytes,
            _marker: PhantomData,
        }
    }

    pub(crate) fn get_type(&self) -> MptWitnessRowType {
        MptWitnessRowType::try_from(self.get_byte_rev(1)).unwrap()
    }

    pub(crate) fn get_byte_rev(&self, rev_index: usize) -> u8 {
        self.bytes[self.bytes.len() - rev_index]
    }

    pub(crate) fn get_byte(&self, index: usize) -> u8 {
        self.bytes[index]
    }

    pub(crate) fn len(&self) -> usize {
        self.bytes.len()
    }

    pub(crate) fn not_first_level(&self) -> u8 {
        self.get_byte_rev(NOT_FIRST_LEVEL_POS)
    }

    pub(crate) fn is_storage_mod(&self) -> u8 {
        self.get_byte_rev(IS_STORAGE_MOD_POS)
    }

    pub(crate) fn s_root_bytes(&self) -> &[u8] { 
        &self.bytes[self.bytes.len()
            - 4 * HASH_WIDTH
            - COUNTER_WITNESS_LEN
            - IS_NON_EXISTING_ACCOUNT_POS
            .. self.bytes.len() - 4 * HASH_WIDTH
                - COUNTER_WITNESS_LEN
                - IS_NON_EXISTING_ACCOUNT_POS
                + HASH_WIDTH]
    }

    pub(crate) fn c_root_bytes(&self) -> &[u8] { 
        &self.bytes[self.bytes.len()
            - 3 * HASH_WIDTH
            - COUNTER_WITNESS_LEN
            - IS_NON_EXISTING_ACCOUNT_POS
            .. self.bytes.len() - 3 * HASH_WIDTH
                - COUNTER_WITNESS_LEN
                - IS_NON_EXISTING_ACCOUNT_POS
                + HASH_WIDTH]
    }

    pub(crate) fn address_bytes(&self) -> &[u8] { 
        &self.bytes[self.bytes.len()
            - 2 * HASH_WIDTH
            - COUNTER_WITNESS_LEN
            - IS_NON_EXISTING_ACCOUNT_POS
            .. self.bytes.len() - 2 * HASH_WIDTH
                - COUNTER_WITNESS_LEN
                - IS_NON_EXISTING_ACCOUNT_POS
                + HASH_WIDTH]
    }

    pub(crate) fn counter_bytes(&self) -> &[u8] { 
        &self.bytes[self.bytes.len()
            - HASH_WIDTH
            - COUNTER_WITNESS_LEN
            - IS_NON_EXISTING_ACCOUNT_POS
            .. self.bytes.len() - HASH_WIDTH
                - COUNTER_WITNESS_LEN
                - IS_NON_EXISTING_ACCOUNT_POS
                + COUNTER_WITNESS_LEN]
    }

    pub(crate) fn s_hash_bytes(&self) -> &[u8] { 
        &self.bytes[S_START..S_START + HASH_WIDTH]
    } 

    pub(crate) fn c_hash_bytes(&self) -> &[u8] { 
        &self.bytes[C_START..C_START + HASH_WIDTH]
    }

    pub(crate) fn main(&self) -> &[u8] { 
        &self.bytes[0..self.bytes.len() - 1]
    }

    pub(crate) fn assign(
        &self,
        region: &mut Region<'_, F>,
        mpt_config: &MPTConfig<F>,
        account_leaf: AccountLeaf,
        storage_leaf: StorageLeaf,
        branch: Branch,
        offset: usize,
    ) -> Result<(), Error> {
        let row = self.main();

        region.assign_advice(
            || "assign is_branch_init".to_string(),
            mpt_config.branch.is_init,
            offset,
            || Ok(F::from(branch.is_branch_init as u64)),
        )?;

        region.assign_advice(
            || "assign is_branch_child".to_string(),
            mpt_config.branch.is_child,
            offset,
            || Ok(F::from(branch.is_branch_child as u64)),
        )?;

        region.assign_advice(
            || "assign acc_s".to_string(),
            mpt_config.accumulators.acc_s.rlc,
            offset,
            || Ok(F::zero()),
        )?;

        region.assign_advice(
            || "assign acc_mult_s".to_string(),
            mpt_config.accumulators.acc_s.mult,
            offset,
            || Ok(F::zero()),
        )?;

        region.assign_advice(
            || "assign acc_c".to_string(),
            mpt_config.accumulators.acc_c.rlc,
            offset,
            || Ok(F::zero()),
        )?;

        region.assign_advice(
            || "assign acc_mult_c".to_string(),
            mpt_config.accumulators.acc_c.mult,
            offset,
            || Ok(F::zero()),
        )?;

        // because used for is_long
        region.assign_advice(
            || "assign s_modified_node_rlc".to_string(),
            mpt_config.accumulators.s_mod_node_rlc,
            offset,
            || Ok(F::zero()),
        )?;
        // because used for is_short
        region.assign_advice(
            || "assign c_modified_node_rlc".to_string(),
            mpt_config.accumulators.c_mod_node_rlc,
            offset,
            || Ok(F::zero()),
        )?;

        region.assign_advice(
            || "assign is_last_branch_child".to_string(),
            mpt_config.branch.is_last_child,
            offset,
            || Ok(F::from(branch.is_last_branch_child as u64)),
        )?;

        region.assign_advice(
            || "assign node_index".to_string(),
            mpt_config.branch.node_index,
            offset,
            || Ok(F::from(branch.node_index as u64)),
        )?;

        region.assign_advice(
            || "assign modified node".to_string(),
            mpt_config.branch.modified_node,
            offset,
            || Ok(F::from(branch.modified_node as u64)),
        )?;

        region.assign_advice(
            || "assign drifted_pos".to_string(),
            mpt_config.branch.drifted_pos,
            offset,
            || Ok(F::from(branch.drifted_pos as u64)),
        )?;

        region.assign_advice(
            || "assign is_at_drifted_pos".to_string(),
            mpt_config.branch.is_at_drifted_pos,
            offset,
            || Ok(F::from((branch.drifted_pos == branch.node_index) as u64)),
        )?;

        region.assign_advice(
            || "assign key rlc".to_string(),
            mpt_config.accumulators.key.rlc,
            offset,
            || Ok(F::zero()),
        )?;

        region.assign_advice(
            || "assign key rlc mult".to_string(),
            mpt_config.accumulators.key.mult,
            offset,
            || Ok(F::zero()),
        )?;

        region.assign_advice(
            || "assign mult diff".to_string(),
            mpt_config.accumulators.mult_diff,
            offset,
            || Ok(F::zero()),
        )?;

        region.assign_advice(
            || "assign sel1".to_string(),
            mpt_config.denoter.sel1,
            offset,
            || Ok(F::zero()),
        )?;
        region.assign_advice(
            || "assign sel2".to_string(),
            mpt_config.denoter.sel2,
            offset,
            || Ok(F::zero()),
        )?;

        region.assign_advice(
            || "assign is_modified".to_string(),
            mpt_config.branch.is_modified,
            offset,
            || Ok(F::from((branch.modified_node == branch.node_index) as u64)),
        )?;

        region.assign_advice(
            || "assign is_leaf_s".to_string(),
            mpt_config.storage_leaf.is_s_key,
            offset,
            || Ok(F::from(storage_leaf.is_s_key as u64)),
        )?;
        region.assign_advice(
            || "assign is_leaf_c".to_string(),
            mpt_config.storage_leaf.is_c_key,
            offset,
            || Ok(F::from(storage_leaf.is_c_key as u64)),
        )?;

        region.assign_advice(
            || "assign is_leaf_s_value".to_string(),
            mpt_config.storage_leaf.is_s_value,
            offset,
            || Ok(F::from(storage_leaf.is_s_value as u64)),
        )?;
        region.assign_advice(
            || "assign is_leaf_c_value".to_string(),
            mpt_config.storage_leaf.is_c_value,
            offset,
            || Ok(F::from(storage_leaf.is_c_value as u64)),
        )?;

        region.assign_advice(
            || "assign is account leaf key s".to_string(),
            mpt_config.account_leaf.is_key_s,
            offset,
            || Ok(F::from(account_leaf.is_key_s as u64)),
        )?;
        region.assign_advice(
            || "assign is account leaf key c".to_string(),
            mpt_config.account_leaf.is_key_c,
            offset,
            || Ok(F::from(account_leaf.is_key_c as u64)),
        )?;
        region.assign_advice(
            || "assign is account leaf nonce balance s".to_string(),
            mpt_config.account_leaf.is_nonce_balance_s,
            offset,
            || Ok(F::from(account_leaf.is_nonce_balance_s as u64)),
        )?;
        region.assign_advice(
            || "assign is account leaf nonce balance c".to_string(),
            mpt_config.account_leaf.is_nonce_balance_c,
            offset,
            || Ok(F::from(account_leaf.is_nonce_balance_c as u64)),
        )?;
        region.assign_advice(
            || "assign is account leaf storage codehash s".to_string(),
            mpt_config.account_leaf.is_storage_codehash_s,
            offset,
            || Ok(F::from(account_leaf.is_storage_codehash_s as u64)),
        )?;
        region.assign_advice(
            || "assign is account leaf storage codehash c".to_string(),
            mpt_config.account_leaf.is_storage_codehash_c,
            offset,
            || Ok(F::from(account_leaf.is_storage_codehash_c as u64)),
        )?;
        region.assign_advice(
            || "assign is account leaf in added branch".to_string(),
            mpt_config.account_leaf.is_in_added_branch,
            offset,
            || Ok(F::from(account_leaf.is_in_added_branch as u64)),
        )?;

        region.assign_advice(
            || "assign is leaf in added branch".to_string(),
            mpt_config.storage_leaf.is_in_added_branch,
            offset,
            || Ok(F::from(storage_leaf.is_in_added_branch as u64)),
        )?;
        region.assign_advice(
            || "assign is extension node s".to_string(),
            mpt_config.branch.is_extension_node_s,
            offset,
            || Ok(F::from(branch.is_extension_node_s as u64)),
        )?;
        region.assign_advice(
            || "assign is extension node c".to_string(),
            mpt_config.branch.is_extension_node_c,
            offset,
            || Ok(F::from(branch.is_extension_node_c as u64)),
        )?;
        region.assign_advice(
            || "assign is non existing account row".to_string(),
            mpt_config.account_leaf.is_non_existing_account_row,
            offset,
            || Ok(F::from(account_leaf.is_non_existing_account_row as u64)),
        )?;

        region.assign_advice(
            || "assign s_rlp1".to_string(),
            mpt_config.s_main.rlp1,
            offset,
            || Ok(F::from(row[0] as u64)),
        )?;

        region.assign_advice(
            || "assign s_rlp2".to_string(),
            mpt_config.s_main.rlp2,
            offset,
            || Ok(F::from(row[1] as u64)),
        )?;

        for idx in 0..HASH_WIDTH {
            region.assign_advice(
                || format!("assign s_advice {}", idx),
                mpt_config.s_main.bytes[idx],
                offset,
                || Ok(F::from(row[RLP_NUM + idx] as u64)),
            )?;
        }

        // not all columns may be needed
        let get_val = |curr_ind: usize| {
            let val;
            if curr_ind >= row.len() {
                val = 0;
            } else {
                val = row[curr_ind];
            }

            val as u64
        };

        region.assign_advice(
            || "assign c_rlp1".to_string(),
            mpt_config.c_main.rlp1,
            offset,
            || Ok(F::from(get_val(WITNESS_ROW_WIDTH / 2))),
        )?;
        region.assign_advice(
            || "assign c_rlp2".to_string(),
            mpt_config.c_main.rlp2,
            offset,
            || Ok(F::from(get_val(WITNESS_ROW_WIDTH / 2 + 1))),
        )?;

        for (idx, _c) in mpt_config.c_main.bytes.iter().enumerate() {
            let val = get_val(WITNESS_ROW_WIDTH / 2 + RLP_NUM + idx);
            region.assign_advice(
                || format!("assign c_advice {}", idx),
                mpt_config.c_main.bytes[idx],
                offset,
                || Ok(F::from(val)),
            )?;
        }
        Ok(())
    } 

    pub(crate) fn assign_branch_row(
        &self,
        region: &mut Region<'_, F>,
        mpt_config: &MPTConfig<F>,
        node_index: u8,
        key: u8,
        key_rlc: F,
        key_rlc_mult: F,
        mult_diff: F,
        s_mod_node_hash_rlc: F,
        c_mod_node_hash_rlc: F,
        drifted_pos: u8,
        s_rlp1: i32,
        c_rlp1: i32,
        offset: usize,
    ) -> Result<(), Error> {
        let row = self.main();

        let account_leaf = AccountLeaf::default();
        let storage_leaf = StorageLeaf::default();
        let mut branch = Branch::default();
        branch.is_branch_child = true;
        branch.is_last_branch_child = node_index == 15;
        branch.node_index = node_index;
        branch.modified_node = key;
        branch.drifted_pos = drifted_pos;

        self.assign(
            region,
            mpt_config,
            account_leaf,
            storage_leaf,
            branch,
            offset,
        )?;

        region.assign_advice(
            || "s_mod_node_hash_rlc",
            mpt_config.accumulators.s_mod_node_rlc,
            offset,
            || Ok(s_mod_node_hash_rlc),
        )?;
        region.assign_advice(
            || "c_mod_node_hash_rlc",
            mpt_config.accumulators.c_mod_node_rlc,
            offset,
            || Ok(c_mod_node_hash_rlc),
        )?;

        region.assign_advice(|| "key rlc", mpt_config.accumulators.key.rlc, offset, || Ok(key_rlc))?;
        region.assign_advice(
            || "key rlc mult",
            mpt_config.accumulators.key.mult,
            offset,
            || Ok(key_rlc_mult),
        )?;
        region.assign_advice(|| "mult diff", mpt_config.accumulators.mult_diff, offset, || Ok(mult_diff))?;

        region.assign_advice(
            || "s_rlp1",
            mpt_config.s_main.rlp1,
            offset,
            || Ok(F::from(s_rlp1 as u64)),
        )?;
        region.assign_advice(
            || "c_rlp1",
            mpt_config.c_main.rlp1,
            offset,
            || Ok(F::from(c_rlp1 as u64)),
        )?;

        region.assign_advice(
            || "is_node_hashed_s",
            mpt_config.denoter.is_node_hashed_s,
            offset,
            || Ok(F::from((row[S_RLP_START + 1] == 0 && row[S_START] > 192) as u64)),
        )?;
        region.assign_advice(
            || "is_node_hashed_c",
            mpt_config.denoter.is_node_hashed_c,
            offset,
            || Ok(F::from((row[C_RLP_START + 1] == 0 && row[C_START] > 192) as u64)),
        )?;

        Ok(())
    }

    /*
    Assignment of the columns that are used for all lookups. There are other columns used for
    lookups which are lookup-specific (for example requiring old and new nonce value).
    */
    pub(crate) fn assign_lookup_columns(
        &self,
        region: &mut Region<'_, F>,
        mpt_config: &MPTConfig<F>,
        pv: &ProofVariables<F>,
        offset: usize,
    ) -> Result<(), Error> {
        let s_root_rlc = bytes_into_rlc(self.s_root_bytes(), mpt_config.acc_r,);
        let c_root_rlc = bytes_into_rlc(self.c_root_bytes(), mpt_config.acc_r,);

        region.assign_advice(
            || "inter start root",
            mpt_config.inter_start_root,
            offset,
            || Ok(s_root_rlc),
        )?;
        region.assign_advice(
            || "inter final root",
            mpt_config.inter_final_root,
            offset,
            || Ok(c_root_rlc),
        )?;

        if pv.before_account_leaf {
            region.assign_advice(
                || "address RLC",
                mpt_config.address_rlc,
                offset,
                || Ok(F::zero()),
            )?;
        } else {
            // address_rlc can be set only in account leaf row - this is to
            // prevent omitting account proof (and having only storage proof
            // with the appropriate address_rlc)
            let address_rlc = bytes_into_rlc(self.address_bytes(), mpt_config.acc_r,);

            region.assign_advice(
                || "address RLC",
                mpt_config.address_rlc,
                offset,
                || Ok(address_rlc),
            )?;
        }
        
        let counter_u32: u32 = u32::from_be_bytes(
                self.counter_bytes()
                .try_into()
                .expect("slice of incorrect length"),
        );
        region.assign_advice(
            || "counter",
            mpt_config.counter,
            offset,
            || Ok(F::from(counter_u32 as u64)),
        )?;

        region.assign_advice(
            || "is_storage_mod",
            mpt_config.proof_type.is_storage_mod,
            offset,
            || Ok(F::from(self.get_byte_rev(IS_STORAGE_MOD_POS) as u64)),
        )?;
        region.assign_advice(
            || "is_nonce_mod",
            mpt_config.proof_type.is_nonce_mod,
            offset,
            || Ok(F::from(self.get_byte_rev(IS_NONCE_MOD_POS) as u64)),
        )?;
        region.assign_advice(
            || "is_balance_mod",
            mpt_config.proof_type.is_balance_mod,
            offset,
            || Ok(F::from(self.get_byte_rev(IS_BALANCE_MOD_POS) as u64)),
        )?;
        region.assign_advice(
            || "is_codehash_mod",
            mpt_config.proof_type.is_codehash_mod,
            offset,
            || Ok(F::from(self.get_byte_rev(IS_CODEHASH_MOD_POS) as u64)),
        )?;
        region.assign_advice(
            || "is_account_delete_mod",
            mpt_config.proof_type.is_account_delete_mod,
            offset,
            || Ok(F::from(self.get_byte_rev(IS_ACCOUNT_DELETE_MOD_POS) as u64)),
        )?;
        region.assign_advice(
            || "is_non_existing_account",
            mpt_config.proof_type.is_non_existing_account_proof,
            offset,
            || Ok(F::from(self.get_byte_rev(IS_NON_EXISTING_ACCOUNT_POS) as u64)),
        )?;

        Ok(())
    }
}