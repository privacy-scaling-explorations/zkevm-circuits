use eth_types::Field;
use halo2_proofs::{
    circuit::{Region, Value},
    plonk::Error,
};
use num_enum::TryFromPrimitive;
use std::{convert::TryFrom, marker::PhantomData};

use crate::{
    mpt_circuit::helpers::bytes_into_rlc,
    mpt_circuit::param::{
        COUNTER_WITNESS_LEN, C_RLP_START, C_START, HASH_WIDTH, IS_ACCOUNT_DELETE_MOD_POS,
        IS_BALANCE_MOD_POS, IS_CODEHASH_MOD_POS, IS_NONCE_MOD_POS, IS_NON_EXISTING_ACCOUNT_POS,
        IS_NON_EXISTING_STORAGE_POS, IS_STORAGE_MOD_POS, NOT_FIRST_LEVEL_POS, RLP_NUM, S_RLP_START,
        S_START, WITNESS_ROW_WIDTH,
    },
    mpt_circuit::{MPTConfig, ProofValues},
};

use super::param::RLP_LIST_SHORT;

#[derive(Debug, Eq, PartialEq, TryFromPrimitive)]
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
    AccountNonExisting = 18,
    StorageNonExisting = 19,
}

#[derive(Clone, Debug)]
pub struct MptWitnessRow<F> {
    pub(crate) bytes: Vec<u8>,
    _marker: PhantomData<F>,
}

impl<F: Field> MptWitnessRow<F> {
    pub fn new(bytes: Vec<u8>) -> Self {
        Self {
            bytes,
            _marker: PhantomData,
        }
    }

    pub(crate) fn get_type(&self) -> MptWitnessRowType {
        MptWitnessRowType::try_from(self.get_byte_rev(1)).unwrap()
    }

    pub(crate) fn get_byte_rev(&self, rev_index: usize) -> u8 {
        self.bytes[self.len() - rev_index]
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

    pub(crate) fn s_root_bytes(&self) -> &[u8] {
        &self.bytes[self.bytes.len()
            - 4 * HASH_WIDTH
            - COUNTER_WITNESS_LEN
            - IS_NON_EXISTING_STORAGE_POS
            ..self.bytes.len() - 4 * HASH_WIDTH - COUNTER_WITNESS_LEN - IS_NON_EXISTING_STORAGE_POS
                + HASH_WIDTH]
    }

    pub(crate) fn c_root_bytes(&self) -> &[u8] {
        &self.bytes[self.bytes.len()
            - 3 * HASH_WIDTH
            - COUNTER_WITNESS_LEN
            - IS_NON_EXISTING_STORAGE_POS
            ..self.bytes.len() - 3 * HASH_WIDTH - COUNTER_WITNESS_LEN - IS_NON_EXISTING_STORAGE_POS
                + HASH_WIDTH]
    }

    pub(crate) fn s_root_bytes_rlc(&self, r: F) -> F {
        bytes_into_rlc(self.s_root_bytes(), r)
    }

    pub(crate) fn c_root_bytes_rlc(&self, r: F) -> F {
        bytes_into_rlc(self.c_root_bytes(), r)
    }

    pub(crate) fn address_bytes(&self) -> &[u8] {
        &self.bytes[self.bytes.len()
            - 2 * HASH_WIDTH
            - COUNTER_WITNESS_LEN
            - IS_NON_EXISTING_STORAGE_POS
            ..self.bytes.len() - 2 * HASH_WIDTH - COUNTER_WITNESS_LEN - IS_NON_EXISTING_STORAGE_POS
                + HASH_WIDTH]
    }

    pub(crate) fn s_hash_bytes(&self) -> &[u8] {
        let offset = if self.bytes[S_RLP_START] < RLP_LIST_SHORT {
            1
        } else {
            0
        };
        &self.bytes[S_RLP_START+offset..34]
        //&self.bytes[S_RLP_START..S_RLP_START + 34]
    }

    pub(crate) fn c_hash_bytes(&self) -> &[u8] {
        let offset = if self.bytes[C_RLP_START] < RLP_LIST_SHORT {
            1
        } else {
            0
        };
        &self.bytes[C_RLP_START+offset..68]
        //&self.bytes[C_RLP_START..C_RLP_START + 34]
    }

    pub(crate) fn main(&self) -> &[u8] {
        &self.bytes[0..self.bytes.len() - 1]
    }

    pub(crate) fn assign(
        &self,
        region: &mut Region<'_, F>,
        mpt_config: &MPTConfig<F>,
        offset: usize,
    ) -> Result<(), Error> {
        let row = self.main();

        region.assign_advice(
            || "assign s_rlp1".to_string(),
            mpt_config.s_main.rlp1,
            offset,
            || Value::known(F::from(row[0] as u64)),
        )?;

        region.assign_advice(
            || "assign s_rlp2".to_string(),
            mpt_config.s_main.rlp2,
            offset,
            || Value::known(F::from(row[1] as u64)),
        )?;

        for idx in 0..HASH_WIDTH {
            region.assign_advice(
                || format!("assign s_advice {}", idx),
                mpt_config.s_main.bytes[idx],
                offset,
                || Value::known(F::from(row[RLP_NUM + idx] as u64)),
            )?;
        }

        // not all columns may be needed
        let get_val = |curr_ind: usize| {
            let val = if curr_ind >= row.len() {
                0
            } else {
                row[curr_ind]
            };

            val as u64
        };

        region.assign_advice(
            || "assign c_rlp1".to_string(),
            mpt_config.c_main.rlp1,
            offset,
            || Value::known(F::from(get_val(WITNESS_ROW_WIDTH / 2))),
        )?;
        region.assign_advice(
            || "assign c_rlp2".to_string(),
            mpt_config.c_main.rlp2,
            offset,
            || Value::known(F::from(get_val(WITNESS_ROW_WIDTH / 2 + 1))),
        )?;

        for (idx, _c) in mpt_config.c_main.bytes.iter().enumerate() {
            let val = get_val(WITNESS_ROW_WIDTH / 2 + RLP_NUM + idx);
            region.assign_advice(
                || format!("assign c_advice {}", idx),
                mpt_config.c_main.bytes[idx],
                offset,
                || Value::known(F::from(val)),
            )?;
        }
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
        pv: &ProofValues<F>,
        offset: usize,
    ) -> Result<(), Error> {
        let s_root_rlc = self.s_root_bytes_rlc(mpt_config.randomness);
        let c_root_rlc = self.c_root_bytes_rlc(mpt_config.randomness);

        region.assign_advice(
            || "inter start root",
            mpt_config.inter_start_root,
            offset,
            || Value::known(s_root_rlc),
        )?;
        region.assign_advice(
            || "inter final root",
            mpt_config.inter_final_root,
            offset,
            || Value::known(c_root_rlc),
        )?;

        if pv.before_account_leaf {
            region.assign_advice(
                || "address RLC",
                mpt_config.address_rlc,
                offset,
                || Value::known(F::zero()),
            )?;
        } else {
            /*
            `address_rlc` can be set only in the account leaf row - this is to
            prevent omitting account proof (and having only storage proof
            with the appropriate address RLC)
            */
            let address_rlc = bytes_into_rlc(self.address_bytes(), mpt_config.randomness);

            region.assign_advice(
                || "address RLC",
                mpt_config.address_rlc,
                offset,
                || Value::known(address_rlc),
            )?;
        }

        region.assign_advice(
            || "is_storage_mod",
            mpt_config.proof_type.is_storage_mod,
            offset,
            || Value::known(F::from(self.get_byte_rev(IS_STORAGE_MOD_POS) as u64)),
        )?;
        region.assign_advice(
            || "is_nonce_mod",
            mpt_config.proof_type.is_nonce_mod,
            offset,
            || Value::known(F::from(self.get_byte_rev(IS_NONCE_MOD_POS) as u64)),
        )?;
        region.assign_advice(
            || "is_balance_mod",
            mpt_config.proof_type.is_balance_mod,
            offset,
            || Value::known(F::from(self.get_byte_rev(IS_BALANCE_MOD_POS) as u64)),
        )?;
        region.assign_advice(
            || "is_codehash_mod",
            mpt_config.proof_type.is_codehash_mod,
            offset,
            || Value::known(F::from(self.get_byte_rev(IS_CODEHASH_MOD_POS) as u64)),
        )?;
        region.assign_advice(
            || "is_account_delete_mod",
            mpt_config.proof_type.is_account_delete_mod,
            offset,
            || Value::known(F::from(self.get_byte_rev(IS_ACCOUNT_DELETE_MOD_POS) as u64)),
        )?;
        region.assign_advice(
            || "is_non_existing_account",
            mpt_config.proof_type.is_non_existing_account_proof,
            offset,
            || {
                Value::known(F::from(
                    self.get_byte_rev(IS_NON_EXISTING_ACCOUNT_POS) as u64
                ))
            },
        )?;
        region.assign_advice(
            || "is_non_existing_storage",
            mpt_config.proof_type.is_non_existing_storage_proof,
            offset,
            || {
                Value::known(F::from(
                    self.get_byte_rev(IS_NON_EXISTING_STORAGE_POS) as u64
                ))
            },
        )?;

        Ok(())
    }
}
