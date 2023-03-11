use eth_types::Field;
use halo2_proofs::{
    circuit::{Region, Value},
    plonk::Error,
};
use num_enum::TryFromPrimitive;
use std::{convert::TryFrom, marker::PhantomData};

use crate::{
    mpt_circuit::param::{
        COUNTER_WITNESS_LEN, HASH_WIDTH, IS_NON_EXISTING_STORAGE_POS, NOT_FIRST_LEVEL_POS,
        WITNESS_ROW_WIDTH,
    },
    mpt_circuit::MPTConfig,
};

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
    pub(crate) rlp_bytes: Vec<u8>,
    pub(crate) is_extension: bool,
    _marker: PhantomData<F>,
}

impl<F: Field> MptWitnessRow<F> {
    pub fn new(bytes: Vec<u8>) -> Self {
        Self {
            bytes,
            rlp_bytes: Vec::new(),
            is_extension: false,
            _marker: PhantomData,
        }
    }

    pub(crate) fn s(&self) -> Vec<u8> {
        self.bytes[0..34].to_owned()
    }

    pub(crate) fn c(&self) -> Vec<u8> {
        self.bytes[34..68].to_owned()
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

    pub(crate) fn address_bytes(&self) -> &[u8] {
        &self.bytes[self.bytes.len()
            - 2 * HASH_WIDTH
            - COUNTER_WITNESS_LEN
            - IS_NON_EXISTING_STORAGE_POS
            ..self.bytes.len() - 2 * HASH_WIDTH - COUNTER_WITNESS_LEN - IS_NON_EXISTING_STORAGE_POS
                + HASH_WIDTH]
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

        for idx in 0..HASH_WIDTH + 2 {
            region.assign_advice(
                || format!("assign s_advice {}", idx),
                mpt_config.s_main.bytes[idx],
                offset,
                || Value::known(F::from(row[idx] as u64)),
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

        for (idx, _c) in mpt_config.c_main.bytes.iter().enumerate() {
            let val = get_val(WITNESS_ROW_WIDTH / 2 + idx);
            region.assign_advice(
                || format!("assign c_advice {}", idx),
                mpt_config.c_main.bytes[idx],
                offset,
                || Value::known(F::from(val)),
            )?;
        }
        Ok(())
    }
}
