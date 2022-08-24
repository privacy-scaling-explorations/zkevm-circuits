use std::convert::{TryFrom};
use num_enum::TryFromPrimitive;

use crate::param::{NOT_FIRST_LEVEL_POS, IS_NON_EXISTING_ACCOUNT_POS, COUNTER_WITNESS_LEN, HASH_WIDTH, IS_STORAGE_MOD_POS, S_START, C_START};

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

pub(crate) struct MptWitnessRow(pub Vec<u8>);
impl MptWitnessRow {
    pub(crate) fn get_type(&self) -> MptWitnessRowType {
        MptWitnessRowType::try_from(self.get_byte_rev(1)).unwrap()
    }

    pub(crate) fn get_byte_rev(&self, rev_index: usize) -> u8 {
        self.0[self.0.len() - rev_index]
    }

    pub(crate) fn get_byte(&self, index: usize) -> u8 {
        self.0[index]
    }

    pub(crate) fn len(&self) -> usize {
        self.0.len()
    }

    pub(crate) fn not_first_level(&self) -> u8 {
        self.get_byte_rev(NOT_FIRST_LEVEL_POS)
    }

    pub(crate) fn is_storage_mod(&self) -> u8 {
        self.get_byte_rev(IS_STORAGE_MOD_POS)
    }

    pub(crate) fn s_root_bytes(&self) -> &[u8] { 
        &self.0[self.0.len()
            - 4 * HASH_WIDTH
            - COUNTER_WITNESS_LEN
            - IS_NON_EXISTING_ACCOUNT_POS
            .. self.0.len() - 4 * HASH_WIDTH
                - COUNTER_WITNESS_LEN
                - IS_NON_EXISTING_ACCOUNT_POS
                + HASH_WIDTH]
    }

    pub(crate) fn c_root_bytes(&self) -> &[u8] { 
        &self.0[self.0.len()
            - 3 * HASH_WIDTH
            - COUNTER_WITNESS_LEN
            - IS_NON_EXISTING_ACCOUNT_POS
            .. self.0.len() - 3 * HASH_WIDTH
                - COUNTER_WITNESS_LEN
                - IS_NON_EXISTING_ACCOUNT_POS
                + HASH_WIDTH]
    }

    pub(crate) fn address_bytes(&self) -> &[u8] { 
        &self.0[self.0.len()
            - 2 * HASH_WIDTH
            - COUNTER_WITNESS_LEN
            - IS_NON_EXISTING_ACCOUNT_POS
            .. self.0.len() - 2 * HASH_WIDTH
                - COUNTER_WITNESS_LEN
                - IS_NON_EXISTING_ACCOUNT_POS
                + HASH_WIDTH]
    }

    pub(crate) fn counter_bytes(&self) -> &[u8] { 
        &self.0[self.0.len()
            - HASH_WIDTH
            - COUNTER_WITNESS_LEN
            - IS_NON_EXISTING_ACCOUNT_POS
            .. self.0.len() - HASH_WIDTH
                - COUNTER_WITNESS_LEN
                - IS_NON_EXISTING_ACCOUNT_POS
                + COUNTER_WITNESS_LEN]
    }

    pub(crate) fn s_hash_bytes(&self) -> &[u8] { 
        &self.0[S_START..S_START + HASH_WIDTH]
    } 

    pub(crate) fn c_hash_bytes(&self) -> &[u8] { 
        &self.0[C_START..C_START + HASH_WIDTH]
    }

    pub(crate) fn main(&self) -> &[u8] { 
        &self.0[0..self.0.len() - 1]
    }

}