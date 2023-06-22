use eth_types::Field;
use num_enum::TryFromPrimitive;
use std::{convert::TryFrom, marker::PhantomData};

use crate::{
    mpt_circuit::param::{
        COUNTER_WITNESS_LEN, HASH_WIDTH, IS_NON_EXISTING_STORAGE_POS, NOT_FIRST_LEVEL_POS,
    },
    table::MPTProofType,
};

use serde::{Deserialize, Serialize};

#[derive(Debug, Eq, PartialEq)]
pub(crate) enum StorageRowType {
    KeyS,
    ValueS,
    KeyC,
    ValueC,
    Drifted,
    Wrong,
    Count,
}

#[derive(Debug, Eq, PartialEq)]
pub(crate) enum AccountRowType {
    KeyS,
    KeyC,
    NonceS,
    BalanceS,
    StorageS,
    CodehashS,
    NonceC,
    BalanceC,
    StorageC,
    CodehashC,
    Drifted,
    Wrong,
    Count,
}

#[derive(Debug, Eq, PartialEq)]
pub(crate) enum ExtensionBranchRowType {
    Mod,
    Child0,
    Child1,
    Child2,
    Child3,
    Child4,
    Child5,
    Child6,
    Child7,
    Child8,
    Child9,
    Child10,
    Child11,
    Child12,
    Child13,
    Child14,
    Child15,
    KeyS,
    ValueS,
    KeyC,
    ValueC,
    Count,
}

#[derive(Debug, Eq, PartialEq)]
pub(crate) enum StartRowType {
    RootS,
    RootC,
    Count,
}

/// MPT branch node
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BranchNode {
    pub(crate) modified_index: usize,
    pub(crate) drifted_index: usize,
    pub(crate) list_rlp_bytes: [Vec<u8>; 2],
}

/// MPT extension node
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ExtensionNode {
    pub(crate) list_rlp_bytes: Vec<u8>,
}

/// MPT start node
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StartNode {
    pub(crate) proof_type: MPTProofType,
}

/// MPT extension branch node
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ExtensionBranchNode {
    pub(crate) is_extension: bool,
    pub(crate) is_placeholder: [bool; 2],
    pub(crate) extension: ExtensionNode,
    pub(crate) branch: BranchNode,
}

/// MPT account node
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AccountNode {
    pub(crate) address: Vec<u8>,
    pub(crate) list_rlp_bytes: [Vec<u8>; 2],
    pub(crate) value_rlp_bytes: [Vec<u8>; 2],
    pub(crate) value_list_rlp_bytes: [Vec<u8>; 2],
    pub(crate) drifted_rlp_bytes: Vec<u8>,
    pub(crate) wrong_rlp_bytes: Vec<u8>,
}

/// MPT storage node
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StorageNode {
    pub(crate) list_rlp_bytes: [Vec<u8>; 2],
    pub(crate) value_rlp_bytes: [Vec<u8>; 2],
    pub(crate) drifted_rlp_bytes: Vec<u8>,
    pub(crate) wrong_rlp_bytes: Vec<u8>,
}

/// MPT node
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct Node {
    pub(crate) start: Option<StartNode>,
    pub(crate) extension_branch: Option<ExtensionBranchNode>,
    pub(crate) account: Option<AccountNode>,
    pub(crate) storage: Option<StorageNode>,
    /// MPT node values
    pub values: Vec<Vec<u8>>,
    /// MPT keccak data
    pub keccak_data: Vec<Vec<u8>>,
}

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

/// MPT witness row
#[derive(Clone, Debug)]
pub struct MptWitnessRow<F> {
    pub(crate) bytes: Vec<u8>,
    pub(crate) rlp_bytes: Vec<u8>,
    pub(crate) is_extension: bool,
    pub(crate) is_placeholder: [bool; 2],
    pub(crate) modified_index: usize,
    pub(crate) drifted_index: usize,
    pub(crate) proof_type: MPTProofType,
    pub(crate) address: Vec<u8>,
    _marker: PhantomData<F>,
}

impl<F: Field> MptWitnessRow<F> {
    /// New MPT witness row
    pub fn new(bytes: Vec<u8>) -> Self {
        Self {
            bytes,
            rlp_bytes: Vec::new(),
            is_extension: false,
            is_placeholder: [false; 2],
            modified_index: 0,
            drifted_index: 0,
            proof_type: MPTProofType::Disabled,
            address: Vec::new(),
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
}
