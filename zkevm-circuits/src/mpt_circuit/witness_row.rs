use crate::table::MPTProofType;

use serde::{Deserialize, Serialize};

use super::RlpItemType;

#[derive(Debug, Eq, PartialEq)]
pub(crate) enum StorageRowType {
    KeyS,
    ValueS,
    KeyC,
    ValueC,
    Drifted,
    Wrong,
    Address,
    Key,
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
    Address,
    Key,
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
    /// TODO
    pub modified_index: usize,
    /// TODO
    pub drifted_index: usize,
    /// TODO
    pub list_rlp_bytes: [Vec<u8>; 2],
}

/// MPT extension node
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ExtensionNode {
    /// TODO
    pub list_rlp_bytes: Vec<u8>,
}

/// MPT start node
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StartNode {
    /// TODO
    pub disable_preimage_check: bool,
    /// TODO
    pub proof_type: MPTProofType,
}

/// MPT extension branch node
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ExtensionBranchNode {
    /// TODO
    pub is_extension: bool,
    /// TODO
    pub is_placeholder: [bool; 2],
    /// TODO
    pub extension: ExtensionNode,
    /// TODO
    pub  branch: BranchNode,
}

/// MPT account node
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AccountNode {
    /// TODO
    pub address: Vec<u8>,
    /// TODO
    pub key: Vec<u8>,
    /// TODO
    pub list_rlp_bytes: [Vec<u8>; 2],
    /// TODO
    pub value_rlp_bytes: [Vec<u8>; 2],
    /// TODO
    pub value_list_rlp_bytes: [Vec<u8>; 2],
    /// TODO
    pub drifted_rlp_bytes: Vec<u8>,
    /// TODO
    pub wrong_rlp_bytes: Vec<u8>,
}

/// MPT storage node
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StorageNode {
    /// TODO
    pub address: Vec<u8>,
    /// TODO
    pub key: Vec<u8>,
    /// TODO
    pub list_rlp_bytes: [Vec<u8>; 2],
    /// TODO
    pub value_rlp_bytes: [Vec<u8>; 2],
    /// TODO
    pub drifted_rlp_bytes: Vec<u8>,
    /// TODO
    pub wrong_rlp_bytes: Vec<u8>,
}

/// MPT node
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct Node {
    /// TODO
    pub start: Option<StartNode>,
    /// TODO
    pub extension_branch: Option<ExtensionBranchNode>,
    /// TODO
    pub account: Option<AccountNode>,
    /// TODO
    pub storage: Option<StorageNode>,
    /// MPT node values
    pub values: Vec<Vec<u8>>,
    /// MPT keccak data
    pub keccak_data: Vec<Vec<u8>>,
}

/// RLP types start
pub const NODE_RLP_TYPES_START: [RlpItemType; StartRowType::Count as usize] =
    [RlpItemType::Hash, RlpItemType::Hash];

/// RLP types branch
pub const NODE_RLP_TYPES_BRANCH: [RlpItemType; ExtensionBranchRowType::Count as usize] = [
    RlpItemType::Node,
    RlpItemType::Node,
    RlpItemType::Node,
    RlpItemType::Node,
    RlpItemType::Node,
    RlpItemType::Node,
    RlpItemType::Node,
    RlpItemType::Node,
    RlpItemType::Node,
    RlpItemType::Node,
    RlpItemType::Node,
    RlpItemType::Node,
    RlpItemType::Node,
    RlpItemType::Node,
    RlpItemType::Node,
    RlpItemType::Node,
    RlpItemType::Node,
    RlpItemType::Key,
    RlpItemType::Node,
    RlpItemType::Nibbles,
    RlpItemType::Node,
];

/// RLP types account
pub const NODE_RLP_TYPES_ACCOUNT: [RlpItemType; AccountRowType::Count as usize] = [
    RlpItemType::Key,
    RlpItemType::Key,
    RlpItemType::Value,
    RlpItemType::Value,
    RlpItemType::Hash,
    RlpItemType::Hash,
    RlpItemType::Value,
    RlpItemType::Value,
    RlpItemType::Hash,
    RlpItemType::Hash,
    RlpItemType::Key,
    RlpItemType::Key,
    RlpItemType::Value,
    RlpItemType::Hash,
];

/// RLP types account
pub const NODE_RLP_TYPES_STORAGE: [RlpItemType; StorageRowType::Count as usize] = [
    RlpItemType::Key,
    RlpItemType::Value,
    RlpItemType::Key,
    RlpItemType::Value,
    RlpItemType::Key,
    RlpItemType::Key,
    RlpItemType::Value,
    RlpItemType::Hash,
];
