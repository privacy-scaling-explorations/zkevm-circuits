use std::ops::Deref;

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

/// Serde for hex
#[derive(Debug, Serialize, Deserialize, Clone)]
#[serde(transparent)]
pub struct Hex {
    #[serde(with = "hex::serde")]
    bytes: Vec<u8>,
}

impl From<Vec<u8>> for Hex {
    fn from(bytes: Vec<u8>) -> Self {
        Self { bytes }
    }
}

impl Deref for Hex {
    type Target = Vec<u8>;

    fn deref(&self) -> &Self::Target {
        &self.bytes
    }
}

/// MPT branch node
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BranchNode {
    /// TODO Doc.
    pub modified_index: usize,
    /// TODO Doc.
    pub drifted_index: usize,
    /// TODO Doc.
    pub list_rlp_bytes: [Hex; 2],
}

/// MPT extension node
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ExtensionNode {
    /// TODO Doc.
    pub list_rlp_bytes: Hex,
}

/// MPT start node
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StartNode {
    /// TODO Doc.
    pub disable_preimage_check: bool,
    /// TODO Doc.
    pub proof_type: MPTProofType,
}

/// MPT extension branch node
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ExtensionBranchNode {
    /// TODO Doc.
    pub is_extension: bool,
    /// TODO Doc.
    pub is_placeholder: [bool; 2],
    /// TODO Doc.
    pub extension: ExtensionNode,
    /// TODO Doc.
    pub branch: BranchNode,
}

/// MPT account node
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct AccountNode {
    /// TODO Doc.
    pub address: Hex,
    /// TODO Doc.
    pub key: Hex,
    /// TODO Doc.
    pub list_rlp_bytes: [Hex; 2],
    /// TODO Doc.
    pub value_rlp_bytes: [Hex; 2],
    /// TODO Doc.
    pub value_list_rlp_bytes: [Hex; 2],
    /// TODO Doc.
    pub drifted_rlp_bytes: Hex,
    /// TODO Doc.
    pub wrong_rlp_bytes: Hex,
}

/// MPT storage node
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StorageNode {
    /// TODO Doc.
    pub address: Hex,
    /// TODO Doc.
    pub key: Hex,
    /// TODO Doc.
    pub list_rlp_bytes: [Hex; 2],
    /// TODO Doc.
    pub value_rlp_bytes: [Hex; 2],
    /// TODO Doc.
    pub drifted_rlp_bytes: Hex,
    /// TODO Doc.
    pub wrong_rlp_bytes: Hex,
}

/// MPT node
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct Node {
    /// TODO Doc.
    pub start: Option<StartNode>,
    /// TODO Doc.
    pub extension_branch: Option<ExtensionBranchNode>,
    /// TODO Doc.
    pub account: Option<AccountNode>,
    /// TODO Doc.
    pub storage: Option<StorageNode>,
    /// MPT node values
    pub values: Vec<Hex>,
    /// MPT keccak data
    pub keccak_data: Vec<Hex>,
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
    RlpItemType::Address,
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
    RlpItemType::Hash,
    RlpItemType::Hash,
];
