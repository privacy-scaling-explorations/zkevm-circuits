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
    LongExtNodeKey,
    LongExtNodeNibbles,
    LongExtNodeValue,
    ShortExtNodeKey,
    ShortExtNodeNibbles,
    ShortExtNodeValue,
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
    LongExtNodeKey,      // only used when extension node nibbles are modified
    LongExtNodeNibbles,  // only used when extension node nibbles are modified
    LongExtNodeValue,    // only used when extension node nibbles are modified
    ShortExtNodeKey,     // only used when extension node nibbles are modified
    ShortExtNodeNibbles, // only used when extension node nibbles are modified
    ShortExtNodeValue,   // only used when extension node nibbles are modified
    Address,             // account address
    Key,                 // hashed account address
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
    Nibbles,
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
    pub is_last_level_and_wrong_ext_case: bool,
    /// TODO Doc.
    pub(crate) is_mod_extension: [bool; 2],
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
    /// Account address.
    pub address: Hex,
    /// Hashed account address.
    pub key: Hex,
    /// RLP bytes denoting the length of the whole account leaf stream.
    pub list_rlp_bytes: [Hex; 2],
    /// RLP bytes denoting the length of the RLP list denoting the value stream (containing nonce,
    /// balance storage, codehash).
    pub value_rlp_bytes: [Hex; 2],
    /// RLP bytes denoting the length of the RLP of the value stream.
    pub value_list_rlp_bytes: [Hex; 2],
    /// RLP bytes denoting the length of the RLP stream of the drifted leaf (neighbour leaf).
    /// This is only needed in the case when a new branch is created which replaces the existing
    /// leaf in the trie and this leaf drifts down into newly created branch.
    pub drifted_rlp_bytes: Hex,
    /// RLP bytes denoting the length of the RLP stream of the (wrong) leaf that has been returned
    /// by `getProof` which has the same address up to a certain nibble as the required leaf.
    /// This is only needed for some special cases of the AccountDoesNotExist proof.
    pub wrong_rlp_bytes: Hex,
    /// Denotes whether the extension node nibbles have been modified in either `S` or `C` proof.
    /// In these special cases, an additional extension node is inserted (deleted).
    pub(crate) is_mod_extension: [bool; 2],
    /// RLP bytes denoting the length of the RLP of the long and short modified extension node.
    pub(crate) mod_list_rlp_bytes: [Hex; 2],
}

/// MPT storage node
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StorageNode {
    /// Storage key.
    pub address: Hex,
    /// Hashed storage key.
    pub key: Hex,
    /// RLP bytes denoting the length of the whole storage leaf stream.
    pub list_rlp_bytes: [Hex; 2],
    /// RLP bytes denoting the length of the value stream.
    pub value_rlp_bytes: [Hex; 2],
    /// RLP bytes denoting the length of the RLP stream of the drifted leaf (neighbour leaf).
    /// This is only needed in the case when a new branch is created which replaces the existing
    /// leaf in the trie and this leaf drifts down into newly created branch.
    pub drifted_rlp_bytes: Hex,
    /// RLP bytes denoting the length of the RLP stream of the (wrong) leaf that has been returned
    /// by `getProof` which has the same address up to a certain nibble as the required leaf.
    /// This is only needed for some special cases of the StorageDoesNotExist proof.
    pub wrong_rlp_bytes: Hex,
    /// Denotes whether the extension node nibbles have been modified in either `S` or `C` proof.
    /// In these special cases, an additional extension node is inserted (deleted).
    pub(crate) is_mod_extension: [bool; 2],
    /// RLP bytes denoting the length of the RLP of the long and short modified extension node.
    pub(crate) mod_list_rlp_bytes: [Hex; 2],
}

/// MPT node
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct Node {
    /// A node denoting the start / end of the proof.
    pub start: Option<StartNode>,
    /// A node as an abstraction of extension node and branch.
    pub extension_branch: Option<ExtensionBranchNode>,
    /// An account leaf node.
    pub account: Option<AccountNode>,
    /// A storage leaf node.
    pub storage: Option<StorageNode>,
    /// RLP substreams of the node (for example for account leaf it contains substreams for key,
    /// nonce, balance, storage, codehash, drifted key, wrong key...)
    pub values: Vec<Hex>,
    /// Streams to be hashed and verified by Keccak circuit.
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
    RlpItemType::Key,
    RlpItemType::Nibbles,
    RlpItemType::Value,
    RlpItemType::Key,
    RlpItemType::Nibbles,
    RlpItemType::Value,
    RlpItemType::Address,
    RlpItemType::Hash,
];

/// RLP types storage
pub const NODE_RLP_TYPES_STORAGE: [RlpItemType; StorageRowType::Count as usize] = [
    RlpItemType::Key,
    RlpItemType::Value,
    RlpItemType::Key,
    RlpItemType::Value,
    RlpItemType::Key,
    RlpItemType::Key,
    RlpItemType::Key,
    RlpItemType::Nibbles,
    RlpItemType::Value,
    RlpItemType::Key,
    RlpItemType::Nibbles,
    RlpItemType::Value,
    RlpItemType::Hash,
    RlpItemType::Hash,
];
