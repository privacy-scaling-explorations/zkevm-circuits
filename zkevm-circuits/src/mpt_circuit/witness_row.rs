use crate::table::MPTProofType;

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
pub(crate) enum ModExtensionRowType {
    Mod,
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
    pub(crate) is_mod_extension: [bool; 2],
    pub(crate) is_placeholder: [bool; 2],
    pub(crate) extension: ExtensionNode,
    pub(crate) branch: BranchNode,
}

/// Modified extension node
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ModExtensionNode {
    pub(crate) list_rlp_bytes: Vec<u8>,
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
    pub(crate) is_mod_extension: [bool; 2],
}

/// MPT storage node
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StorageNode {
    pub(crate) list_rlp_bytes: [Vec<u8>; 2],
    pub(crate) value_rlp_bytes: [Vec<u8>; 2],
    pub(crate) drifted_rlp_bytes: Vec<u8>,
    pub(crate) wrong_rlp_bytes: Vec<u8>,
    pub(crate) is_mod_extension: [bool; 2],
}

/// MPT node
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct Node {
    pub(crate) start: Option<StartNode>,
    pub(crate) extension_branch: Option<ExtensionBranchNode>,
    pub(crate) account: Option<AccountNode>,
    pub(crate) storage: Option<StorageNode>,
    pub(crate) mod_extension: Option<ModExtensionNode>,
    /// MPT node values
    pub values: Vec<Vec<u8>>,
    /// MPT keccak data
    pub keccak_data: Vec<Vec<u8>>,
}
