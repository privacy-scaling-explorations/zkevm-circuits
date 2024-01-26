use eth_types::U256;
use num_enum::IntoPrimitive;
use strum_macros::EnumIter;

use serde::{Deserialize, Serialize};

use std::ops::Deref;

use ethers::types::{Address, H256, U64};

/// Tag for an AccountField in RwTable
#[derive(Clone, Copy, Debug, EnumIter, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum AccountFieldTag {
    /// Nonce field
    Nonce = 1,
    /// Balance field
    Balance,
    /// CodeHash field
    CodeHash,
    /// NonExisting field
    NonExisting,
}
// impl_expr!(AccountFieldTag);

/// The types of proofs in the MPT table
#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub enum MPTProofType {
    /// Disabled
    Disabled,
    /// Nonce updated
    NonceChanged = AccountFieldTag::Nonce as isize,
    /// Balance updated
    BalanceChanged = AccountFieldTag::Balance as isize,
    /// Code hash updated
    CodeHashChanged = AccountFieldTag::CodeHash as isize,
    /// Account destroyed
    AccountDestructed,
    /// Account does not exist
    AccountDoesNotExist,
    /// Storage updated
    StorageChanged,
    /// Storage does not exist
    StorageDoesNotExist,
}
// impl_expr!(MPTProofType);

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
    /// TODO Doc.
    pub(crate) is_mod_extension: [bool; 2],
    /// TODO Doc.
    pub(crate) mod_list_rlp_bytes: [Hex; 2],
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
    /// TODO Doc.
    pub(crate) is_mod_extension: [bool; 2],
    /// TODO Doc.
    pub(crate) mod_list_rlp_bytes: [Hex; 2],
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

#[derive(Default, Debug, IntoPrimitive, Clone, Copy)]
#[repr(u8)]
pub enum ProofType {
    #[default]
    Disabled = 0,
    NonceChanged = 1,
    BalanceChanged = 2,
    CodeHashChanged = 3,
    AccountDestructed = 4,
    AccountDoesNotExist = 5,
    StorageChanged = 6,
    StorageDoesNotExist = 7,
    AccountCreate = 8,
}

#[derive(Default, Debug, Clone)]
pub struct TrieModification {
    pub typ: ProofType,
    pub key: H256,
    pub value: U256,
    pub address: Address,
    pub nonce: U64,
    pub balance: U256,
    pub code_hash: H256,
}

#[derive(Serialize, Debug, Clone)]
pub struct TrieModificationJson {
    #[serde(rename = "Type")]
    pub typ: u8,
    #[serde(rename = "Key")]
    pub key: H256,
    #[serde(rename = "Value")]
    pub value: H256,
    #[serde(rename = "Address")]
    pub address: Address,
    #[serde(rename = "Nonce")]
    pub nonce: u64,
    #[serde(rename = "Balance")]
    pub balance: serde_json::Number,
    #[serde(rename = "CodeHash")]
    pub code_hash: Vec<u8>,
}
