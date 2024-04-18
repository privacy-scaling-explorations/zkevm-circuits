use ethers::types::{Address, H256, U64};
use serde::Serialize;
use std::ffi::{CStr, CString};

use crate::go;
use eth_types::U256;
use num_enum::IntoPrimitive;

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
struct TrieModificationJson {
    #[serde(rename = "Type")]
    typ: u8,
    #[serde(rename = "Key")]
    key: H256,
    #[serde(rename = "Value")]
    value: H256,
    #[serde(rename = "Address")]
    address: Address,
    #[serde(rename = "Nonce")]
    nonce: u64,
    #[serde(rename = "Balance")]
    balance: serde_json::Number,
    #[serde(rename = "CodeHash")]
    code_hash: Vec<u8>,
}

#[derive(Debug, Serialize)]
struct GetWitnessRequest<'a> {
    #[serde(rename = "BlockNum")]
    block_no: u64,
    #[serde(rename = "Mods")]
    mods: Vec<TrieModificationJson>,
    #[serde(rename = "NodeUrl")]
    node_url: &'a str,
}

pub fn get_witness(block_no: u64, mods: &[TrieModification], node_url: &str) -> String {
    let mods: Vec<_> = mods
        .iter()
        .map(|m| TrieModificationJson {
            typ: m.typ as u8,
            key: m.key,
            value: {
                let mut bytes = [0u8; 32];
                m.value.to_big_endian(&mut bytes);
                H256::from_slice(&bytes)
            },
            address: m.address,
            nonce: m.nonce.as_u64(),
            balance: serde_json::Number::from_string_unchecked(format!("{}", m.balance)),
            code_hash: m.code_hash.as_bytes().to_vec(),
        })
        .collect();

    let req = GetWitnessRequest {
        block_no,
        mods,
        node_url,
    };

    let json = serde_json::to_string(&req).expect("Invalid request");
    let c_config = CString::new(json).expect("invalid config");
    let result = unsafe { go::GetMptWitness(c_config.as_ptr()) };
    let c_str = unsafe { CStr::from_ptr(result) };
    let json = c_str
        .to_str()
        .expect("Error translating from library")
        .to_string();

    unsafe { go::FreeString(c_str.as_ptr()) };

    // Note: previously this function returned a Vec of Nodes, but now returning a JSON string
    // to avoid importing zkEVM circuit here (that will create a circular dependency).
    // TODO: consider defining Node types in another crate.

    json
}
