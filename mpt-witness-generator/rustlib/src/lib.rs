use ethers::types::{Address, H256, U64};
use serde::Serialize;
use std::{
    ffi::{CStr, CString},
    os::raw::c_char,
};

use num_enum::IntoPrimitive;
use zkevm_circuits::{mpt_circuit::witness_row::Node, util::U256};

mod witness {
    use super::*;
    extern "C" {
        pub fn GetWitness(str: *const c_char) -> *const c_char;
    }
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

pub fn get_witness(block_no: u64, mods: &[TrieModification], node_url: &str) -> Vec<Node> {
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
    let result = unsafe { witness::GetWitness(c_config.as_ptr() as *const i8) };
    let c_str = unsafe { CStr::from_ptr(result) };
    let json = c_str.to_str().expect("Error translating from library");

    let mut nodes: Vec<Node> = serde_json::from_str(json).unwrap();

    // Add the address and the key to the list of values in the Account and Storage nodes
    for node in nodes.iter_mut() {
        if node.account.is_some() {
            let account = node.account.clone().unwrap();
            node.values.push([vec![148], account.address].concat());
            node.values.push([vec![160], account.key].concat());
        }
        if node.storage.is_some() {
            let storage = node.storage.clone().unwrap();
            node.values.push([vec![160], storage.address].concat());
            node.values.push([vec![160], storage.key].concat());
        }
    }
    nodes
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use super::*;

    #[test]
    fn it_works() {
        let nodes = get_witness(
            14359865,
            &[TrieModification {
                typ: ProofType::StorageChanged,
                key: H256::from_low_u64_le(0x12),
                value: 0x1123e2.into(),
                address: Address::from_str("0x4E5B2e1dc63F6b91cb6Cd759936495434C7e972F").unwrap(),
                nonce: 0.into(),
                balance: 0.into(),
                code_hash: H256::zero(),
            }],
            "https://mainnet.infura.io/v3/9aa3d95b3bc440fa88ea12eaa4456161",
        );
        println!("{:?}", nodes);
        assert_eq!(nodes.len(), 12);
    }
}
