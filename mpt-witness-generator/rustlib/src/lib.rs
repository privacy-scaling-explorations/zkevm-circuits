use ethers::types::H256;
use serde::Serialize;
use std::{
    ffi::{CStr, CString},
    os::raw::c_char,
};

pub use self::utils::{Node, TrieModification, TrieModificationJson};
pub mod utils;

mod golang {
    use super::*;
    extern "C" {
        pub fn GetWitness(str: *const c_char) -> *const c_char;
        pub fn FreeString(str: *const c_char);
    }
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
    println!("get_witness called in MPT");
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
    println!("Calling go GetWitness");
    let result = unsafe { golang::GetWitness(c_config.as_ptr() as *const i8) };
    println!("go GetWitness called.");
    let c_str = unsafe { CStr::from_ptr(result) };
    let json = c_str.to_str().expect("Error translating from library");

    let mut nodes: Vec<Node> = serde_json::from_str(json).unwrap();
    unsafe { golang::FreeString(c_str.as_ptr()) };

    // Add the address and the key to the list of values in the Account and Storage nodes
    for node in nodes.iter_mut() {
        if node.account.is_some() {
            let account = node.account.clone().unwrap();
            node.values
                .push([vec![148], account.address.to_vec()].concat().into());
            node.values
                .push([vec![160], account.key.to_vec()].concat().into());
        }
        if node.storage.is_some() {
            let storage = node.storage.clone().unwrap();
            node.values
                .push([vec![160], storage.address.to_vec()].concat().into());
            node.values
                .push([vec![160], storage.key.to_vec()].concat().into());
        }
    }
    nodes
}

// pub fn recover_witness(
//     block_no: u64,
//     mods: &[TrieModification],
//     node_url: &str,
// ) -> Result<Vec<Node>, serde_json::Error> {
//     let mods: Vec<_> = mods
//         .iter()
//         .map(|m| TrieModificationJson {
//             typ: m.typ as u8,
//             key: m.key,
//             value: {
//                 let mut bytes = [0u8; 32];
//                 m.value.to_big_endian(&mut bytes);
//                 H256::from_slice(&bytes)
//             },
//             address: m.address,
//             nonce: m.nonce.as_u64(),
//             balance: serde_json::Number::from_string_unchecked(format!("{}", m.balance)),
//             code_hash: m.code_hash.as_bytes().to_vec(),
//         })
//         .collect();

//     let req = GetWitnessRequest {
//         block_no,
//         mods,
//         node_url,
//     };

//     let json = serde_json::to_string(&req).expect("Invalid request");
//     let c_config = CString::new(json).expect("invalid config");
//     println!("Calling go GetWitness");
//     let result = unsafe { golang::GetWitness(c_config.as_ptr() as *const i8) };
//     println!("go GetWitness called.");
    
//     let c_str = unsafe { CStr::from_ptr(result) };
// // let json = c_str.to_str().expect("Error translating from library");
// let json = String::from("hola");
//     unsafe { golang::FreeString(c_str.as_ptr()) };

//     // Add the address and the key to the list of values in the Account and Storage nodes
//     serde_json::from_str(json).map(|mut nodes: Vec<Node>| {
//         for node in nodes.iter_mut() {
//             if node.account.is_some() {
//                 let account = node.account.clone().unwrap();
//                 node.values
//                     .push([vec![148], account.address.to_vec()].concat().into());
//                 node.values
//                     .push([vec![160], account.key.to_vec()].concat().into());
//             }
//             if node.storage.is_some() {
//                 let storage = node.storage.clone().unwrap();
//                 node.values
//                     .push([vec![160], storage.address.to_vec()].concat().into());
//                 node.values
//                     .push([vec![160], storage.key.to_vec()].concat().into());
//             }
//         }
//         nodes
//     })
// }

#[cfg(test)]
mod tests {
    use super::*;
    use std::str::FromStr;

    #[test]
    fn it_works() {
        let nodes = get_witness(
            14359865,
            &[TrieModification {
                typ: utils::ProofType::StorageChanged,
                key: H256::from_low_u64_le(0x12),
                value: 0x1123e2.into(),
                address: ethers::types::Address::from_str(
                    "0x4E5B2e1dc63F6b91cb6Cd759936495434C7e972F",
                )
                .unwrap(),
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
