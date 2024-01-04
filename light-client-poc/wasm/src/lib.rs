use std::convert::TryFrom;

use light_client_poc::verifier;
use revm::{primitives::{Address, address, Bytecode, AccountInfo, ruint::Uint, TransactTo, Bytes, U256}, db::{CacheDB, EmptyDB}, EVM};
use wasm_bindgen::prelude::*;

use crate::rpc::get_block;

mod rpc;

#[wasm_bindgen]
extern "C" {
    pub fn alert(s: &str);
}
/*
async fn test() {
    let encoded = include_str!(
        "../../light_client/zkevm-circuits/light-client-poc/serialized_verifier_input.json"
    );

    const CONTRACT_ADDR: Address = address!("0d4a11d5EEaaC28EC3F61d100daF4d40471f1852");
    let bytecode = Bytecode::new_raw([0x60, 0x01, 0x00].into());
    let account = AccountInfo::new(Uint::from(10), 0, bytecode.hash_slow(), bytecode);
    let mut db = CacheDB::new(EmptyDB::default());
    db.insert_account_info(CONTRACT_ADDR, account);
    let mut evm: EVM<CacheDB<EmptyDB>> = EVM::new();
    evm.database(db);

    // fill in missing bits of env struc
    // change that to whatever caller you want to be
    evm.env.tx.caller = Address::from_slice(&[0; 20]);
    // account you want to transact with
    evm.env.tx.transact_to = TransactTo::Call(CONTRACT_ADDR);
    // calldata formed via abigen
    evm.env.tx.data = Bytes::new();
    // transaction value in wei
    evm.env.tx.value = U256::try_from(0).unwrap();

    let _result = evm.transact().unwrap();

    match get_block(2000007).await {
        Ok(block) => alert(&format!(
            "State root: {}, txcount2:{}",
            block.stateRoot,
            block.transactions.len()
        )),
        Err(err) => alert(&format!("{:?}", err)),
    }
}
*/
// alert(&format!("Gas used yeah: {}", result.result.gas_used()));

#[wasm_bindgen]
pub fn verify_proof() -> String {
    let fk = include_str!("../prover.fk");
    let proof = include_str!("../prover.proof");
    let data = include_str!("../prover.data");

    let v:  verifier::InitialStateCircuitVerifierData = serde_json::from_str(data).unwrap();

    verifier::wasm_verify_serialized(data, fk, proof)
}