
#![allow(unused_imports, dead_code, deprecated)]

mod verifier;
mod rpc;

use std::convert::TryFrom;

use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};
use wasm_bindgen::prelude::*;
use wasm_bindgen::JsCast;
use wasm_bindgen_futures::JsFuture;
use web_sys::{Request, RequestInit, RequestMode, Response};

use eyre::{eyre, Result};

use revm::{
    db::{CacheDB, EmptyDB, CacheState},
    interpreter::CreateScheme,
    primitives::{
        address, b256, calc_excess_blob_gas, keccak256, Env, HashMap, SpecId, ruint::Uint, AccountInfo, Address, Bytecode, Bytes, TransactTo, B256, U256,
    },
    EVM,
};

#[wasm_bindgen]
extern "C" {
    fn alert(s: &str);
}

#[derive(Deserialize)]
struct RpcResponse<T> {
    jsonrpc: String,
    id: u32,
    result: T,
}

#[allow(non_snake_case)]
#[derive(Deserialize)]
struct RpcBlock {
    number: String,
    difficulty: String,
    extraData: String,
    gasLimit: String,
    gasUsed: String,
    hash: String,
    logsBloom: String,
    miner: String,
    mixHash: String,
    nonce: String,
    parentHash: String,
    receiptsRoot: String,
    sha3Uncles: String,
    size: String,
    stateRoot: String,
    timestamp: String,
    totalDifficulty: String,
    transactions: Vec<RpcTransaction>,
    transactionsRoot: String,
    uncles: Vec<String>,
}

#[allow(non_snake_case)]
#[derive(Deserialize)]
struct RpcTransaction {
    blockHash: String,
    blockNumber: String,
    from: String,
    gas: String,
    gasPrice: String,
    hash: String,
    input: String,
    nonce: String,
    r: String,
    s: String,
    to: String,
    transactionIndex: String,
    v: String,
    value: String,
}

pub fn js2err(err: JsValue) -> eyre::Report {
    eyre!("js error: {:?}", err)
}

pub async fn web3_rpc<'a, T : DeserializeOwned>(method: &str, params: &str) -> Result<T> {
    // https://rustwasm.github.io/docs/wasm-bindgen/examples/fetch.html
    // https://stackoverflow.com/questions/72521659/how-to-make-post-request-with-json-body-using-web-sys-in-webassembly

    const WEB3_PROVIDER : &str = env!("PROVIDER_URL");
    let request = format!(r#"{{"method":"{method}","params":{params},"id":1,"jsonrpc":"2.0"}}"#);

    let mut opts = RequestInit::new();
    opts.method("POST");
    opts.mode(RequestMode::Cors);
    opts.body(Some(&wasm_bindgen::JsValue::from_str(&request)));

    let request = Request::new_with_str_and_init(WEB3_PROVIDER, &opts).map_err(js2err)?;

    request
        .headers()
        .set("Content-Type","application/json").map_err(js2err)?;

    let window = web_sys::window().ok_or_else(|| eyre!("web_sys::window()"))?;
    let resp_value = JsFuture::from(window.fetch_with_request(&request)).await.map_err(js2err)?;
    assert!(resp_value.is_instance_of::<Response>());
    let resp: Response = resp_value.dyn_into().map_err(js2err)?;
    let json = JsFuture::from(resp.json().map_err(js2err)?).await.map_err(js2err)?;

    // Use serde to parse the JSON into a struct.
    let value: RpcResponse<T> = json.into_serde()?;

    Ok(value.result)
}

pub(crate) async fn get_block(block_no: u64) -> Result<RpcBlock>{
    let params = format!(r#"["0x{:x}",true]"#, block_no);
    web3_rpc("eth_getBlockByNumber",&params).await
}

#[wasm_bindgen]
pub async fn greet(_name: &str) {

    let encoded = include_str!("../../light_client/zkevm-circuits/light-client-poc/serialized_verifier_input.json");

    const CONTRACT_ADDR: Address = address!("0d4a11d5EEaaC28EC3F61d100daF4d40471f1852");
    let bytecode = Bytecode::new_raw([0x60,0x01,0x00].into());
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
        Ok(block) => alert(&format!("State root: {}, txcount2:{}", block.stateRoot, block.transactions.len())),
        Err(err) => alert(&format!("{:?}",err)),
    }

   // alert(&format!("Gas used yeah: {}", result.result.gas_used()));

}
