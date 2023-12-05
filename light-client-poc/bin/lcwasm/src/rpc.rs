
#![allow(unused_imports, dead_code, deprecated)]

use std::convert::TryFrom;

use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};
use wasm_bindgen::prelude::*;
use wasm_bindgen::JsCast;
use wasm_bindgen_futures::JsFuture;
use web_sys::{Request, RequestInit, RequestMode, Response};

use eyre::{eyre, Result};

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



