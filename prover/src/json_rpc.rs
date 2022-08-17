/// Common utilities for json-rpc
use hyper::body::Buf;
use hyper::client::HttpConnector;
use hyper::Body;
use hyper::Request;
use hyper::Uri;

use serde::de::DeserializeOwned;
use serde::Deserialize;
use serde::Serialize;

#[derive(Debug, Serialize, Deserialize)]
pub struct JsonRpcError {
    pub code: i32,
    pub message: String,
}

#[derive(Debug, Serialize)]
pub struct JsonRpcResponseError {
    pub jsonrpc: String,
    pub id: serde_json::Value,
    pub error: JsonRpcError,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct JsonRpcResponse<T> {
    pub jsonrpc: String,
    pub id: serde_json::Value,
    pub result: Option<T>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct JsonRpcRequest<T: Serialize> {
    pub jsonrpc: String,
    pub id: serde_json::Value,
    pub method: String,
    pub params: T,
}

/// Invokes a `json-rpc` request with a timeout of `timeout` ms for the network
/// and deserialize part.
pub async fn jsonrpc_request_client<T: Serialize + Send + Sync, R: DeserializeOwned>(
    timeout: u64,
    client: &hyper::Client<HttpConnector>,
    uri: &Uri,
    method: &str,
    params: T,
) -> Result<R, String> {
    #[derive(Debug, Deserialize)]
    struct JsonRpcResponseInternal<T> {
        result: Option<T>,
        error: Option<JsonRpcError>,
    }

    let node_req = Request::post(uri);
    let req_obj = JsonRpcRequest {
        jsonrpc: "2.0".to_string(),
        id: 0.into(),
        method: method.to_string(),
        params,
    };

    let node_req = node_req
        .header(hyper::header::CONTENT_TYPE, "application/json")
        .body(Body::from(serde_json::to_vec(&req_obj).unwrap()))
        .unwrap();

    log::debug!("jsonrpc_request_client: {} {}", uri, method);

    let json = tokio::time::timeout(std::time::Duration::from_millis(timeout), async {
        let resp = client.request(node_req).await.unwrap();
        let body = hyper::body::aggregate(resp).await.unwrap();
        let json: JsonRpcResponseInternal<R> = serde_json::from_reader(body.reader()).unwrap();

        json
    })
    .await
    .map_err(|e| e.to_string())?;

    if json.error.is_some() {
        return Err(json.error.unwrap().message);
    }

    if json.result.is_none() {
        return Err("no result in response".to_string());
    }

    Ok(json.result.unwrap())
}
