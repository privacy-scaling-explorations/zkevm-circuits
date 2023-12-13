#[macro_use]
extern crate lazy_static;

use base64::{engine::general_purpose, Engine};
use eth_types::keccak256;
use eyre::{ensure, Result};
use flate2::{read::ZlibDecoder, write::ZlibEncoder, Compression};
use hyper::{
    body::{self},
    service::{make_service_fn, service_fn},
    Body, Client, Request, Response, Server,
};
use serde::Deserialize;
use std::{
    collections::HashMap,
    convert::Infallible,
    fs::File,
    io::{prelude::*, Read, Write},
};

pub const CACHE_URL: &str = "http://localhost:3000";

#[allow(dead_code)]
#[derive(Deserialize, Debug)]
struct RequestBody {
    jsonrpc: String,
    method: String,
    params: Option<Vec<Param>>,
    id: u32,
}

#[derive(Deserialize, Debug)]
#[serde(untagged)]
enum Param {
    String(String),
    Bool(bool),
    StringVec(Vec<String>),
}

lazy_static! {
    static ref CACHED: tokio::sync::Mutex<HashMap<String, Vec<u8>>> =
        tokio::sync::Mutex::new(HashMap::new());
}

impl RequestBody {
    fn name(&self) -> String {
        let params = if let Some(params) = &self.params {
            params
                .iter()
                .map(|s| match s {
                    Param::String(s) => s.to_owned(),
                    Param::Bool(b) => format!("{}", b),
                    Param::StringVec(v) => v.join(""),
                })
                .collect::<Vec<_>>()
                .join("-")
        } else {
            "".to_owned()
        };
        format!("{}_{}", self.method, params)
    }
}

const CACHE_PATH: &str = "web3_rpc_cache";

async fn infallible_web3_proxy(req: Request<Body>) -> Result<Response<Body>, Infallible> {
    match web3_proxy(req).await {
        Ok(res) => Ok(res),
        Err(err) => {
            let msg = format!("Internal Server Error: {err}");
            Ok(Response::builder()
                .status(500)
                .body(Body::from(msg))
                .unwrap())
        }
    }
}

async fn web3_proxy(req: Request<Body>) -> Result<Response<Body>> {
    let method = req.method().clone();
    let headers = req.headers().clone();
    let request_body_bytes = hyper::body::to_bytes(req.into_body()).await?.to_vec();
    let request_body_json: RequestBody = serde_json::from_slice(&request_body_bytes)?;

    let key = hex::encode(keccak256(request_body_json.name().as_bytes()));

    let response_body = CACHED.lock().await.get(&key).cloned();

    let response_body = if let Some(response_body) = response_body {
        response_body
    } else {
        let connector = hyper_rustls::HttpsConnectorBuilder::new()
            .with_native_roots()
            .https_or_http()
            .enable_http1()
            .build();

        let client = Client::builder().build(connector);
        let provider_url = std::env::var("PROVIDER_URL")?;

        let mut req = Request::builder()
            .method(method)
            .uri(provider_url)
            .body(Body::from(request_body_bytes))?;

        for (key, value) in headers {
            if let Some(key) = key {
                if !["host", "accept-encoding", "date"].contains(&key.as_str()) {
                    req.headers_mut().append(key, value);
                }
            }
        }

        let resp = client.request(req).await?;
        let (head, response_body) = resp.into_parts();
        ensure!(head.status.is_success(), "Provider does not return 200");

        let response_bytes = body::to_bytes(response_body).await?.to_vec();

        CACHED
            .lock()
            .await
            .insert(key.clone(), response_bytes.clone());

        let mut encoder = ZlibEncoder::new(Vec::new(), Compression::default());
        encoder.write_all(&response_bytes)?;
        let response_bytes_compressed_b64 = general_purpose::STANDARD.encode(encoder.finish()?);

        let mut f = File::options().append(true).create(true).open(CACHE_PATH)?;
        writeln!(&mut f, "{}={}", key, &response_bytes_compressed_b64)?;

        response_bytes
    };

    let response = Response::builder()
        .status(200)
        .body(Body::from(response_body))?;

    Ok(response)
}

#[tokio::main]
pub async fn main() -> Result<()> {
    if let Ok(mut f) = File::open(CACHE_PATH) {
        let mut buf = String::new();
        f.read_to_string(&mut buf)?;
        let kvs: Vec<_> = buf
            .lines()
            .map(|line| {
                let (k, v) = line.split_once('=').unwrap();
                let response_bytes_compressed = general_purpose::STANDARD.decode(v).unwrap();
                let mut decoder = ZlibDecoder::new(&response_bytes_compressed[..]);
                let mut buf = Vec::new();
                decoder.read_to_end(&mut buf).unwrap();
                (k.to_string(), buf)
            })
            .collect();
        println!("loaded {} cached responses", kvs.len());
        CACHED.lock().await.extend(kvs);
    }

    let make_svc =
        make_service_fn(|_conn| async { Ok::<_, Infallible>(service_fn(infallible_web3_proxy)) });

    let addr = ([127, 0, 0, 1], 3000).into();

    println!("Listening on http://{}", addr);

    Server::bind(&addr).serve(make_svc).await?;

    Ok(())
}