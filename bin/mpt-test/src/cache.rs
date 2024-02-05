//! A simple cache for web3 rpc requests

use eth_types::keccak256;
use eyre::{ensure, eyre, Result};
use flate2::{read::ZlibDecoder, write::ZlibEncoder, Compression};
use hyper::{
    body::{self},
    service::{make_service_fn, service_fn},
    Body, Client, Request, Response, Server,
};
use serde::Deserialize;
use serde_json::Value;
use std::{
    collections::HashMap,
    convert::Infallible,
    fs::File,
    io::{Read, Seek, Write},
};

const CACHE_PATH: &str = "web3_rpc_cache.bin";

lazy_static! {
    static ref CACHE: tokio::sync::Mutex<CacheFile> = tokio::sync::Mutex::new(CacheFile::new());
}

/// Cache file format is a consecutive list of entries, each entry is:
/// - 32 bytes: key (keccak256 of the request)
/// - 4 bytes: length of the compressed response
/// - N bytes: compressed response
struct CacheFile {
    offsets: HashMap<[u8; 32], u64>,
}
impl CacheFile {
    pub fn new() -> Self {
        Self {
            offsets: HashMap::new(),
        }
    }
    /// Load all existing entries from the cache file
    pub async fn load(&mut self) -> Result<()> {
        if let Ok(mut f) = File::open(CACHE_PATH) {
            let mut hash = [0u8; 32];
            while f.read_exact(&mut hash).is_ok() {
                let offset = f.stream_position()?;
                self.offsets.insert(hash, offset);
                let mut len_buf = [0u8; 4];
                f.read_exact(&mut len_buf)?;
                let len = u32::from_le_bytes(len_buf);
                f.seek(std::io::SeekFrom::Current(len as i64))?;
            }
            println!("loaded {} cached responses", self.offsets.len());
        }
        Ok(())
    }
    /// Write a new entry
    async fn write(&mut self, key: [u8; 32], value: &[u8]) -> Result<()> {
        let mut encoder = ZlibEncoder::new(Vec::new(), Compression::best());
        encoder.write_all(value)?;
        let compressed = encoder.finish()?;

        let mut f = File::options().append(true).create(true).open(CACHE_PATH)?;
        f.write_all(&key)?;
        let offset = f.stream_position()?;
        f.write_all(&(compressed.len() as u32).to_le_bytes())?;
        f.write_all(&compressed)?;

        self.offsets.insert(key, offset);

        Ok(())
    }
    /// Read an entry, returns Ok(None) if not found
    async fn read(&self, key: [u8; 32]) -> Result<Option<Vec<u8>>> {
        let offset = self.offsets.get(&key).cloned();
        if let Some(offset) = offset {
            let mut f =
                File::open(CACHE_PATH).expect("since offset exists, file should exist. qed.");
            f.seek(std::io::SeekFrom::Start(offset))?;

            let mut len_buf = [0u8; 4];
            f.read_exact(&mut len_buf)?;
            let len = u32::from_le_bytes(len_buf);

            let mut compressed = vec![0u8; len as usize];
            f.read_exact(&mut compressed)?;
            let mut decoder = ZlibDecoder::new(&compressed[..]);
            let mut decompressed: Vec<u8> = Vec::new();
            decoder.read_to_end(&mut decompressed).unwrap();

            Ok(Some(decompressed))
        } else {
            Ok(None)
        }
    }
}

#[derive(Deserialize, Debug)]
struct RequestBody {
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

impl RequestBody {
    fn hash(&self) -> [u8; 32] {
        let params = if let Some(params) = &self.params {
            params
                .iter()
                .map(|s| match s {
                    Param::String(s) => s.to_owned(),
                    Param::Bool(b) => format!("{}", b),
                    Param::StringVec(v) => v.join("-"),
                })
                .collect::<Vec<_>>()
                .join("-")
        } else {
            "".to_owned()
        };
        keccak256(format!("{}-{}", self.method, params).as_bytes())
    }
}

/// Handle a web3 rpc request with error handling
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

/// Handle a web3 rpc request, return cached result or call the env!("WEB3_PROVIDER_URL") RPC server
async fn web3_proxy(req: Request<Body>) -> Result<Response<Body>> {
    let method = req.method().clone();
    let headers = req.headers().clone();

    // try to read the result from the cache
    let request_body_bytes = hyper::body::to_bytes(req.into_body()).await?.to_vec();
    let request_body_json: RequestBody = serde_json::from_slice(&request_body_bytes)?;
    let key = request_body_json.hash();
    let response_result = CACHE.lock().await.read(key).await?;

    let response_body = if let Some(response_result) = response_result {
        // return cached result
        format!(
            "{{\"id\":{}, \"jsonrpc\":\"2.0\", \"result\":{}}}",
            request_body_json.id,
            String::from_utf8(response_result).unwrap()
        )
        .into_bytes()
    } else {
        println!(
            "=>{}",
            String::from_utf8(request_body_bytes.clone()).unwrap()
        );

        // call RPC server, copying headers and method from the original request
        let connector = hyper_rustls::HttpsConnectorBuilder::new()
            .with_native_roots()
            .https_or_http()
            .enable_http1()
            .build();

        let client = Client::builder().build(connector);
        let provider_url = std::env::var("WEB3_PROVIDER_URL")?;

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

        // parse response and cache it
        let response_bytes = body::to_bytes(response_body).await?.to_vec();

        let root: Value = serde_json::from_slice(&response_bytes)?;
        let Some(result) = root.get("result") else {
            return Err(eyre!("Provider does not return result"));
        };
        let result_bytes = serde_json::to_vec(result)?;
        CACHE.lock().await.write(key, &result_bytes).await?;

        response_bytes
    };

    // return HTTP 200 response
    let response = Response::builder()
        .status(200)
        .body(Body::from(response_body))?;

    Ok(response)
}

/// Load the cache file
pub async fn load() -> Result<()> {
    CACHE.lock().await.load().await
}

/// Start the cache server at localhost:3000
pub async fn start() -> Result<()> {
    let make_svc =
        make_service_fn(|_conn| async { Ok::<_, Infallible>(service_fn(infallible_web3_proxy)) });

    let addr = ([127, 0, 0, 1], 3000).into();

    println!("Listening on http://{}", addr);

    Server::bind(&addr).serve(make_svc).await?;

    Ok(())
}
