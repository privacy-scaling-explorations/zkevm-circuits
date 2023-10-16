use eth_types::keccak256;
use eyre::{ensure, Result};
use hyper::{
    body::{self},
    service::{make_service_fn, service_fn},
    Body, Client, Request, Response, Server,
};
use serde::Deserialize;
use std::{convert::Infallible, path::Path};

pub const ORACLE_URL : &str = "http://localhost:3000";

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

const CACHE_PATH: &str = "cache";

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

    let cache_path = Path::new(CACHE_PATH);
    std::fs::create_dir_all(cache_path)?;
    let file_id = hex::encode(keccak256(request_body_json.name().as_bytes()));
    let file_path = cache_path.join(Path::new(&file_id));

    let response_body = if let Ok(response_body) = std::fs::read(&file_path) {
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
                if !["host", "accept-encoding", "date"].contains(&key.as_str()){
                    req.headers_mut().append(key, value);
                }
            }
        }

        let resp = client.request(req).await?;
        let (head, response_body) = resp.into_parts();
        ensure!(head.status.is_success(), "Provider does not return 200");

        let response_bytes = body::to_bytes(response_body).await?.to_vec();

        std::fs::write(file_path, &response_bytes)?;

        response_bytes.to_vec()
    };

    let response = Response::builder()
        .status(200)
        .body(Body::from(response_body))?;

    Ok(response)
}

pub async fn run_oracle() -> Result<()> {
    let make_svc =
        make_service_fn(|_conn| async { Ok::<_, Infallible>(service_fn(infallible_web3_proxy)) });

    let addr = ([127, 0, 0, 1], 3000).into();

    Server::bind(&addr).serve(make_svc).await?;

    Ok(())
}

pub fn oracle_url() -> String {
    format!("http://localhost:3000")
}

pub fn spawn_oracle() -> Result<()> {
    std::process::Command::new(std::env::current_exe()?)
        .args(["--oracle"])
        .spawn()?;
    Ok(())
}
