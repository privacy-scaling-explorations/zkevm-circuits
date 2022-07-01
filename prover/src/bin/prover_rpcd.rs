use env_logger::Env;
use hyper::body::Buf;
use hyper::body::HttpBody;
use hyper::header::HeaderValue;
use hyper::service::{make_service_fn, service_fn};
use hyper::{Body, Method, Request, Response, Server, StatusCode};
use std::env::var;

use prover::shared_state::SharedState;
use prover::structs::*;

/// sets default headers for CORS requests
fn set_headers(headers: &mut hyper::HeaderMap, extended: bool) {
    headers.insert("content-type", HeaderValue::from_static("application/json"));
    headers.insert("access-control-allow-origin", HeaderValue::from_static("*"));

    if extended {
        headers.insert(
            "access-control-allow-methods",
            HeaderValue::from_static("post, get, options"),
        );
        headers.insert(
            "access-control-allow-headers",
            HeaderValue::from_static("origin, content-type, accept, x-requested-with"),
        );
        headers.insert("access-control-max-age", HeaderValue::from_static("300"));
    }
}

async fn handle_request(
    shared_state: SharedState,
    req: Request<Body>,
) -> Result<Response<Body>, hyper::Error> {
    {
        // limits the request size
        const MAX_BODY_SIZE: u64 = 1 << 20;
        let response_content_length = match req.body().size_hint().upper() {
            Some(v) => v,
            None => MAX_BODY_SIZE + 1,
        };

        if response_content_length > MAX_BODY_SIZE {
            let mut resp = Response::new(Body::from("request too large"));
            *resp.status_mut() = StatusCode::BAD_REQUEST;
            return Ok(resp);
        }
    }

    match (req.method(), req.uri().path()) {
        (&Method::GET, "/health") => {
            // nothing to report yet - healthy by default
            let mut resp = Response::default();
            set_headers(resp.headers_mut(), false);
            Ok(resp)
        }

        // returns http 200 if busy else 204.
        // can be used programmatically for e.g. shutting down the instance if no workis being
        // done.
        (&Method::GET, "/status") => {
            let rw = shared_state.rw.lock().await;
            let is_busy = rw.pending_tasks > 0 || rw.tasks.iter().any(|e| e.result.is_none());
            drop(rw);

            let mut resp = Response::default();
            *resp.status_mut() = match is_busy {
                false => StatusCode::NO_CONTENT,
                true => StatusCode::OK,
            };
            set_headers(resp.headers_mut(), false);
            Ok(resp)
        }

        // json-rpc
        (&Method::POST, "/") => {
            let body_bytes = hyper::body::aggregate(req.into_body())
                .await
                .unwrap()
                .reader();
            let json_req: Result<JsonRpcRequest<Vec<serde_json::Value>>, serde_json::Error> =
                serde_json::from_reader(body_bytes);

            if let Err(err) = json_req {
                let payload = serde_json::to_vec(&JsonRpcResponseError {
                    jsonrpc: "2.0".to_string(),
                    id: 0.into(),
                    error: JsonRpcError {
                        // parser error
                        code: -32700,
                        message: err.to_string(),
                    },
                })
                .unwrap();
                let mut resp = Response::new(Body::from(payload));
                set_headers(resp.headers_mut(), false);
                return Ok(resp);
            }

            let json_req = json_req.unwrap();
            let result: Result<serde_json::Value, String> =
                handle_method(json_req.method.as_str(), &json_req.params, &shared_state).await;
            let payload = match result {
                Err(err) => {
                    serde_json::to_vec(&JsonRpcResponseError {
                        jsonrpc: "2.0".to_string(),
                        id: json_req.id,
                        error: JsonRpcError {
                            // internal server error
                            code: -32000,
                            message: err,
                        },
                    })
                }
                Ok(val) => serde_json::to_vec(&JsonRpcResponse {
                    jsonrpc: "2.0".to_string(),
                    id: json_req.id,
                    result: val,
                }),
            };
            let mut resp = Response::new(Body::from(payload.unwrap()));
            set_headers(resp.headers_mut(), false);
            Ok(resp)
        }

        // serve CORS headers
        (&Method::OPTIONS, "/") => {
            let mut resp = Response::default();
            set_headers(resp.headers_mut(), true);
            Ok(resp)
        }

        // everything else
        _ => {
            let mut not_found = Response::default();
            *not_found.status_mut() = StatusCode::NOT_FOUND;
            Ok(not_found)
        }
    }
}

async fn handle_method(
    method: &str,
    params: &[serde_json::Value],
    shared_state: &SharedState,
) -> Result<serde_json::Value, String> {
    match method {
        // enqueues a task for computating proof for any given block
        "proof" => {
            let options = params.get(0).ok_or("expected struct ProofRequestOptions")?;
            let options: ProofRequestOptions =
                serde_json::from_value(options.to_owned()).map_err(|e| e.to_string())?;

            match shared_state.get_or_enqueue(&options).await {
                // No error
                None => Ok(serde_json::Value::Null),
                Some(result) => {
                    if let Err(err) = result {
                        return Err(err);
                    }

                    Ok(serde_json::to_value(result.unwrap()).unwrap())
                }
            }
        }
        // TODO/TBD: add method to only return the witnesses for a block.
        //  block table, tx table, etc...
        //
        // TODO: Add the abilitity to abort the current task.

        // the following methods can be used to programmatically
        // prune the `tasks` from the list.
        "flushAll" => {
            shared_state.rw.lock().await.tasks.clear();
            Ok(serde_json::Value::Bool(true))
        }
        "flushPending" => {
            shared_state
                .rw
                .lock()
                .await
                .tasks
                .retain(|e| e.result.is_some());
            Ok(serde_json::Value::Bool(true))
        }
        "flushCompleted" => {
            shared_state
                .rw
                .lock()
                .await
                .tasks
                .retain(|e| e.result.is_none());
            Ok(serde_json::Value::Bool(true))
        }
        _ => Err("this method is not available".to_string()),
    }
}

/// This command starts a http/json-rpc server and serves proof oriented
/// methods. Required environment variables:
/// - BIND - the interface address + port combination to accept connections on
///   `[::]:1234`
/// - PARAMS_PATH - a path to a file generated with the gen_params tool
#[tokio::main]
async fn main() {
    env_logger::Builder::from_env(Env::default().default_filter_or("info")).init();

    let addr = var("BIND")
        .expect("BIND env var")
        .parse::<std::net::SocketAddr>()
        .expect("valid socket address");
    let shared_state = SharedState::new();

    {
        // start the http server
        let ctx = shared_state.clone();
        let h1 = tokio::spawn(async move {
            let service = make_service_fn(move |_| {
                let ctx = ctx.clone();
                let service = service_fn(move |req| handle_request(ctx.clone(), req));

                async move { Ok::<_, hyper::Error>(service) }
            });
            let server = Server::bind(&addr).serve(service);
            log::info!("Listening on http://{}", addr);
            server.await.expect("server should be serving");
        });

        // starts the duty cycle loop
        let ctx = shared_state.clone();
        // use a dedicated runtime for mixed async / heavy (blocking) compute
        let rt = tokio::runtime::Builder::new_multi_thread()
            .enable_all()
            .build()
            .unwrap();
        let h2 = rt.spawn(async move {
            let ctx = ctx.clone();
            loop {
                ctx.duty_cycle().await;
                tokio::time::sleep(std::time::Duration::from_millis(1000)).await;
            }
        });

        // wait for all tasks
        let _ = tokio::join!(h1, h2);
    }
}
