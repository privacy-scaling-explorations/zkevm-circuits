use env_logger::Env;
use std::env::var;

use prover::compute_proof::compute_witness;

/// This command generates and prints the witness for a given block to stdout.
/// Required environment variables:
/// - BLOCK_NUM - the block number to generate the proof for
/// - RPC_URL - a geth http rpc that supports the debug namespace
#[tokio::main]
async fn main() {
    env_logger::Builder::from_env(Env::default().default_filter_or("info")).init();

    let block_num: u64 = var("BLOCK_NUM")
        .expect("BLOCK_NUM env var")
        .parse()
        .expect("Cannot parse BLOCK_NUM env var");
    let rpc_url: String = var("RPC_URL")
        .expect("RPC_URL env var")
        .parse()
        .expect("Cannot parse RPC_URL env var");

    let result = compute_witness(&block_num, &rpc_url)
        .await
        .expect("witness");
    serde_json::to_writer(std::io::stdout(), &result).expect("serialize and write");
}
