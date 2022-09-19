use eth_types::{
    address,
    geth_types::{Account2, BlockConstants, GethData, Transaction},
    Address, Error, GethExecTrace, Word, H160, H256, U256,
};
use eth_types::{Block as Blk, Transaction as Txn};
use mock::{test_ctx::LoggerConfig, TestContext};
use serde_json::Value;
use std::{collections::HashMap, convert::TryInto, fs::File, io::Read, ops::Deref, string::String};
use zkevm_circuits::{
    test_util::{run_test_circuits, test_circuits_using_witness_block, BytecodeTestConfig},
    witness::Block,
};

fn load_json_rpc_result(path: &str) -> Value {
    let mut file = File::open(path).unwrap();
    let mut trace_string = String::default();
    file.read_to_string(&mut trace_string).unwrap();

    let output: Value = serde_json::from_str(&trace_string)
        .map_err(Error::SerdeError)
        .unwrap();
    output
}

/// `cargo run -p zkevm-circuits --features test`
pub fn main() {
    let history_hashes = load_json_rpc_result("block27/block_hashes.json");
    let history_hashes: Vec<U256> = serde_json::from_value(history_hashes).unwrap();
    let state = load_json_rpc_result("block27/prestate.json");
    let state: HashMap<H160, Account2> =
        serde_json::from_value(state[0]["result"].clone()).unwrap();

    let block = load_json_rpc_result("block27/block.json");
    let mut block: Blk<Txn> = serde_json::from_value(block.clone()).unwrap();

    // Need to mock base fee
    block.base_fee_per_gas = Some(U256::zero());
    println!("block {:?}", block);

    let config = BytecodeTestConfig {
        enable_evm_circuit_test: true,
        enable_state_circuit_test: false,
        gas_limit: 1_000_000u64,
    };

    let ctx = TestContext::<2, 2>::new_with_state_and_block(
        Some(history_hashes),
        state,
        block,
        LoggerConfig::default(),
    )
    .unwrap()
    .into();

    run_test_circuits(ctx, Some(config)).unwrap()
}
