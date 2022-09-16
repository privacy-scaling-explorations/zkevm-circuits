use eth_types::{
    address,
    geth_types::{Account2, BlockConstants, GethData, Transaction},
    Address, Error, GethExecTrace, Word, H160, U256,
};
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
    output["result"].clone()
}

/// `cargo run -p zkevm-circuits --features test`
pub fn main() {
    let state = load_json_rpc_result("Block4_preStateTrace/Block4_preStateTrace.json");
    let state: HashMap<H160, Account2> = serde_json::from_value(state[0]["result"].clone()).unwrap();

    let trace = load_json_rpc_result("Block4_preStateTrace/Layer_2_Block_4_0xdb57ca49a9456bb6f2399a4d4797af386ee46afe6b52aa54e682f32928440cad.json");
    let trace: GethExecTrace = serde_json::from_value(trace.clone()).unwrap();

    let config = BytecodeTestConfig {
        enable_evm_circuit_test: true,
        enable_state_circuit_test: false,
        gas_limit: 1_000_000u64,
    };

    let block = TestContext::<2, 1>::new_with_logger_config2(
        None,
        |accs| {
            for (idx, (&addr, acc)) in state.iter().enumerate() {
                accs[idx]
                    .address(addr.clone())
                    .balance(acc.balance)
                    .code(acc.code.clone())
                    .nonce(U256::from(acc.nonce));
            }
        },
        |mut txs, accs| {
            txs[0].to(accs[0].address).from(accs[1].address);
        },
        |block, _tx| block.number(0xcafeu64),
        [trace]
    )
    .unwrap()
    .into();

    run_test_circuits(block, Some(config)).unwrap()
}
