#![feature(test)]
use eth_types::{
    geth_types::{Account, BlockConstants, GethData, RawAccount},
    Address, Block, Error, Transaction, H160, U256,
};
use external_tracer::{trace, TraceConfig};
use halo2_proofs::dev::MockProver;
use itertools::Itertools;
use mock::test_ctx::LoggerConfig;
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
use serde_json::Value;
use std::{
    collections::HashMap, convert::TryInto, env, fs::File, io::Read, path::Path, string::String,
};
use zkevm_circuits::super_circuit::SuperCircuit;

fn load_json_rpc_result(path: &Path) -> Value {
    let mut file = File::open(path).unwrap();
    let mut string = String::default();
    file.read_to_string(&mut string).unwrap();

    let output: Value = serde_json::from_str(&string)
        .map_err(Error::SerdeError)
        .unwrap();
    output
}

const BLOCK_FILE: &'static str = "block.json";
const BLOCK_HASH_FILE: &'static str = "block_hashes.json";
const PRESTATE_FILE: &'static str = "prestate.json";

/// `cargo run --bin apply_block <dir_path>`

pub fn main() {
    let mut args = env::args();
    let path_arg = args.next_back().expect("path to directory");
    let dir_path = Path::new(&path_arg);

    let mut block: Block<Transaction> =
        serde_json::from_value(load_json_rpc_result(&dir_path.join(BLOCK_FILE))).unwrap();

    // Need to mock base fee
    block.base_fee_per_gas = Some(U256::zero());
    println!("block {:#?}", block);
    let history_hashes: Vec<U256> = {
        let mut hashes: Vec<U256> =
            serde_json::from_value(load_json_rpc_result(&dir_path.join(BLOCK_HASH_FILE))).unwrap();
        let block_num: usize = block.number.unwrap().as_u64().try_into().unwrap();

        if block_num < hashes.len() {
            hashes.drain((hashes.len() - block_num)..).collect()
        } else {
            hashes
        }
    };
    let state: Value = load_json_rpc_result(&dir_path.join(PRESTATE_FILE));
    let state: HashMap<H160, RawAccount> =
        serde_json::from_value(state[0]["result"].clone()).unwrap();
    let accounts: HashMap<Address, Account> = state
        .iter()
        .map(|(&address, raw_acc)| {
            (
                address,
                Account {
                    address,
                    nonce: raw_acc.nonce.into(),
                    balance: raw_acc.balance,
                    code: raw_acc.code.clone(),
                    storage: raw_acc.storage.clone(),
                },
            )
        })
        .collect();

    let chain_id = block.transactions[0].chain_id.unwrap();
    let logger_config = LoggerConfig::default();
    let trace_config = TraceConfig {
        chain_id,
        history_hashes: history_hashes.clone(),
        block_constants: BlockConstants::try_from(&block).unwrap(),
        accounts: accounts.clone(),
        transactions: block.transactions.iter().map(|tx| tx.into()).collect_vec(),
        logger_config,
    };
    let geth_traces = trace(&trace_config).unwrap();

    let geth_data = GethData {
        chain_id,
        history_hashes,
        eth_block: block,
        geth_traces: geth_traces,
        accounts: accounts.values().cloned().collect_vec(),
    };

    let (k, circuit, instance) =
        SuperCircuit::<_, 2, 32>::build(geth_data, &mut ChaCha20Rng::seed_from_u64(2)).unwrap();
    println!("k {:?}", k);
    println!("instance len {:?}", instance.len());

    let prover = MockProver::run(k, &circuit, instance).unwrap();
    prover.assert_satisfied();
}
