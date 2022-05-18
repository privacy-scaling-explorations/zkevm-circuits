mod abi;
mod compiler;
mod json;
mod result_cache;
mod statetest;
mod utils;
mod yaml;

use crate::compiler::Compiler;
use crate::yaml::YamlStateTestBuilder;
use anyhow::{bail, Result};
use clap::Parser;
use eth_types::evm_types::Gas;
use rayon::prelude::*;
use result_cache::ResultCache;
use statetest::{StateTest, StateTestConfig, StateTestError};
use std::path::PathBuf;
use std::sync::Arc;
use std::sync::RwLock;
use zkevm_circuits::test_util::BytecodeTestConfig;

use crate::utils::config_bytecode_test_config;

#[macro_use]
extern crate prettytable;

/// EVM test vectors utility
#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct Args {
    /// Path of test files
    #[clap(
        short,
        long,
        default_value = "tests/src/GeneralStateTestsFiller/VMTests/**"
    )]
    path: String,

    /// Test to execute
    #[clap(short, long)]
    test: Option<String>,

    /// Do not run circuits
    #[clap(long, short)]
    skip_circuit: bool,

    /// Do not run circuit
    #[clap(long)]
    skip_state_circuit: bool,

    /// Raw execute bytecode
    #[clap(short, long)]
    raw: Option<String>,
}

const TEST_IGNORE_LIST: [&str; 0] = [];
const FILE_IGNORE_LIST: [&str; 5] = [
    "EIP1559",
    "EIP2930",
    "stExample",
    "bufferFiller.yml",    // we are using U256::as_xxx() that panics
    "ValueOverflowFiller", // weird 0x:biginteger 0x...
];

/// This crate helps to execute the common ethereum tests located in https://github.com/ethereum/tests

const RESULT_CACHE: &str = "result.cache";

fn run_test_suite(tcs: Vec<StateTest>, config: StateTestConfig) -> Result<()> {
    let results = ResultCache::new(PathBuf::from(RESULT_CACHE))?;

    let tcs: Vec<StateTest> = tcs
        .into_iter()
        .filter(|t| !results.contains(&t.id))
        .collect();

    let results = Arc::new(RwLock::from(results));

    // for each test
    tcs.into_par_iter().for_each(|tc| {
        let id = tc.id.clone();
        if TEST_IGNORE_LIST.iter().any(|t| id.as_str().contains(t)) {
            return;
        }
        if results.read().unwrap().contains(&id.as_str()) {
            return;
        }

        std::panic::set_hook(Box::new(|_info| {}));
        let result = std::panic::catch_unwind(|| tc.run(config.clone()));

        // handle panic
        let result = match result {
            Ok(res) => res,
            Err(_) => {
                log::error!(target: "vmvectests", "PANIKED test {}",id);
                results.write().unwrap().insert(&id, "00PANIK").unwrap();
                return;
            }
        };

        // handle known error
        if let Err(err) = result {
            match err {
                StateTestError::SkipUnimplementedOpcode(_)
                | StateTestError::SkipTestMaxGasLimit(_) => {
                    log::warn!(target: "vmvectests", "SKIPPED test {} : {:?}",id, err);
                    results
                        .write()
                        .unwrap()
                        .insert(&id, &format!("03SKIPPED {}", err))
                        .unwrap();
                }
                _ => {
                    log::error!(target: "vmvectests", "FAILED test {} : {:?}",id, err);
                    results
                        .write()
                        .unwrap()
                        .insert(&id, &format!("01FAILED {:?}", err))
                        .unwrap();
                }
            }
            return;
        }

        let results = std::sync::Arc::clone(&results);
        results.write().unwrap().insert(&id, "04success").unwrap();
        log::info!(target: "vmvectests", "04SUCCESS test {}",id)
    });

    Ok(())
}

fn run_single_test(test: StateTest, mut config: StateTestConfig) -> Result<()> {
    println!("{}", &test);

    let trace = test.clone().geth_trace()?;
    config_bytecode_test_config(
        &mut config.bytecode_test_config,
        trace.struct_logs.iter().map(|step| step.op),
    );
    crate::utils::print_trace(trace)?;
    println!("result={:?}", test.run(config));

    Ok(())
}

fn run_bytecode(code: &str, mut bytecode_test_config: BytecodeTestConfig) -> Result<()> {
    use eth_types::bytecode;
    use mock::TestContext;
    use std::str::FromStr;
    use zkevm_circuits::test_util::run_test_circuits;

    let bytecode = if let Ok(bytes) = hex::decode(code) {
        let bytecode = bytecode::Bytecode::try_from(bytes).expect("unable to decode bytecode");
        for op in bytecode.iter() {
            println!("{}", op.to_string());
        }
        bytecode
    } else {
        let mut bytecode = bytecode::Bytecode::default();
        for op in code.split(";") {
            let op = bytecode::OpcodeWithData::from_str(op.trim()).unwrap();
            bytecode.append_op(op);
        }
        println!("{}\n", hex::encode(bytecode.code()));
        bytecode
    };

    config_bytecode_test_config(
        &mut bytecode_test_config,
        bytecode.iter().map(|op| op.opcode()),
    );

    let result = run_test_circuits(
        TestContext::<2, 1>::simple_ctx_with_bytecode(bytecode)?,
        Some(bytecode_test_config),
    );

    println!("Execution result is : {:?}", result);

    Ok(())
}

fn main() -> Result<()> {
    //  RAYON_NUM_THREADS=1 RUST_BACKTRACE=1 cargo run -- --path
    // "tests/src/GeneralStateTestsFiller/**" --skip-state-circuit

    let args = Args::parse();

    let bytecode_test_config = BytecodeTestConfig {
        enable_state_circuit_test: !args.skip_state_circuit,
        ..Default::default()
    };

    if let Some(raw) = &args.raw {
        run_bytecode(&raw, bytecode_test_config)?;
        return Ok(());
    }

    ResultCache::new(PathBuf::from(RESULT_CACHE))?.sort()?;

    let config = StateTestConfig {
        max_gas: Gas(100000000),
        run_circuit: !args.skip_circuit,
        bytecode_test_config,
    };

    env_logger::Builder::from_env(env_logger::Env::default().default_filter_or("info")).init();

    let files = glob::glob(&format!("{}/*.yml", args.path))
        .expect("Failed to read glob pattern")
        .map(|f| f.unwrap())
        .filter(|f| {
            !FILE_IGNORE_LIST
                .iter()
                .any(|e| f.as_path().to_string_lossy().contains(e))
        });

    let mut tests = Vec::new();
    let mut compiler = Compiler::new(true, Some(PathBuf::from("./code.cache")))?;

    log::info!("Parsing and compliling tests...");
    for file in files {
        let src = std::fs::read_to_string(&file)?;
        let path = file.as_path().to_string_lossy();
        let mut tcs = match YamlStateTestBuilder::new(&mut compiler).from_yaml(&path, &src) {
            Err(err) => {
                if args.test.is_none() {
                    log::warn!("Failed to load {}: {:?}", path, err);
                }
                Vec::new()
            }
            Ok(tcs) => tcs,
        };
        tests.append(&mut tcs);
    }

    if let Some(test_id) = args.test {
        tests = tests.into_iter().filter(|t| t.id == test_id).collect();
        if tests.is_empty() {
            bail!("test '{}' not found", test_id);
        }
        let test = tests.remove(0);
        run_single_test(test, config)?;
    } else {
        run_test_suite(tests, config)?;
    }

    Ok(())
}
