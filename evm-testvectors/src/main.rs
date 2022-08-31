mod abi;
mod compiler;
mod config;
mod result_cache;
mod statetest;
mod testme;
mod utils;

use anyhow::{bail, Result};
use clap::Parser;
use compiler::Compiler;
use config::Config;
use result_cache::ResultCache;
use statetest::{load_statetests_suite, run_statetests_suite, StateTest, StateTestConfig};
use std::path::PathBuf;
use zkevm_circuits::test_util::BytecodeTestConfig;

#[macro_use]
extern crate prettytable;

/// EVM test vectors utility
#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct Args {
    /// Path of test files
    #[clap(short, long, default_value = "tests/src/GeneralStateTestsFiller/**")]
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

    /// cache
    #[clap(short, long)]
    cache: bool,
}

/// This crate helps to execute the common ethereum tests located in https://github.com/ethereum/tests

const RESULT_CACHE: &str = "result.cache";

fn run_single_test(test: StateTest, config: StateTestConfig) -> Result<()> {
    println!("{}", &test);

    let trace = test.clone().geth_trace()?;
    crate::utils::print_trace(trace)?;
    println!("result={:?}", test.run(config));

    Ok(())
}

fn run_bytecode(code: &str, bytecode_test_config: BytecodeTestConfig) -> Result<()> {
    use eth_types::bytecode;
    use mock::TestContext;
    use std::str::FromStr;
    use zkevm_circuits::test_util::run_test_circuits;

    let bytecode = if let Ok(bytes) = hex::decode(code) {
        match bytecode::Bytecode::try_from(bytes.clone()) {
            Ok(bytecode) => {
                for op in bytecode.iter() {
                    println!("{}", op.to_string());
                }
                bytecode
            }
            Err(err) => {
                println!("Failed to parse bytecode {:?}", err);
                bytecode::Bytecode::from_raw_unsafe(bytes)
            }
        }
    } else {
        let mut bytecode = bytecode::Bytecode::default();
        for op in code.split(';') {
            let op = bytecode::OpcodeWithData::from_str(op.trim()).unwrap();
            bytecode.append_op(op);
        }
        println!("{}\n", hex::encode(bytecode.code()));
        bytecode
    };

    let result = run_test_circuits(
        TestContext::<2, 1>::simple_ctx_with_bytecode(bytecode)?,
        Some(bytecode_test_config),
    );

    println!("Execution result is : {:?}", result);

    Ok(())
}

fn main() -> Result<()> {
    //  RAYON_NUM_THREADS=1 RUST_BACKTRACE=1 cargo run -- --path
    // "tests/src/GeneralStateTestsFiller/**/" --skip-state-circuit

    let mut config = Config::load()?;
    let args = Args::parse();

    let bytecode_test_config = BytecodeTestConfig {
        enable_state_circuit_test: !args.skip_state_circuit,
        ..Default::default()
    };

    let statetest_config = StateTestConfig {
        run_circuit: !args.skip_circuit,
        bytecode_test_config: bytecode_test_config.clone(),
        config: config.clone(),
    };

    if let Some(raw) = &args.raw {
        run_bytecode(raw, bytecode_test_config)?;
        return Ok(());
    }

    env_logger::Builder::from_env(env_logger::Env::default().default_filter_or("info")).init();

    log::info!("Parsing and compliling tests...");
    let compiler = Compiler::new(true, Some(PathBuf::from("./code.cache")))?;

    if let Some(test_id) = args.test {
        config.skip_test.clear();
        let state_tests = load_statetests_suite(&args.path, config, compiler)?;
        let mut state_tests: Vec<_> = state_tests
            .into_iter()
            .filter(|t| t.id == test_id)
            .collect();
        if state_tests.is_empty() {
            bail!("test '{}' not found", test_id);
        }
        run_single_test(state_tests.remove(0), statetest_config)?;
    } else {
        let state_tests = load_statetests_suite(&args.path, config, compiler)?;
        let mut results = if args.cache {
            let results = ResultCache::with_file(PathBuf::from(RESULT_CACHE))?;
            results.write_sorted()?;
            results
        } else {
            ResultCache::with_memory()
        };
        run_statetests_suite(state_tests, statetest_config, &mut results)?;
        println!("REPORT\n{}", results.report());
        results.write_sorted()?;
    }

    Ok(())
}
