mod abi;
mod code_cache;
mod lllc;
mod result_cache;
mod statetest;
mod yaml;

use crate::lllc::Lllc;
use crate::yaml::YamlStateTestBuilder;
use anyhow::{bail, Result};
use clap::Parser;
use eth_types::evm_types::{Gas, OpcodeId};
use rayon::prelude::*;
use result_cache::ResultCache;
use statetest::{StateTest, StateTestConfig, StateTestError};
use std::path::PathBuf;
use std::sync::Arc;
use std::sync::RwLock;

#[macro_use]
extern crate prettytable;
use prettytable::Table;

// see https://github.com/appliedzkp/zkevm-circuits/issues/477
const UNIMPLEMENTED_OPCODES: [OpcodeId; 31] = [
    OpcodeId::SDIV,
    OpcodeId::SMOD,
    OpcodeId::ADDMOD,
    OpcodeId::MULMOD,
    OpcodeId::EXP,
    OpcodeId::NOT,
    OpcodeId::CODESIZE,
    OpcodeId::SHL,
    OpcodeId::SHR,
    OpcodeId::SAR,
    OpcodeId::RETURN,
    OpcodeId::REVERT,
    OpcodeId::SHA3,
    OpcodeId::ADDRESS,
    OpcodeId::BALANCE,
    OpcodeId::EXTCODESIZE,
    OpcodeId::EXTCODECOPY,
    OpcodeId::RETURNDATASIZE,
    OpcodeId::RETURNDATACOPY,
    OpcodeId::BLOCKHASH,
    OpcodeId::LOG1,
    OpcodeId::LOG2,
    OpcodeId::LOG3,
    OpcodeId::LOG4,
    OpcodeId::LOG0,
    OpcodeId::CREATE,
    OpcodeId::CREATE2,
    OpcodeId::CALLCODE,
    OpcodeId::DELEGATECALL,
    OpcodeId::STATICCALL,
    OpcodeId::SELFDESTRUCT,
];

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

    /// Dump the content and the geth log of a test (needs --test)
    #[clap(short, long)]
    explain: bool,

    /// Do not run circuit
    #[clap(short, long)]
    skip_circuit: bool,

    /// Raw execute bytecode
    #[clap(short, long)]
    raw: Option<String>,
}

/// This crate helps to execute the common ethereum tests located in https://github.com/ethereum/tests

const RESULT_CACHE: &str = "result.cache";

/// # Errors
fn run_tests(tcs: Vec<StateTest>, config: &StateTestConfig, verbose: bool) -> Result<()> {
    let results = ResultCache::new(PathBuf::from(RESULT_CACHE))?;

    let tcs: Vec<StateTest> = tcs
        .into_iter()
        .filter(|t| !results.contains(&t.id))
        .collect();

    let results = Arc::new(RwLock::from(results));

    // for each test
    tcs.into_par_iter().for_each(|tc| {
        let id = tc.id.to_string();
        if results.read().unwrap().contains(&id.as_str()) {
            return;
        }

        let result = if verbose {
            tc.run(config)
        } else {
            std::panic::set_hook(Box::new(|_info| {}));
            let result = std::panic::catch_unwind(|| tc.run(config));

            // handle panic
            match result {
                Ok(res) => res,
                Err(_) => {
                    log::error!(target: "vmvectests", "PANIKED test {}",id);
                    return;
                }
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
                        .insert(&id, &format!("{}", err))
                        .unwrap();
                }
                _ => log::error!(target: "vmvectests", "FAILED test {} : {:?}",id, err),
            }
            return;
        }

        let results = std::sync::Arc::clone(&results);
        results.write().unwrap().insert(&id, "success").unwrap();
        log::info!(target: "vmvectests", "SUCCESS test {}",id)
    });

    Ok(())
}

fn explain_test(test: &StateTest) -> Result<()> {
    // Create the table

    println!("{}", &test);

    let trace = test.clone().geth_trace()?;
    let mut table = Table::new();
    table.add_row(row![
        "PC", "OP", "GAS", "GAS_COST", "DEPTH", "ERR", "STACK", "MEMORY", "STORAGE"
    ]);
    for step in trace.struct_logs {
        table.add_row(row![
            format!("{}", step.pc.0),
            format!("{:?}", step.op),
            format!("{}", step.gas.0),
            format!("{}", step.gas_cost.0),
            format!("{}", step.depth),
            step.error.unwrap_or("".to_string()),
            format!("{:?}", step.stack),
            format!("{:?}", step.memory),
            format!("{:?}", step.storage)
        ]);
    }

    println!("FAILED: {:?}", trace.failed);
    println!("GAS: {:?}", trace.gas);
    table.printstd();
    Ok(())
}

fn run_bytecode(code: &str) -> Result<()> {
    use eth_types::bytecode;
    use mock::TestContext;
    use zkevm_circuits::test_util::{BytecodeTestConfig, run_test_circuits};

    let bytecode = if let Ok(bytes) = hex::decode(code) {
        let bytecode = bytecode::Bytecode::try_from(bytes).expect("unable to decode bytecode");
        println!("{}\n", bytecode.disasm());
        bytecode
    } else {
        let mut bytecode = bytecode::Bytecode::default();
        for op in code.split(";") {
            bytecode.append_asm(op.trim());
        }
        println!("{}\n", hex::encode(bytecode.code()));
        bytecode
    };
            let test_config = BytecodeTestConfig {
                enable_state_circuit_test: false,
                ..Default::default()
            };
 
    let result = run_test_circuits(
        TestContext::<2, 1>::simple_ctx_with_bytecode(bytecode)?,
        Some(test_config),
    );

    println!("Execution result is : {:?}", result);

    Ok(())
}

fn main() -> Result<()> {
    let args = Args::parse();

    if let Some(raw) = args.raw {
        run_bytecode(&raw)?;
        return Ok(());
    }

    ResultCache::new(PathBuf::from(RESULT_CACHE))?.sort()?;

    let config = StateTestConfig {
        max_gas: Gas(1000000),
        run_circuit: !args.skip_circuit,
        unimplemented_opcodes: UNIMPLEMENTED_OPCODES.into(),
    };

    env_logger::Builder::from_env(env_logger::Env::default().default_filter_or("info")).init();

    let files = glob::glob(&format!("{}/*.yml", args.path)).expect("Failed to read glob pattern");

    let mut tests = Vec::new();
    let mut lllc = Lllc::default().with_docker_lllc().with_default_cache()?;

    log::info!("Parsing and compliling tests...");
    for file in files {
        let file = file?;
        let src = std::fs::read_to_string(&file)?;
        let path = file.as_path().to_string_lossy();
        let mut tcs = match YamlStateTestBuilder::new(&mut lllc).from_yaml(&path, &src) {
            Err(err) => {
                log::warn!("Failed to load {}: {:?}", path, err);
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
        explain_test(&tests[0])?;
        run_tests(tests, &config, true)?;
    } else {
        run_tests(tests, &config, false)?;
    }

    Ok(())
}
