/// Execute the bytecode from an empty state and run the EVM and State circuits
mod abi;
mod compiler;
mod config;
mod statetest;
mod utils;

use anyhow::{bail, Result};
use clap::Parser;
use compiler::Compiler;
use config::Config;
use statetest::{load_statetests_suite, run_statetests_suite, CircuitsConfig, Results, StateTest};
use std::path::PathBuf;
use std::time::SystemTime;
use zkevm_circuits::test_util::BytecodeTestConfig;

use crate::config::TestSuite;

const REPORT_FOLDER: &str = "report";
const CODEHASH_FILE: &str = "./codehash.txt";

#[macro_use]
extern crate prettytable;

/// EVM test vectors utility
#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct Args {
    /// Suite (by default is "default")
    #[clap(long, default_value = "default")]
    suite: String,

    /// Execute only one test and dump the results
    #[clap(long)]
    inspect: Option<String>,

    /// Cache execution results
    #[clap(long)]
    cache: bool,

    /// Generates log and and html file with info.
    #[clap(long)]
    report: bool,

    /// Raw execute bytecode, can be hex `6001` or asm `PUSH1(60); PUSH1(60)`
    #[clap(long)]
    raw: Option<String>,

    /// Verbose
    #[clap(short, long)]
    v: bool,
}

const RESULT_CACHE: &str = "result.cache";

fn run_single_test(test: StateTest, circuits_config: CircuitsConfig) -> Result<()> {
    println!("{}", &test);

    let trace = test.clone().geth_trace()?;
    crate::utils::print_trace(trace)?;
    println!(
        "result={:?}",
        test.run(TestSuite::default(), circuits_config)
    );

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
                bytecode::Bytecode::from_raw_unchecked(bytes)
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

    let config = Config::load()?;
    let circuits_config = CircuitsConfig::default();

    let args = Args::parse();

    if let Some(raw) = &args.raw {
        run_bytecode(raw, circuits_config.bytecode_test_config)?;
        return Ok(());
    }

    env_logger::Builder::from_env(env_logger::Env::default().default_filter_or("info")).init();

    log::info!("Using suite '{}'", args.suite);
    log::info!("Parsing and compliling tests...");
    let compiler = Compiler::new(true, Some(PathBuf::from(CODEHASH_FILE)))?;
    let suite = config.suite(&args.suite)?.clone();
    let state_tests = load_statetests_suite(&suite.path, config, compiler)?;
    log::info!("{} tests collected in {}", state_tests.len(), suite.path);

    if let Some(test_id) = args.inspect {
        // Test only one and return
        let mut state_tests: Vec<_> = state_tests
            .into_iter()
            .filter(|t| t.id == test_id)
            .collect();
        if state_tests.is_empty() {
            bail!("test '{}' not found", test_id);
        }
        run_single_test(state_tests.remove(0), circuits_config)?;
        return Ok(());
    };

    if args.report {
        if args.cache {
            bail!("--cache is not compartible with --report");
        }

        let git_hash = utils::current_git_commit()?;
        let timestamp = SystemTime::now()
            .duration_since(SystemTime::UNIX_EPOCH)
            .unwrap()
            .as_secs();

        std::fs::create_dir_all(REPORT_FOLDER)?;
        let csv_filename = format!("{}/{}.{}.csv", REPORT_FOLDER, timestamp, git_hash);
        let html_filename = format!("{}/{}.{}.html", REPORT_FOLDER, timestamp, git_hash);

        let mut results = Results::with_cache(PathBuf::from(csv_filename))?;

        run_statetests_suite(state_tests, &circuits_config, &suite, &mut results)?;

        // filter non-csv files and files from the same commit
        let mut files: Vec<_> = std::fs::read_dir(REPORT_FOLDER)
            .unwrap()
            .filter_map(|f| {
                let filename = f.unwrap().file_name().to_str().unwrap().to_string();
                (filename.ends_with(".csv") && !filename.contains(&format!(".{}.", git_hash)))
                    .then_some(filename)
            })
            .collect();

        files.sort_by(|f, s| s.cmp(f));
        let previous = if !files.is_empty() {
            let file = files.remove(0);
            println!("Comparing with previous results in {}", file);
            let path = format!("{}/{}", REPORT_FOLDER, file);
            Some((file, Results::from_file(PathBuf::from(path))?))
        } else {
            None
        };

        let report = results.report(previous);
        std::fs::write(&html_filename, report.gen_html()?)?;

        println!("{}", html_filename);
    } else {
        let mut results = if args.cache {
            Results::with_cache(PathBuf::from(RESULT_CACHE))?
        } else {
            Results::default()
        };

        log::info!("Executing...");
        run_statetests_suite(state_tests, &circuits_config, &suite, &mut results)?;
        let success = results.success();

        log::info!("Generating report...");
        results.report(None).print_tty()?;

        if !success {
            std::process::exit(1);
        }
    }

    Ok(())
}
