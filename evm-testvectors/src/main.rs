mod abi;
mod code_cache;
mod lllc;
mod statetest;
mod yaml;

use crate::lllc::Lllc;
use crate::yaml::YamlStateTestBuilder;
use anyhow::{bail, Result};
use eth_types::evm_types::{Gas, OpcodeId};
use statetest::StateTestConfig;
use rayon::prelude::*;

/// This crate helps to execute the common ethereum tests located in https://github.com/ethereum/tests

/// # Errors
fn run_yaml_state_tests(yaml: &str, config: &StateTestConfig, lllc: Lllc) -> Result<()> {

    // generate all combinations of tests specified in the yaml
    let tcs = match YamlStateTestBuilder::new(lllc).from_yaml(yaml) {
        Err(err) => {
            log::error!("{:?}", err);
            return Ok(());
        }
        Ok(tcs) => tcs,
    };

    // let skip = ["mul_d8(stack_underflow)_g0_v0", "pop_d1(pop2)_g0_v0"];
    let skip = Vec::new();

    // for each test
    let _ : Vec<_> = tcs.into_par_iter().map(|tc| {
        let id = tc.id.to_string();
        if !skip.contains(&id.as_str()) {
        if let Err(err) = tc.run(config) {
            log::warn!(target: "vmvectests", "FAILED test {} : {:?}",id, err);
        } else {
            log::info!(target: "vmvectests", "SUCCESS test {}",id);
        }}

    }).collect();
    Ok(())
}

fn main() -> Result<()> {
    let config = StateTestConfig {
        max_gas: Gas(1000000),
        unimplemented_opcodes: vec![
            OpcodeId::EXP,
            OpcodeId::DELEGATECALL,
            OpcodeId::CODECOPY,
            OpcodeId::CODESIZE,
            OpcodeId::ADDMOD,
            OpcodeId::SDIV,
            OpcodeId::SMOD,
            OpcodeId::MULMOD,
            OpcodeId::NOT,
            OpcodeId::LOG1,
            OpcodeId::LOG2,
            OpcodeId::LOG3,
            OpcodeId::LOG4,
            OpcodeId::LOG0,
        ],
    };

    env_logger::Builder::from_env(env_logger::Env::default().default_filter_or("info")).init();

    let files = glob::glob("tests/src/GeneralStateTestsFiller/VMTests/vmArithmeticTest/**/*.yml")
        .expect("Failed to read glob pattern");
    for file in files {
        run_yaml_state_tests(
            &std::fs::read_to_string(file?.as_path())?,
            &config,
            lllc::Lllc::default()
                .with_docker_lllc()
                .with_default_cache()?,
        )?;
    }

    Ok(())
}
