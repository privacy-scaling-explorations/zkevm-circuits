mod code_cache;
mod exec;
mod lllc;
mod statetest;
mod statetest_yaml;

use crate::lllc::Lllc;
use crate::statetest_yaml::YamlStateTestBuilder;
use anyhow::{bail, Result};

/// This crate helps to execute the common ethereum tests located in https://github.com/ethereum/tests

/// # Errors
fn run_yaml_state_tests(yaml: &str, lllc: Lllc) -> Result<()> {
    let mut failed = 0;

    // generate all combinations of tests specified in the yaml
    let tcs = YamlStateTestBuilder::new(lllc).from_yaml(yaml)?;

    // for each test
    for tc in tcs {
        let id = tc.id.to_string();

        if let Some(err) = tc.run().err() {
            log::error!(target: "vmvectests", "FAILED test {} : {}",id, err);
            failed += 1;
        } else {
            log::info!(target: "vmvectests", "OK test {}", id);
        }
    }

    if failed > 0 {
        bail!("{} tests failed", failed);
    }
    Ok(())
}

fn main() -> Result<()> {
    env_logger::Builder::from_env(env_logger::Env::default().default_filter_or("info")).init();

    run_yaml_state_tests(
        include_str!("../tests/src/GeneralStateTestsFiller/VMTests/vmArithmeticTest/addFiller.yml"),
        lllc::Lllc::default()
            .with_docker_lllc()
            .with_default_cache()?,
    )?;
    Ok(())
}
