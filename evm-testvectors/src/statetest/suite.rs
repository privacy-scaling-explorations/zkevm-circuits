use super::{StateTest, StateTestConfig};
use crate::compiler::Compiler;
use crate::config::Config;
use crate::result_cache::ResultCache;
use crate::statetest::JsonStateTestBuilder;
use crate::statetest::StateTestError;
use crate::statetest::YamlStateTestBuilder;
use anyhow::Result;
use rayon::prelude::*;
use std::sync::Arc;
use std::sync::RwLock;

/// tests that panicks
const LVL_PANIK : &str = "00💀PANIK"; 
/// tests that are failing
const LVL_FAIL : &str = "01🔴FAILD";
/// tests that are failing, but contains unimplemented features or known bugs
const LVL_IGNORE: &str = "02🟠IGNOR";
/// tests that passes
const LVL_SUCCESS : &str = "03🟢SUCCS";

pub fn load_statetests_suite(
    path: &str,
    config: Config,
    mut compiler: Compiler,
) -> Result<Vec<StateTest>> {
    let skip_paths = config
        .skip_path
        .iter()
        .map(|t| &t.paths)
        .fold(Vec::new(), |mut acc, v| {
            acc.extend(v);
            acc
        });

    let files = glob::glob(path)
        .expect("Failed to read glob pattern")
        .map(|f| f.unwrap())
        .filter(|f| {
            !skip_paths
                .iter()
                .any(|e| f.as_path().to_string_lossy().contains(*e))
        });

    let mut tests = Vec::new();
    for file in files {
        if let Some(ext) = file.extension() {
            let ext = &*ext.to_string_lossy();
            if !["yml", "json"].contains(&ext) {
                continue;
            }
            let path = file.as_path().to_string_lossy();
            let src = std::fs::read_to_string(&file)?;
            log::debug!("Reading file {:?}", file);
            let mut tcs = match ext {
                "yml" => YamlStateTestBuilder::new(&mut compiler).load_yaml(&path, &src)?,
                "json" => JsonStateTestBuilder::new(&mut compiler).load_json(&path, &src)?,
                _ => unreachable!(),
            };

            tests.append(&mut tcs);
        }
    }
    Ok(tests)
}

pub fn run_statetests_suite(
    tcs: Vec<StateTest>,
    config: StateTestConfig,
    results: &mut ResultCache,
) -> Result<()> {
    let tcs: Vec<StateTest> = tcs
        .into_iter()
        .filter(|t| !results.contains(&t.id))
        .collect();

    let results = Arc::new(RwLock::from(results));

    let skip_tests =
        config
            .global
            .skip_test
            .iter()
            .chain(config.global.ignore_test.iter())
            .map(|t| &t.ids)
            .fold(Vec::new(), |mut acc, v| {
                acc.extend(v);
                acc
            });

    // for each test
    tcs.into_par_iter().for_each(|tc| {
        let id = format!("{}/{}", tc.path, tc.id);

        // Test result is cached? Ignore
        if results.read().unwrap().contains(id.as_str()) {
            return;
        }

        // Test must be ignored config?
        if skip_tests.contains(&&tc.id) {
            log::info!( "{} {}",LVL_IGNORE,id);
            results.write().unwrap().insert(&id, LVL_IGNORE).unwrap();
            return;
        }

        std::panic::set_hook(Box::new(|_info| {}));

        log::debug!("running test {}...",id);
        let result = std::panic::catch_unwind(|| tc.run(config.clone()));

        // handle panic
        let result = match result {
            Ok(res) => res,
            Err(_) => {
                log::error!(target: "vmvectests", "{} {}",LVL_PANIK, id);
                results.write().unwrap().insert(&id, LVL_PANIK).unwrap();
                return;
            }
        };

        // handle known error
        if let Err(err) = result {
            match err {
                StateTestError::SkipUnimplemented(_)
                | StateTestError::SkipTestMaxSteps(_)
                | StateTestError::SkipTestMaxGasLimit(_) => {
                    log::warn!(target: "vmvectests", "{} test {} : {:?}",LVL_IGNORE,id, err);
                    results
                        .write()
                        .unwrap()
                        .insert(&id, &format!("{} {}", LVL_IGNORE, err))
                        .unwrap();
                }
                _ => {
                    log::error!(target: "vmvectests", "{} {} : {:?}",LVL_FAIL, id, err);
                    results
                        .write()
                        .unwrap()
                        .insert(&id, &format!("{} {:?}", LVL_FAIL, err))
                        .unwrap();
                }
            }
            return;
        }

        let results = std::sync::Arc::clone(&results);
        results.write().unwrap().insert(&id, LVL_SUCCESS).unwrap();
        log::info!(target: "vmvectests", "{} {}",LVL_SUCCESS, id)
    });

    Ok(())
}
