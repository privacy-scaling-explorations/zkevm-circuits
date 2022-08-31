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
            .config
            .skip_test
            .iter()
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
            log::info!(target: "vmvectests", "01🟡IGNOR {}",id);
            results.write().unwrap().insert(&id, "01🟡IGNOR").unwrap();
            return;
        }

        std::panic::set_hook(Box::new(|_info| {}));

        log::debug!(target: "vmvectests", "running test {}...",id);
        let result = std::panic::catch_unwind(|| tc.run(config.clone()));

        // handle panic
        let result = match result {
            Ok(res) => res,
            Err(_) => {
                log::error!(target: "vmvectests", "00💀PANIK {}",id);
                results.write().unwrap().insert(&id, "00💀PANIK").unwrap();
                return;
            }
        };

        // handle known error
        if let Err(err) = result {
            match err {
                StateTestError::SkipUnimplemented(_)
                | StateTestError::SkipTestMaxSteps(_)
                | StateTestError::SkipTestMaxGasLimit(_) => {
                    log::warn!(target: "vmvectests", "02🟠SKIPP test {} : {:?}",id, err);
                    results
                        .write()
                        .unwrap()
                        .insert(&id, &format!("02🟠SKIPP {}", err))
                        .unwrap();
                }
                _ => {
                    log::error!(target: "vmvectests", "01🔴FAILD {} : {:?}",id, err);
                    results
                        .write()
                        .unwrap()
                        .insert(&id, &format!("01🔴FAILD {:?}", err))
                        .unwrap();
                }
            }
            return;
        }

        let results = std::sync::Arc::clone(&results);
        results.write().unwrap().insert(&id, "04🟢SUCCS").unwrap();
        log::info!(target: "vmvectests", "04🟢SUCCS {}",id)
    });

    Ok(())
}
