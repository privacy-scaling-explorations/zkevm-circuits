use super::executor::run_test;
use super::JsonStateTestBuilder;
use super::Results;
use super::{CircuitsConfig, StateTest};
use crate::compiler::Compiler;
use crate::config::{Config, TestSuite};
use crate::statetest::results::{ResultInfo, ResultLevel};
use crate::statetest::YamlStateTestBuilder;
use anyhow::{Context, Result};
use rayon::prelude::*;
use std::sync::Arc;
use std::sync::RwLock;

pub fn load_statetests_suite(
    path: &str,
    config: Config,
    mut compiler: Compiler,
) -> Result<Vec<StateTest>> {
    let skip_paths: Vec<&String> = config.skip_paths.iter().flat_map(|t| &t.paths).collect();
    let skip_tests: Vec<&String> = config.skip_tests.iter().flat_map(|t| &t.tests).collect();

    let files = glob::glob(path)
        .context("failted to read glob")?
        .filter_map(|v| v.ok())
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

            tcs.retain(|v| !skip_tests.contains(&&v.id));
            tests.append(&mut tcs);
        }
    }
    Ok(tests)
}

pub fn run_statetests_suite(
    tcs: Vec<StateTest>,
    circuits_config: &CircuitsConfig,
    suite: &TestSuite,
    results: &mut Results,
) -> Result<()> {
    // Filter already cached entries
    let tcs: Vec<StateTest> = tcs
        .into_iter()
        .filter(|t| !results.contains(&t.id))
        .collect();

    let results = Arc::new(RwLock::from(results));

    // for each test
    tcs.into_par_iter().for_each(|ref tc| {
        let full_id = format!("{}#{}", tc.id, tc.path);

        if !suite.allowed(&tc.id) {
            results
                .write()
                .unwrap()
                .insert(
                    full_id,
                    ResultInfo {
                        level: ResultLevel::Ignored,
                        details: "Ignored in config file".to_string(),
                    },
                )
                .unwrap();
            return;
        }

        std::panic::set_hook(Box::new(|_info| {}));

        log::debug!("running test {}...", full_id);
        let result = std::panic::catch_unwind(|| {
            run_test(tc.clone(), suite.clone(), circuits_config.clone())
        });

        // handle panic
        let result = match result {
            Ok(res) => res,
            Err(_) => {
                results
                    .write()
                    .unwrap()
                    .insert(
                        full_id,
                        ResultInfo {
                            level: ResultLevel::Panic,
                            details: String::default(),
                        },
                    )
                    .unwrap();
                return;
            }
        };

        // handle known error
        if let Err(err) = result {
            results
                .write()
                .unwrap()
                .insert(
                    full_id,
                    ResultInfo {
                        level: if err.is_skip() {
                            ResultLevel::Ignored
                        } else {
                            ResultLevel::Fail
                        },
                        details: err.to_string(),
                    },
                )
                .unwrap();
            return;
        }

        results
            .write()
            .unwrap()
            .insert(
                full_id,
                ResultInfo {
                    level: ResultLevel::Success,
                    details: String::default(),
                },
            )
            .unwrap();
    });

    Ok(())
}
