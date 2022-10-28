use super::JsonStateTestBuilder;
use super::Results;
use super::{StateTest, StateTestConfig};
use crate::compiler::Compiler;
use crate::config::Config;
use crate::statetest::results::{ResultInfo, ResultLevel};
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
    let skip_paths: Vec<&String> = config.skip_path.iter().flat_map(|t| &t.paths).collect();

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
    results: &mut Results,
) -> Result<()> {
    let tcs: Vec<StateTest> = tcs
        .into_iter()
        .filter(|t| !results.contains(&t.id))
        .collect();

    let results = Arc::new(RwLock::from(results));

    let skip_tests: Vec<&String> = config
        .global
        .skip_test
        .iter()
        .chain(config.global.ignore_test.iter())
        .flat_map(|t| &t.ids)
        .collect();

    // for each test
    tcs.into_par_iter().for_each(|ref tc| {
        // Test result is cached? Ignore
        if results.read().unwrap().contains(tc.id.as_str()) {
            return;
        }

        // Test must be ignored config?
        if skip_tests.contains(&&tc.id) {
            results
                .write()
                .unwrap()
                .insert(
                    tc.id.clone(),
                    ResultInfo {
                        level: ResultLevel::Ignored,
                        details: "Ignored in config file".to_string(),
                        path: tc.path.to_string(),
                    },
                )
                .unwrap();
            return;
        }

        std::panic::set_hook(Box::new(|_info| {}));

        log::debug!("running test {}/{}...", tc.path, tc.id);
        let result = std::panic::catch_unwind(|| tc.clone().run(config.clone()));

        // handle panic
        let result = match result {
            Ok(res) => res,
            Err(_) => {
                results
                    .write()
                    .unwrap()
                    .insert(
                        tc.id.clone(),
                        ResultInfo {
                            level: ResultLevel::Panic,
                            details: String::default(),
                            path: tc.path.to_string(),
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
                    tc.id.clone(),
                    ResultInfo {
                        level: if err.is_skip() {
                            ResultLevel::Ignored
                        } else {
                            ResultLevel::Fail
                        },
                        details: err.to_string(),
                        path: tc.path.to_string(),
                    },
                )
                .unwrap();
            return;
        }

        results
            .write()
            .unwrap()
            .insert(
                tc.id.clone(),
                ResultInfo {
                    level: ResultLevel::Success,
                    details: String::default(),
                    path: tc.path.to_string(),
                },
            )
            .unwrap();
    });

    Ok(())
}
