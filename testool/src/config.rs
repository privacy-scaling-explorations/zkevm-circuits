use anyhow::{Context, Result};
use eth_types::evm_types::OpcodeId;
use serde::Deserialize;

#[derive(Debug, Clone, Deserialize)]
pub struct Config {
    pub max_gas: u64,
    pub max_steps: u64,

    /// see [Implemented opcodes status](https://github.com/appliedzkp/zkevm-circuits/issues/477)
    pub unimplemented_opcodes: Vec<OpcodeId>,
    pub ignore_test: Vec<SkipTest>,
    pub skip_path: Vec<SkipPath>,
    pub skip_test: Vec<SkipTest>,
}

impl Config {
    pub fn load() -> Result<Self> {
        let content = std::fs::read_to_string("./Config.toml")?;
        let toml: Result<Config, _> = toml::from_str(&content);
        toml.context("parsing toml")
    }
}

#[derive(Debug, Clone, Deserialize)]
pub struct SkipPath {
    pub desc: Option<String>,
    pub paths: Vec<String>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct SkipTest {
    pub desc: Option<String>,
    pub ids: Vec<String>,
}
