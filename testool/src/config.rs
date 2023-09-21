use anyhow::{anyhow, Context, Result};
use serde::Deserialize;

const CONFIG_FILE: &str = "Config.toml";

#[derive(Debug, Clone, Deserialize)]
pub struct Config {
    pub suite: Vec<TestSuite>,
    #[serde(default)]
    pub skip_paths: Vec<SkipPaths>,
    #[serde(default)]
    pub skip_tests: Vec<SkipTests>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct TestSuite {
    pub id: String,
    pub path: String,
    pub max_gas: u64,
    pub max_steps: u64,
}

impl Default for TestSuite {
    fn default() -> Self {
        Self {
            id: "default".to_string(),
            path: String::default(),
            max_gas: u64::MAX,
            max_steps: u64::MAX,
        }
    }
}

impl Config {
    pub fn load() -> Result<Self> {
        let content = std::fs::read_to_string(CONFIG_FILE)
            .context(format!("Unable to open {CONFIG_FILE}"))?;
        toml::from_str(&content).context("parsing toml")
    }
    pub fn suite(&self, name: &str) -> Result<&TestSuite> {
        self.suite
            .iter()
            .find(|s| s.id == name)
            .ok_or_else(|| anyhow!("Suite not found"))
    }
}

#[derive(Debug, Clone, Deserialize)]
pub struct TestsSet {
    pub id: String,
    pub desc: Option<String>,
    pub tests: Vec<String>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct SkipPaths {
    pub desc: Option<String>,
    pub paths: Vec<String>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct SkipTests {
    pub desc: Option<String>,
    pub tests: Vec<String>,
}
