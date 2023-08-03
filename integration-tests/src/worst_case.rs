use ethers::solc::{CompilerInput, CompilerOutput, Solc};
// use ethers_solc::error::{SolcError, SolcIoError};
use crate::wcerrors::SolcError;
/// this is a placeholder for this modules documentation
use semver::Version;
use serde::{de::DeserializeOwned, Deserialize, Serialize};
use std::{
    io::BufRead,
    path::PathBuf,
    process::{Command, Output, Stdio},
    str::FromStr,
};

/// Placeholder
pub type Result<T> = std::result::Result<T, SolcError>;
/// Solidity compilation warnings to ignore (by error code)
// 2018: Warning- "Function state mutability can be restricted to pure"
pub const WARN: &[u64] = &[2018];
/// The name of the `solc` binary on the system
pub const SOLC: &str = "solc";

/// this is a placeholder for this struct documentation
#[derive(Debug, Clone, Eq, PartialEq, PartialOrd, Ord, Serialize, Deserialize)]

/// Placeholder
pub struct Solcwc(Solc);

impl Solcwc {
    /// this is a placeholder
    // pub fn compile<T: Serialize>(&self, input: &T) -> Result<CompilerOutput> {
    //     self.compile_as(input)
    // }
    pub fn compile(&self, input: &CompilerInput) -> Result<CompilerOutput> {
        let output = self.compile_output(input)?;
        let mut deserializer = serde_json::Deserializer::from_slice(&output);
        deserializer.disable_recursion_limit();
        Ok(CompilerOutput::deserialize(&mut deserializer)?)
    }
    /// this is a placeholder
    pub fn compile_as<T: Serialize, D: DeserializeOwned>(&self, input: &T) -> Result<D> {
        let output = self.compile_output(input)?;
        Ok(serde_json::from_slice(&output)?)
    }

    /// this is a placeholder
    pub fn compile_output<T: Serialize>(&self, input: &T) -> Result<Vec<u8>> {
        let mut cmd = Command::new(&self.0.solc);
        if let Some(ref base_path) = self.0.base_path {
            cmd.current_dir(base_path);
            cmd.arg("--base-path").arg(base_path);
        }
        let mut child = cmd
            .args(&self.0.args)
            .arg("--standard-json")
            .stdin(Stdio::piped())
            .stderr(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .map_err(|err| SolcError::io(err, &self.0.solc))?;
        let stdin = child.stdin.take().expect("Stdin exists.");
        serde_json::to_writer(stdin, input)?;
        compile_output(
            child
                .wait_with_output()
                .map_err(|err| SolcError::io(err, &self.0.solc))?,
        )
    }

    /// this is a placeholder
    pub fn find_svm_installed_version(version: impl AsRef<str>) -> Result<Option<Self>> {
        let version = version.as_ref();
        let solc = Self::svm_home()
            // .unwrap()
            .ok_or_else(|| SolcError::solc("svm home dir not found"))?
            .join(version)
            .join(format!("solc-{version}"));

        if !solc.is_file() {
            return Ok(None);
        }
        Ok(Some(Solcwc::new(solc)))
    }

    /// this is a placeholder
    pub fn new(path: impl Into<PathBuf>) -> Self {
        Solcwc(Solc {
            solc: path.into(),
            base_path: None,
            args: Vec::new(),
        })
    }

    /// this is a placeholder
    pub fn svm_global_version() -> Option<Version> {
        let home = Self::svm_home()?;
        let version = std::fs::read_to_string(home.join(".global_version")).ok()?;
        Version::parse(&version).ok()
    }

    /// this is a placeholder
    pub fn svm_home() -> Option<PathBuf> {
        home::home_dir().map(|dir| dir.join(".svm"))
    }

    /// this is a placeholder
    pub fn version(&self) -> Result<Version> {
        version_from_output(
            Command::new(&self.0.solc)
                .arg("--version")
                .stdin(Stdio::piped())
                .stderr(Stdio::piped())
                .stdout(Stdio::piped())
                .output()
                .map_err(|err| SolcError::io(err, &self.0.solc))?,
        )
    }
}

fn compile_output(output: Output) -> Result<Vec<u8>> {
    if output.status.success() {
        Ok(output.stdout)
    } else {
        Err(SolcError::solc(
            String::from_utf8_lossy(&output.stderr).to_string(),
        ))
    }
}

fn version_from_output(output: Output) -> Result<Version> {
    if output.status.success() {
        let version = output
            .stdout
            .lines()
            .map_while(std::result::Result::ok)
            .filter(|l| !l.trim().is_empty())
            .last()
            .ok_or_else(|| SolcError::solc("version not found in solc output"))?;
        // NOTE: semver doesn't like `+` in g++ in build metadata which is invalid semver
        Ok(Version::from_str(
            &version
                .trim_start_matches("Version: ")
                .replace(".g++", ".gcc"),
        )?)
    } else {
        Err(SolcError::solc(
            String::from_utf8_lossy(&output.stderr).to_string(),
        ))
    }
}

impl Default for Solcwc {
    fn default() -> Self {
        if let Ok(solc) = std::env::var("SOLC_PATH") {
            return Solcwc::new(solc);
        }
        #[cfg(not(target_arch = "wasm32"))]
        {
            if let Some(solc) = Solcwc::svm_global_version()
                .and_then(|vers| Solcwc::find_svm_installed_version(vers.to_string()).ok())
                .flatten()
            {
                return solc;
            }
        }

        Solcwc::new(SOLC)
    }
}
