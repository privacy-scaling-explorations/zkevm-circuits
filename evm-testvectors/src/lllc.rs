use anyhow::{bail, Context, Result};
use eth_types::Bytes;
use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Stdio};

use super::code_cache::CodeCache;

pub struct Lllc {
    cache: Option<CodeCache>,
    lllc_path: Option<PathBuf>,
    lllc_args: Vec<String>,
}

impl Default for Lllc {
    fn default() -> Self {
        Self {
            cache: None,
            lllc_path: None,
            lllc_args: Vec::new(),
        }
    }
}

impl Lllc {
    pub fn with_lllc(self, lllc_path: PathBuf, lllc_args: &[&str]) -> Self {
        Self {
            lllc_path: Some(lllc_path),
            lllc_args: lllc_args.iter().map(ToString::to_string).collect(),
            ..self
        }
    }
    pub fn with_cache(self, cache_path: PathBuf) -> Result<Self> {
        Ok(Self {
            cache: Some(CodeCache::new(cache_path)?),
            ..self
        })
    }
    pub fn with_docker_lllc(self) -> Self {
        Self::with_lllc(
            self,
            PathBuf::from("docker"),
            &["run", "-i", "--rm", "lllc"],
        )
    }
    pub fn with_default_cache(self) -> Result<Self> {
        Self::with_cache(self, PathBuf::from("lllc.cache"))
    }
    /// compiles LLL code
    pub fn compile(&mut self, src: &str) -> Result<Bytes> {
        if let Some(bytecode) = self.cache.as_mut().and_then(|c| c.get(src)) {
            return Ok(bytecode.clone());
        }
        if let Some(lllc_path) = &self.lllc_path {
            let mut child = Command::new(lllc_path.clone())
                .args(self.lllc_args.clone())
                .stdin(Stdio::piped())
                .stderr(Stdio::piped())
                .stdout(Stdio::piped())
                .spawn()?;

            child
                .stdin
                .as_mut()
                .context("failed to open stdin")?
                .write_all(src.as_bytes())?;

            let output = child.wait_with_output()?;

            let bytecode = if output.status.success() {
                let raw_output = String::from_utf8(output.stdout)?;
                Bytes::from(hex::decode(raw_output.trim())?)
            } else {
                let err = String::from_utf8(output.stderr)?;
                bail!("lllc command failed {:?} when compiling {:?}", err, src)
            };
            log::info!(target: "lllc","{}=> {}",src,hex::encode(&bytecode));

            if let Some(cache) = &mut self.cache {
                cache.insert(src, bytecode.clone())?;
            }

            return Ok(bytecode);
        }
        bail!("No way to compile LLLC for '{}'", src)
    }
}

#[cfg(test)]
mod test {
    #[test]
    #[cfg(feature = "docker-lllc")]
    fn test_docker_lllc() -> anyhow::Result<()> {
        let out = super::Lllc::default().with_docker_lllc().compile(
            "[[0]] (+ 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff 4)",
        )?;
        assert_eq!(
            hex::encode(out),
            "60047fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0160005500"
        );
        Ok(())
    }
}
