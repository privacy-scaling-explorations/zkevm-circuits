use anyhow::{bail, Context, Result};
use eth_types::{H256, Bytes};
use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::collections::HashMap;
use keccak256::plain::Keccak;
use std::io::Read;

pub struct Lllc {
    cache: HashMap<H256, Bytes>,
    cache_path : Option<PathBuf>,
    lllc_path: Option<PathBuf>,
    lllc_args: Vec<String>,
}

impl Default for Lllc {
    fn default() -> Self {
        Self {
            cache: HashMap::new(),
            cache_path: None,
            lllc_path: None,
            lllc_args: Vec::new()
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
        let cache = if let Ok(mut file) = std::fs::File::open(&cache_path) {
            let h256 = |s| H256::from_slice(&hex::decode(s).unwrap()); 
            let bytes = |s| Bytes::from(hex::decode(s).unwrap());
            
            let mut buf = String::new();
            file.read_to_string(&mut buf)?;
            buf.lines()
                .filter(|l| l.len() > 1)
                .map(|l| l.split_once("=").unwrap())
                .map(|(k,v)| (h256(k),bytes(v))).collect()
        } else {
            HashMap::new()
        };
        Ok(Self {
            cache_path: Some(cache_path),
            cache,
            ..self
        })
    }
    pub fn with_docker_lllc(self) -> Self {
        Self::with_lllc(self, PathBuf::from("docker"), &["run", "-i", "--rm", "lllc"])
    }
    pub fn with_default_cache(self) -> Result<Self> {
        Self::with_cache(self, PathBuf::from("lllc.cache"))
    }
    pub fn hash(src: &str) -> H256 {
        let mut hash = Keccak::default();
        hash.update(src.as_bytes());
        H256::from_slice(&hash.digest())
    }
    /// compiles LLL code
    pub fn compile(&mut self, src: &str) -> Result<Bytes> {
        if let Some(bytecode) = self.cache.get(&Self::hash(src)) {
            println!("Using cache for {}",src);
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

            let code = if output.status.success() {
                let raw_output = String::from_utf8(output.stdout)?;
                log::trace!(target:"evmvectests", "lllc out={}",raw_output);
                Bytes::from(hex::decode(raw_output.trim())?)
            } else {
                let err = String::from_utf8(output.stderr)?;
                bail!("lllc command failed {:?}", err)
            };

            // update cache
            if let Some(cache_path) = self.cache_path.as_ref() {
                println!("*** compiling");
                let entry = format!("{}={}\n", hex::encode(Self::hash(src)), hex::encode(&code));
                std::fs::OpenOptions::new()
                    .read(true)
                    .write(true)
                    .create(true)
                    .append(true)
                    .open(cache_path)?
                    .write_all(entry.as_bytes())?;
                panic!("written!");
            }

            return Ok(code);
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
