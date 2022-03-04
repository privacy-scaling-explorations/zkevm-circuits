use anyhow::{bail, Context, Result};
use eth_types::Bytes;
use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Stdio};
pub struct Lllc {
    path: PathBuf,
    args: Vec<String>,
}

/// Create a new builder from the lllc path
///   there is some problems compiling old solidity version in M1
///   use patched github.com/adria0/solidity commit
/// 931b8a66cb985476b5c61e23d41e030c0cff009a
impl Lllc {
    pub fn new(path: PathBuf, args: &[&str]) -> Self {
        Self {
            path,
            args: args.iter().map(ToString::to_string).collect(),
        }
    }
    pub fn with_docker() -> Self {
        Lllc::new(PathBuf::from("docker"), &["run", "-i", "--rm", "lllc"])
    }

    /// compiles LLL code
    pub fn compile(&self, src: &str) -> Result<Bytes> {
        let mut child = Command::new(self.path.clone())
            .args(self.args.clone())
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

        if output.status.success() {
            let raw_output = String::from_utf8(output.stdout)?;
            log::trace!(target:"evmvectests", "lllc out={}",raw_output);
            Ok(Bytes::from(hex::decode(raw_output.trim())?))
        } else {
            let err = String::from_utf8(output.stderr)?;
            bail!("lllc command failed {:?}", err)
        }
    }
}

#[cfg(test)]
mod test {
    #[test]
    #[cfg(feature = "docker-lllc")]
    fn test_docker_lllc() -> anyhow::Result<()> {
        let out = super::Lllc::with_docker().compile(
            "[[0]] (+ 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff 4)",
        )?;
        assert_eq!(
            hex::encode(out),
            "60047fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0160005500"
        );
        Ok(())
    }
}
