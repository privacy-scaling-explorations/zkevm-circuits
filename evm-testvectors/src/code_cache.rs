use anyhow::Result;
use eth_types::{Bytes, H256};
use keccak256::plain::Keccak;
use std::collections::HashMap;
use std::io::Read;
use std::io::Write;
use std::path::PathBuf;

pub struct CodeCache {
    entries: HashMap<H256, Bytes>,
    path: PathBuf,
}

impl CodeCache {
    pub fn new(path: PathBuf) -> Result<Self> {
        let entries = if let Ok(mut file) = std::fs::File::open(&path) {
            let h256 = |s| H256::from_slice(&hex::decode(s).expect("cache load h256"));
            let bytes = |s| Bytes::from(hex::decode(s).expect("cache load value"));

            let mut buf = String::new();
            file.read_to_string(&mut buf)?;
            buf.lines()
                .filter(|l| l.len() > 1)
                .map(|l| l.split_once("=").unwrap())
                .map(|(k, v)| (h256(k), bytes(v)))
                .collect()
        } else {
            HashMap::new()
        };
        Ok(Self { path, entries })
    }

    pub fn get(&self, src: &str) -> Option<&Bytes> {
        self.entries.get(&Self::hash(src))
    }

    pub fn insert(&mut self, src: &str, bytecode: Bytes) -> Result<()> {
        let code_hash = Self::hash(src);

        if !self.entries.contains_key(&code_hash) {
            let entry = format!("{}={}\n", hex::encode(code_hash), hex::encode(&bytecode));
            std::fs::OpenOptions::new()
                .read(true)
                .write(true)
                .create(true)
                .append(true)
                .open(&self.path)?
                .write_all(entry.as_bytes())?;

            self.entries.insert(code_hash, bytecode);
        }

        Ok(())
    }

    fn hash(src: &str) -> H256 {
        let mut hash = Keccak::default();
        hash.update(src.as_bytes());
        H256::from_slice(&hash.digest())
    }
}
