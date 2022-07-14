use anyhow::Result;
use std::collections::HashMap;
use std::io::Read;
use std::io::Write;
use std::path::PathBuf;

pub struct ResultCache {
    entries: HashMap<String, String>,
    path: PathBuf,
}

impl ResultCache {
    pub fn new(path: PathBuf) -> Result<Self> {
        let entries = if let Ok(mut file) = std::fs::File::open(&path) {
            let mut buf = String::new();
            file.read_to_string(&mut buf)?;
            buf.lines()
                .filter(|l| l.len() > 1)
                .map(|l| l.split_once("=").unwrap())
                .map(|(k, v)| (k.to_string(), v.to_string()))
                .collect()
        } else {
            HashMap::new()
        };
        Ok(Self { path, entries })
    }

    pub fn sort(&self) -> Result<()> {
        let mut lines: Vec<_> = self.entries.iter().collect();
        lines.sort_by(|(k1, v1), (k2, v2)| (v1, k1).cmp(&(v2, k2)));
        let buf = lines
            .iter()
            .map(|(k, v)| format!("{}={}", k, v))
            .collect::<Vec<_>>()
            .join("\n");
        std::fs::OpenOptions::new()
            .write(true)
            .create(true)
            .open(&self.path)?
            .write_all(buf.as_bytes())?;
        Ok(())
    }

    pub fn contains(&self, test: &str) -> bool {
        self.entries.contains_key(test)
    }

    pub fn insert(&mut self, test: &str, result: &str) -> Result<()> {
        if !self.entries.contains_key(test) {
            let entry = format!("{}={}\n", test, result);
            std::fs::OpenOptions::new()
                .read(true)
                .write(true)
                .create(true)
                .append(true)
                .open(&self.path)?
                .write_all(entry.as_bytes())?;

            self.entries.insert(test.to_string(), result.to_string());
        }

        Ok(())
    }
}
