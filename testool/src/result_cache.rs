use anyhow::Result;
use prettytable::Row;
use prettytable::Table;
use std::collections::HashMap;
use std::collections::HashSet;
use std::io::Read;
use std::io::Write;
use std::path::PathBuf;

pub struct ResultCache {
    entries: HashMap<String, String>,
    path: Option<PathBuf>,
}

impl ResultCache {
    pub fn with_memory() -> Self {
        Self {
            entries: HashMap::new(),
            path: None,
        }
    }
    pub fn with_file(path: PathBuf) -> Result<Self> {
        let entries = if let Ok(mut file) = std::fs::File::open(&path) {
            let mut buf = String::new();
            file.read_to_string(&mut buf)?;
            buf.lines()
                .filter(|l| l.len() > 1)
                .map(|l| l.split_once('=').unwrap())
                .map(|(k, v)| (k.to_string(), v.to_string()))
                .collect()
        } else {
            HashMap::new()
        };
        Ok(Self {
            path: Some(path),
            entries,
        })
    }

    pub fn report(&self) -> String {
        let mut folders = HashSet::new();
        let mut results = HashSet::new();
        let mut count_by_folder_status: HashMap<String, usize> = HashMap::new();
        let mut count_by_result: HashMap<String, usize> = HashMap::new();
        for (path_id, status) in &self.entries {
            let id = path_id.rsplit_terminator('/').next().unwrap();
            let full_path = &path_id[..path_id.len() - id.len() - 1];
            let name = full_path.rsplit_terminator('/').next().unwrap();
            let folder = &full_path[..full_path.len() - name.len() - 1];

            let result = &status[..6];

            folders.insert(folder);
            results.insert(result.to_string());

            let key = format!("{}_{}", folder, result);
            *count_by_folder_status.entry(key).or_default() += 1;
            *count_by_result.entry(status.to_string()).or_default() += 1;
        }

        let mut folders: Vec<_> = folders.iter().collect();
        folders.sort();
        let mut results: Vec<_> = results.iter().collect();
        results.sort();

        let mut table = Table::new();
        let mut header = vec![String::from("path")];
        header.append(&mut results.iter().map(|v| v.to_string()).collect());
        table.add_row(Row::from_iter(header));

        let mut totals = vec![0usize; results.len()];

        for folder in folders {
            let mut row = Vec::new();
            for i in 0..results.len() {
                let key = format!("{}_{}", folder, results[i]);
                let value = *count_by_folder_status.get(&key).unwrap_or(&0usize);
                row.push(value);
                totals[i] += value;
            }
            let sum: usize = row.iter().sum();
            let mut cells = vec![folder.to_string()];
            cells.append(
                &mut row
                    .iter()
                    .map(|n| format!("{} ({}%)", n, (100 * n) / sum))
                    .collect(),
            );
            table.add_row(Row::from_iter(cells));
        }

        let sum: usize = totals.iter().sum();
        let mut cells = vec!["TOTAL".to_string()];
        cells.append(
            &mut totals
                .iter()
                .map(|n| format!("{} ({}%)", n, (100 * n) / sum))
                .collect(),
        );
        table.add_row(Row::from_iter(cells));

        let mut output = String::from("");
        output.push_str(&format!("{}", table));
        output.push('\n');

        let mut info: Vec<String> = Vec::new();
        for (result, count) in count_by_result {
            info.push(format!("{:04} => {}", count, result));
        }
        info.sort_by(|a, b| b.cmp(a));
        output.push_str("Top 25 results\n");
        info.iter()
            .take(25)
            .for_each(|s| output.push_str(&format!("{}\n", s)));

        output
    }

    pub fn write_sorted(&self) -> Result<()> {
        if let Some(path) = &self.path {
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
                .open(path)?
                .write_all(buf.as_bytes())?;
        }
        Ok(())
    }

    pub fn contains(&self, test: &str) -> bool {
        self.entries.contains_key(test)
    }

    pub fn insert(&mut self, test: &str, result: &str) -> Result<()> {
        if !self.entries.contains_key(test) {
            let entry = format!("{}={}\n", test, result);
            if let Some(path) = &self.path {
                std::fs::OpenOptions::new()
                    .read(true)
                    .write(true)
                    .create(true)
                    .append(true)
                    .open(path)?
                    .write_all(entry.as_bytes())?;
            }
            self.entries.insert(test.to_string(), result.to_string());
        }

        Ok(())
    }
}
