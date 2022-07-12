//! Common utility traits and functions.
use eth_types::Field;

pub use gadgets::util::Expr;

pub(crate) fn random_linear_combine_word<F: Field>(bytes: [u8; 32], randomness: F) -> F {
    crate::evm_circuit::util::Word::random_linear_combine(bytes, randomness)
}

use itertools::Itertools;

/// TODO
pub struct TableShow<F: Field> {
    names: Vec<String>,
    columns: Vec<Vec<F>>,
}

impl<F: Field> TableShow<F> {
    /// TODO
    pub fn new(names: Vec<&str>) -> Self {
        let names_len = names.len();
        Self {
            names: names.iter().map(|s| s.to_string()).collect(),
            columns: vec![Vec::new(); names_len],
        }
    }

    /// TODO
    pub fn push(&mut self, column_index: usize, v: F) {
        self.columns[column_index].push(v);
    }

    /// TODO
    pub fn print(&self) {
        print!("|");
        for name in &self.names {
            print!(" {} |", name)
        }
        println!("\n---");
        let num_bytes: Vec<usize> = self
            .columns
            .iter()
            .map(|col| col.iter().max().unwrap())
            .map(|max| {
                let max_repr = max.to_repr();
                let bytes = max_repr.as_ref();
                let mut len = 1;
                for i in (0..32).rev() {
                    if bytes[i] != 0 {
                        len = i + 1;
                        break;
                    }
                }
                len
            })
            .collect();
        for row in 0..self.columns[0].len() {
            print!("|");
            for col in 0..self.columns.len() {
                print!(
                    " {:02x} |",
                    self.columns[col][row]
                        .to_repr()
                        .as_ref()
                        .iter()
                        .take(num_bytes[col])
                        .format("")
                );
            }
            println!("");
        }
    }
}
