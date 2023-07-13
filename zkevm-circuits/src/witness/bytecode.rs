use bus_mapping::state_db::CodeDB;
use eth_types::{Bytecode, Word};
use itertools::Itertools;
use std::collections::HashMap;

/// A collection of bytecode to prove
#[derive(Clone, Debug, Default)]
pub struct BytecodeCollection {
    codes: HashMap<Word, Bytecode>,
}

impl BytecodeCollection {
    /// Compute number of rows required for bytecode table.
    pub fn num_rows_required_for_bytecode_table(&self) -> usize {
        self.codes
            .values()
            .map(|bytecode| bytecode.codesize() + 1)
            .sum()
    }
    /// Query code by hash
    pub fn get(&self, codehash: &Word) -> Option<Bytecode> {
        self.codes.get(codehash).cloned()
    }

    /// Get raw bytes
    pub fn to_raw(&self) -> Vec<Vec<u8>> {
        self.codes.values().map(|code| code.code()).collect_vec()
    }
}

impl From<&CodeDB> for BytecodeCollection {
    fn from(_code_db: &CodeDB) -> Self {
        todo!()
    }
}

impl From<Vec<Vec<u8>>> for BytecodeCollection {
    fn from(bytecodes: Vec<Vec<u8>>) -> Self {
        Self {
            codes: HashMap::from_iter(bytecodes.iter().map(|bytecode| {
                let code = Bytecode::from(bytecode.clone());
                (code.hash(), code)
            })),
        }
    }
}

impl IntoIterator for BytecodeCollection {
    type Item = Bytecode;
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.codes.values().cloned().collect_vec().into_iter()
    }
}
