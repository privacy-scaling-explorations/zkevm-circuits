use crate::{table::BytecodeFieldTag, util};
use bus_mapping::state_db::CodeDB;
use eth_types::{Bytecode, Field, Word};
use itertools::Itertools;
use std::collections::HashMap;

/// A collection of bytecode to prove
#[derive(Clone, Debug, Default)]
pub struct BytecodeCollection {
    codes: HashMap<Word, Bytecode>,
}

impl BytecodeCollection {
    /// Construct from raw bytes
    pub fn from_raw(bytecodes: Vec<Vec<u8>>) -> Self {
        Self {
            codes: HashMap::from_iter(bytecodes.iter().map(|bytecode| {
                let code = Bytecode::from(bytecode.clone());
                (code.hash(), code)
            })),
        }
    }

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
    #[deprecated()]
    pub fn to_raw(&self) -> Vec<Vec<u8>> {
        self.codes.values().map(|code| code.code()).collect_vec()
    }
}

impl From<&CodeDB> for BytecodeCollection {
    fn from(code_db: &CodeDB) -> Self {
        Self {
            codes: code_db
                .0
                .values()
                .map(|v| {
                    let bytecode = Bytecode::from(v.clone());
                    (bytecode.hash(), bytecode)
                })
                .collect(),
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
/// Bytecode
#[derive(Clone, Debug)]
pub struct BytecodeUnroller {
    /// We assume the is_code field is properly set.
    bytecode: Bytecode,
}

impl BytecodeUnroller {
    #[deprecated()]
    /// get byte value and is_code pair
    pub fn get(&self, dest: usize) -> Option<(u8, bool)> {
        self.bytecode.get(dest)
    }

    #[deprecated()]
    /// The length of the bytecode
    pub fn codesize(&self) -> usize {
        self.bytecode.codesize()
    }

    /// The length of the bytecode table
    pub fn table_len(&self) -> usize {
        self.bytecode.codesize() + 1
    }

    #[deprecated()]
    /// The code hash
    pub fn hash(&self) -> Word {
        self.bytecode.hash()
    }

    #[deprecated()]
    /// The code in bytes
    pub fn code(&self) -> Vec<u8> {
        self.bytecode.code()
    }
}

/// Public data for the bytecode
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct BytecodeRow<F: Field> {
    /// We don't assign it now
    code_hash: Word,
    pub(crate) tag: F,
    pub(crate) index: F,
    pub(crate) is_code: F,
    pub(crate) value: F,
}

impl<F: Field> BytecodeRow<F> {
    pub(crate) fn to_vec(&self) -> [F; 6] {
        let code_hash: util::word::Word<F> = util::word::Word::from(self.code_hash);
        [
            code_hash.lo(),
            code_hash.hi(),
            self.tag,
            self.index,
            self.is_code,
            self.value,
        ]
    }

    pub(crate) fn head(code_hash: Word, code_size: usize) -> Self {
        Self {
            code_hash,
            tag: F::from(BytecodeFieldTag::Header as u64),
            index: F::ZERO,
            is_code: F::ZERO,
            value: F::from(code_size as u64),
        }
    }
    pub(crate) fn body(code_hash: Word, index: usize, is_code: bool, value: u8) -> Self {
        Self {
            code_hash,
            tag: F::from(BytecodeFieldTag::Byte as u64),
            index: F::from(index as u64),
            is_code: F::from(is_code.into()),
            value: F::from(value.into()),
        }
    }
}
