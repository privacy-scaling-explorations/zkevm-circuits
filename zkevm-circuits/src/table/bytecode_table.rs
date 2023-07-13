use bus_mapping::state_db::CodeDB;

use crate::util;

use super::*;

/// Tag to identify the field in a Bytecode Table row
#[derive(Clone, Copy, Debug)]
pub enum BytecodeFieldTag {
    /// Header field
    Header,
    /// Byte field
    Byte,
}
impl_expr!(BytecodeFieldTag);

/// Table with Bytecode indexed by its Code Hash
#[derive(Clone, Debug)]
pub struct BytecodeTable {
    /// Code Hash
    pub code_hash: word::Word<Column<Advice>>,
    /// Tag
    pub tag: Column<Advice>,
    /// Index
    pub index: Column<Advice>,
    /// Is Code is true when the byte is not an argument to a PUSH* instruction.
    pub is_code: Column<Advice>,
    /// Value
    pub value: Column<Advice>,
}

impl BytecodeTable {
    /// Construct a new BytecodeTable
    pub fn construct<F: Field>(meta: &mut ConstraintSystem<F>) -> Self {
        let [tag, index, is_code, value] = array::from_fn(|_| meta.advice_column());
        let code_hash = word::Word::new([meta.advice_column(), meta.advice_column()]);
        Self {
            code_hash,
            tag,
            index,
            is_code,
            value,
        }
    }

    /// Assign the `BytecodeTable` from a list of bytecodes, followig the same
    /// table layout that the Bytecode Circuit uses.
    pub fn load<F: Field>(
        &self,
        layouter: &mut impl Layouter<F>,
        bytecodes: CodeDB,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "bytecode table",
            |mut region| {
                let mut offset = 0;
                for column in <BytecodeTable as LookupTable<F>>::advice_columns(self) {
                    region.assign_advice(
                        || "bytecode table all-zero row",
                        column,
                        offset,
                        || Value::known(F::ZERO),
                    )?;
                }
                offset += 1;

                let bytecode_table_columns =
                    <BytecodeTable as LookupTable<F>>::advice_columns(self);
                for bytecode in bytecodes.clone().into_iter() {
                    let rows = {
                        let code_hash = util::word::Word::from(bytecode.hash());
                        std::iter::once([
                            code_hash.lo(),
                            code_hash.hi(),
                            F::from(BytecodeFieldTag::Header as u64),
                            F::ZERO,
                            F::ZERO,
                            F::from(bytecode.codesize() as u64),
                        ])
                        .chain(bytecode.code_vec().iter().enumerate().map(
                            |(index, &(byte, is_code))| {
                                [
                                    code_hash.lo(),
                                    code_hash.hi(),
                                    F::from(BytecodeFieldTag::Byte as u64),
                                    F::from(index as u64),
                                    F::from(is_code.into()),
                                    F::from(byte.into()),
                                ]
                            },
                        ))
                        .collect_vec()
                    };
                    for row in rows.iter() {
                        for (&column, value) in bytecode_table_columns.iter().zip_eq(row.to_vec()) {
                            region.assign_advice(
                                || format!("bytecode table row {}", offset),
                                column,
                                offset,
                                || Value::known(value),
                            )?;
                        }
                        offset += 1;
                    }
                }
                Ok(())
            },
        )
    }
}

impl<F: Field> LookupTable<F> for BytecodeTable {
    fn columns(&self) -> Vec<Column<Any>> {
        vec![
            self.code_hash.lo().into(),
            self.code_hash.hi().into(),
            self.tag.into(),
            self.index.into(),
            self.is_code.into(),
            self.value.into(),
        ]
    }

    fn annotations(&self) -> Vec<String> {
        vec![
            String::from("code_hash_lo"),
            String::from("code_hash_hi"),
            String::from("tag"),
            String::from("index"),
            String::from("is_code"),
            String::from("value"),
        ]
    }
}
