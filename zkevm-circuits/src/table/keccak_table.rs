use super::*;

/// Keccak Table, used to verify keccak hashing from RLC'ed input.
#[derive(Clone, Debug)]
pub struct KeccakTable {
    /// True when the row is enabled
    pub is_enabled: Column<Advice>,
    /// Byte array input as `RLC(reversed(input))`
    pub input_rlc: Column<Advice>, // RLC of input bytes
    /// Byte array input length
    pub input_len: Column<Advice>,
    /// RLC of the hash result
    pub output_rlc: Column<Advice>, // RLC of hash of input bytes
}

impl<F: Field> LookupTable<F> for KeccakTable {
    fn columns(&self) -> Vec<Column<Any>> {
        vec![
            self.is_enabled.into(),
            self.input_rlc.into(),
            self.input_len.into(),
            self.output_rlc.into(),
        ]
    }

    fn annotations(&self) -> Vec<String> {
        vec![
            String::from("is_enabled"),
            String::from("input_rlc"),
            String::from("input_len"),
            String::from("output_rlc"),
        ]
    }
}

impl KeccakTable {
    /// Construct a new KeccakTable
    pub fn construct<F: Field>(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            is_enabled: meta.advice_column(),
            input_rlc: meta.advice_column_in(SecondPhase),
            input_len: meta.advice_column(),
            output_rlc: meta.advice_column_in(SecondPhase),
        }
    }

    /// Generate the keccak table assignments from a byte array input.
    pub fn assignments<F: Field>(
        input: &[u8],
        challenges: &Challenges<Value<F>>,
        is_big_endian: bool,
    ) -> Vec<[Value<F>; 4]> {
        // let bytes = if is_big_endian {
        // input.iter().cloned().rev().collect::<Vec<u8>>()
        // } else {
        // input.to_owned()
        // };
        let r = F::from(123456u64);
        let input_rlc = challenges
            .keccak_input()
            .map(|_challenge| rlc::value(input.iter().rev(), /* challenge */ r + F::ONE));
        // let input_rlc = challenges
        // .keccak_input()
        // .map(|challenge| rlc::value(&bytes, /*challenge*/r + F::ONE));
        let input_len = F::from(input.len() as u64);
        let mut keccak = Keccak::default();
        keccak.update(input);
        let output = keccak.digest();
        let output_rlc = challenges.evm_word().map(|_challenge| {
            rlc::value(
                &if is_big_endian {
                    Word::from_big_endian(output.as_slice())
                } else {
                    Word::from_little_endian(output.as_slice())
                }
                .to_le_bytes(),
                // challenge
                r,
            )
        });

        vec![[
            Value::known(F::ONE),
            input_rlc,
            Value::known(input_len),
            output_rlc,
        ]]
    }

    /// Assign a table row for keccak table
    pub fn assign_row<F: Field>(
        &self,
        region: &mut Region<F>,
        offset: usize,
        values: [Value<F>; 4],
    ) -> Result<(), Error> {
        for (&column, value) in <KeccakTable as LookupTable<F>>::advice_columns(self)
            .iter()
            .zip(values.iter())
        {
            region.assign_advice(|| format!("assign {}", offset), column, offset, || *value)?;
        }
        Ok(())
    }

    /// Provide this function for the case that we want to consume a keccak
    /// table but without running the full keccak circuit
    pub fn dev_load<'a, F: Field>(
        &self,
        layouter: &mut impl Layouter<F>,
        inputs: impl IntoIterator<Item = &'a Vec<u8>> + Clone,
        challenges: &Challenges<Value<F>>,
        is_big_endian: bool,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "keccak table",
            |mut region| {
                let mut offset = 0;
                for column in <KeccakTable as LookupTable<F>>::advice_columns(self) {
                    region.assign_advice(
                        || "keccak table all-zero row",
                        column,
                        offset,
                        || Value::known(F::ZERO),
                    )?;
                }
                offset += 1;

                let keccak_table_columns = <KeccakTable as LookupTable<F>>::advice_columns(self);
                for input in inputs.clone() {
                    for row in Self::assignments(input, challenges, is_big_endian) {
                        // let mut column_index = 0;
                        for (&column, value) in keccak_table_columns.iter().zip_eq(row) {
                            region.assign_advice(
                                || format!("keccak table row {}", offset),
                                column,
                                offset,
                                || value,
                            )?;
                        }
                        offset += 1;
                    }
                }
                Ok(())
            },
        )
    }

    /// returns matchings between the circuit columns passed as parameters and
    /// the table collumns
    pub fn match_columns(
        &self,
        value_rlc: Column<Advice>,
        length: Column<Advice>,
        code_hash: Column<Advice>,
    ) -> Vec<(Column<Advice>, Column<Advice>)> {
        vec![
            (value_rlc, self.input_rlc),
            (length, self.input_len),
            (code_hash, self.output_rlc),
        ]
    }
}
