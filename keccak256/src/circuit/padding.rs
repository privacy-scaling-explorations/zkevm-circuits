use super::{BYTES_PER_WORD, MAX_INPUT_BYTES, MAX_INPUT_WORDS};
use crate::permutation::tables::RangeCheckConfig;
use eth_types::Field;
use halo2_proofs::{
    circuit::{layouter::RegionLayouter, AssignedCell, Layouter},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Selector},
    poly::Rotation,
};
use itertools::Itertools;
use std::{convert::TryInto, marker::PhantomData};

pub type Byte = u8;
pub type AssignedByte<F> = AssignedCell<F, F>;
pub type AssignedWord<F> = AssignedCell<F, F>;

/// Gets 8 Advice columns with the 8bytes to form the word + the final word
/// value of the composed bytes at the end.
pub(crate) struct WordBuilderConfig<F> {
    q_enable: Selector,
    bytes_and_word: [Column<Advice>; BYTES_PER_WORD + 1],
    byte_table: RangeCheckConfig<F, 255>,
    _marker: PhantomData<F>,
}

impl<F: Field> WordBuilderConfig<F> {
    pub(crate) fn configure(
        meta: &mut ConstraintSystem<F>,
        bytes: [Column<Advice>; BYTES_PER_WORD + 1],
    ) -> WordBuilderConfig<F> {
        let q_enable = meta.complex_selector();
        let byte_table = RangeCheckConfig::<F, 255>::configure(meta);

        // Enable equality for all byte cells.
        bytes.iter().for_each(|&byte| meta.enable_equality(byte));

        meta.lookup("Range check for word bytes", |meta| {
            let q_enable = meta.query_selector(q_enable);
            bytes
                .iter()
                .map(|&byte| {
                    (
                        q_enable.clone() * meta.query_advice(byte, Rotation::cur()),
                        byte_table.range,
                    )
                })
                .collect_vec()
        });

        meta.create_gate("Build Word", |meta| {
            let q_enable = meta.query_selector(q_enable);

            // Running sum to construct a u64 word with 8 u8 bytes shifted by it's position.
            let bytes_sum: Expression<F> = bytes[0..BYTES_PER_WORD]
                .iter()
                .map(|&column| meta.query_advice(column, Rotation::cur()))
                .enumerate()
                .map(|(idx, byte_expr)| Expression::Constant(F::from(1u64 << idx)) * byte_expr)
                .reduce(|acc, byte_shifted| acc + byte_shifted)
                // Unwrapping is safe here as we recieve an array that contails all elements.
                .unwrap();

            let word = meta.query_advice(*bytes.last().unwrap(), Rotation::cur());

            vec![q_enable * (bytes_sum - word)]
        });
        Self {
            q_enable,
            bytes_and_word: bytes,
            byte_table,
            _marker: PhantomData,
        }
    }

    pub fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        self.byte_table.load(layouter)
    }

    pub fn assign_state(
        &self,
        layouter: &mut impl Layouter<F>,
        bytes: [AssignedByte<F>; BYTES_PER_WORD],
    ) -> Result<AssignedWord<F>, Error> {
        layouter.assign_region(
            || "Word construction",
            |mut region| {
                let offset = 0;
                self.q_enable.enable(&mut region, offset)?;
                // Copy bytes to byte columns
                let byte_cells: [AssignedByte<F>; BYTES_PER_WORD] = bytes
                    .iter()
                    .zip(self.bytes_and_word[0..BYTES_PER_WORD].iter())
                    .map(|(byte, &byte_col)| {
                        byte.copy_advice(|| "Copy byte", &mut region, byte_col, offset)
                    })
                    .collect::<Result<Vec<AssignedByte<F>>, Error>>()?
                    .try_into()
                    .unwrap();

                // Compute the word formed by the bytes and assign it into the last column of
                // the bytes
                let word_scalar = byte_cells
                    .iter()
                    .enumerate()
                    .map(|(idx, byte_cell)| F::from(1u64 << idx) * byte_cell.value().unwrap())
                    .reduce(|acc, byte_shifted| acc + byte_shifted)
                    // Unwrapping is safe here as we recieve an array that contails all elements.
                    .unwrap();

                region.assign_advice(
                    || "Assign byte-constructed Word",
                    *self.bytes_and_word.last().unwrap(),
                    offset,
                    || Ok(word_scalar),
                )
            },
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
}
