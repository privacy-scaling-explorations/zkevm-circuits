use super::BYTES_PER_WORD;
use crate::permutation::tables::RangeCheckConfig;
use eth_types::Field;
use halo2_proofs::{
    circuit::{AssignedCell, Layouter},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Selector},
    poly::Rotation,
};
use itertools::Itertools;
use std::{convert::TryInto, marker::PhantomData};

pub type Byte = u8;
pub type AssignedByte<F> = AssignedCell<F, F>;
pub type AssignedWord<F> = AssignedCell<F, F>;

#[derive(Debug, Clone)]
/// Gets 8 Advice columns with the 8bytes to form the word + the final word
/// value of the composed bytes at the end.
pub(crate) struct WordBuilderConfig<F> {
    q_enable: Selector,
    bytes: [Column<Advice>; BYTES_PER_WORD],
    word: Column<Advice>,
    byte_table: RangeCheckConfig<F, 255>,
}

impl<F: Field> WordBuilderConfig<F> {
    pub(crate) fn configure(
        meta: &mut ConstraintSystem<F>,
        bytes: [Column<Advice>; BYTES_PER_WORD],
        word: Column<Advice>,
        byte_table: RangeCheckConfig<F, 255>,
    ) -> WordBuilderConfig<F> {
        let q_enable = meta.complex_selector();

        // Enable equality for all byte cells.
        bytes.iter().for_each(|&byte| meta.enable_equality(byte));
        meta.enable_equality(word);

        bytes.iter().for_each(|&byte| {
            meta.lookup("Range check for word byte", |meta| {
                let q_enable = meta.query_selector(q_enable);

                vec![(
                    q_enable.clone() * meta.query_advice(byte, Rotation::cur()),
                    byte_table.range,
                )]
            });
        });

        meta.create_gate("Build Word", |meta| {
            let q_enable = meta.query_selector(q_enable);

            // Running sum to construct a u64 word with 8 u8 bytes shifted by it's position.
            let bytes_sum: Expression<F> = bytes
                .iter()
                .map(|&column| meta.query_advice(column, Rotation::cur()))
                .enumerate()
                .map(|(idx, byte_expr)| {
                    Expression::Constant(F::from(1u64 << (idx * 8))) * byte_expr
                })
                .reduce(|acc, byte_shifted| acc + byte_shifted)
                // Unwrapping is safe here as we recieve an array that contails all elements.
                .unwrap();

            let word = meta.query_advice(word, Rotation::cur());

            vec![q_enable * (bytes_sum - word)]
        });
        Self {
            q_enable,
            bytes,
            word,
            byte_table,
        }
    }

    pub(crate) fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        self.byte_table.load(layouter)
    }

    pub(crate) fn assign_bytes(
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
                    .zip(self.bytes.iter())
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
                    .map(|(idx, byte_cell)| {
                        F::from(1u64 << (idx * 8)) * byte_cell.value().unwrap_or(&F::zero())
                    })
                    .reduce(|acc, byte_shifted| acc + byte_shifted)
                    // Unwrapping is safe here as we recieve an array that contails all elements.
                    .unwrap();

                region.assign_advice(
                    || "Assign byte-constructed Word",
                    self.word,
                    offset,
                    || Ok(word_scalar),
                )
            },
        )
    }
}
