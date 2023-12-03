use super::*;

use crate::{
    exp_circuit::param::{OFFSET_INCREMENT, ROWS_PER_STEP},
    table::LookupTable,
    witness::{Block, Chunk},
};
use bus_mapping::circuit_input_builder::ExpEvent;

/// Lookup table within the Exponentiation circuit.
#[derive(Clone, Copy, Debug)]
pub struct ExpTable {
    /// Whether the row is the start of a step.
    pub is_step: Column<Fixed>,
    /// An identifier for every exponentiation trace, at the moment this is the
    /// read-write counter at the time of the lookups done to the
    /// exponentiation table.
    pub identifier: Column<Advice>,
    /// Whether this row is the last row in the exponentiation operation's
    /// trace.
    pub is_last: Column<Advice>,
    /// The integer base of the exponentiation.
    pub base_limb: Column<Advice>,
    /// The integer exponent of the exponentiation.
    pub exponent_lo_hi: Column<Advice>,
    /// The intermediate result of exponentiation by squaring.
    pub exponentiation_lo_hi: Column<Advice>,
}

impl ExpTable {
    /// Construct the Exponentiation table.
    pub fn construct<F: Field>(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            is_step: meta.fixed_column(),
            identifier: meta.advice_column(),
            is_last: meta.advice_column(),
            base_limb: meta.advice_column(),
            exponent_lo_hi: meta.advice_column(),
            exponentiation_lo_hi: meta.advice_column(),
        }
    }

    /// Given an exponentiation event and randomness, get assignments to the
    /// exponentiation table.
    pub fn assignments<F: Field>(exp_event: &ExpEvent) -> Vec<[F; 5]> {
        let mut assignments = Vec::new();
        let base_limbs = split_u256_limb64(&exp_event.base);
        let identifier = F::from(exp_event.identifier as u64);
        let mut exponent = exp_event.exponent;
        for (step_idx, exp_step) in exp_event.steps.iter().rev().enumerate() {
            let is_last = if step_idx == exp_event.steps.len() - 1 {
                F::ONE
            } else {
                F::ZERO
            };
            let (exp_lo, exp_hi) = split_u256(&exp_step.d);
            let (exponent_lo, exponent_hi) = split_u256(&exponent);

            // row 1
            assignments.push([
                identifier,
                is_last,
                base_limbs[0].as_u64().into(),
                exponent_lo
                    .to_scalar()
                    .expect("exponent should fit to scalar"),
                exp_lo
                    .to_scalar()
                    .expect("exponentiation lo should fit to scalar"),
            ]);
            // row 2
            assignments.push([
                identifier,
                F::ZERO,
                base_limbs[1].as_u64().into(),
                exponent_hi
                    .to_scalar()
                    .expect("exponent hi should fit to scalar"),
                exp_hi
                    .to_scalar()
                    .expect("exponentiation hi should fit to scalar"),
            ]);
            // row 3
            assignments.push([
                identifier,
                F::ZERO,
                base_limbs[2].as_u64().into(),
                F::ZERO,
                F::ZERO,
            ]);
            // row 4
            assignments.push([
                identifier,
                F::ZERO,
                base_limbs[3].as_u64().into(),
                F::ZERO,
                F::ZERO,
            ]);
            for _ in ROWS_PER_STEP..OFFSET_INCREMENT {
                assignments.push([F::ZERO, F::ZERO, F::ZERO, F::ZERO, F::ZERO]);
            }

            // update intermediate exponent.
            let (exponent_div2, remainder) = exponent.div_mod(U256::from(2));
            if remainder.is_zero() {
                // exponent is even
                exponent = exponent_div2;
            } else {
                // exponent is odd
                exponent = exponent - 1;
            }
        }
        assignments
    }

    /// Assign witness data from a block to the exponentiation table.
    pub fn load<F: Field>(
        &self,
        layouter: &mut impl Layouter<F>,
        block: &Block<F>,
        chunk: &Chunk<F>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "exponentiation table",
            |mut region| {
                let mut offset = 0;
                let exp_table_columns = <ExpTable as LookupTable<F>>::advice_columns(self);
                for exp_event in block.exp_events.iter() {
                    for row in Self::assignments::<F>(exp_event) {
                        for (&column, value) in exp_table_columns.iter().zip_eq(row) {
                            region.assign_advice(
                                || format!("exponentiation table row {}", offset),
                                column,
                                offset,
                                || Value::known(value),
                            )?;
                        }
                        offset += 1;
                    }
                }

                // pad an empty row
                let row = [F::from_u128(0); 5];
                for (column, value) in exp_table_columns.iter().zip_eq(row) {
                    region.assign_advice(
                        || format!("exponentiation table row {}", offset),
                        *column,
                        offset,
                        || Value::known(value),
                    )?;
                }

                // Enable selector at all rows
                let max_exp_steps = chunk.fixed_param.max_exp_steps;
                for offset in 0..max_exp_steps * OFFSET_INCREMENT {
                    let is_step = if offset % OFFSET_INCREMENT == 0 {
                        F::ONE
                    } else {
                        F::ZERO
                    };
                    region.assign_fixed(
                        || format!("exponentiation table row {}", offset),
                        self.is_step,
                        offset,
                        || Value::known(is_step),
                    )?;
                }

                Ok(())
            },
        )
    }
}

impl<F: Field> LookupTable<F> for ExpTable {
    fn columns(&self) -> Vec<Column<Any>> {
        vec![
            self.is_step.into(),
            self.identifier.into(),
            self.is_last.into(),
            self.base_limb.into(),
            self.exponent_lo_hi.into(),
            self.exponentiation_lo_hi.into(),
        ]
    }

    fn annotations(&self) -> Vec<String> {
        vec![
            String::from("is_step"),
            String::from("identifier"),
            String::from("is_last"),
            String::from("base_limb"),
            String::from("exponent_lo_hi"),
            String::from("exponentiation_lo_hi"),
        ]
    }

    fn table_exprs(&self, meta: &mut VirtualCells<F>) -> Vec<Expression<F>> {
        vec![
            meta.query_fixed(self.is_step, Rotation::cur()),
            meta.query_advice(self.identifier, Rotation::cur()),
            meta.query_advice(self.is_last, Rotation::cur()),
            meta.query_advice(self.base_limb, Rotation::cur()),
            meta.query_advice(self.base_limb, Rotation::next()),
            meta.query_advice(self.base_limb, Rotation(2)),
            meta.query_advice(self.base_limb, Rotation(3)),
            meta.query_advice(self.exponent_lo_hi, Rotation::cur()),
            meta.query_advice(self.exponent_lo_hi, Rotation::next()),
            meta.query_advice(self.exponentiation_lo_hi, Rotation::cur()),
            meta.query_advice(self.exponentiation_lo_hi, Rotation::next()),
        ]
    }
}
