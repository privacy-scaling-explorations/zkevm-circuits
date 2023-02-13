use crate::table::LookupTable;
use crate::witness::MptUpdates;
use eth_types::Field;
use halo2_proofs::arithmetic::FieldExt;
use halo2_proofs::plonk::{Any, SecondPhase};
use halo2_proofs::{
    circuit::{Layouter, Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Error},
};
use itertools::Itertools;

/// The MptTable shared between MPT Circuit and State Circuit
#[derive(Clone, Copy, Debug)]
pub struct MptTable([Column<Advice>; 7]);

impl<F: Field> LookupTable<F> for MptTable {
    fn columns(&self) -> Vec<Column<Any>> {
        self.0.iter().map(|&col| col.into()).collect()
    }

    fn annotations(&self) -> Vec<String> {
        vec![
            String::from("Address"),
            String::from("Storage key"),
            String::from("Proof type"),
            String::from("New root"),
            String::from("Old root"),
            String::from("New value"),
            String::from("Old value"),
        ]
    }
}

type MptTableRow<F> = [Value<F>; 7];

impl MptTable {
    /// Construct a new MptTable
    pub(crate) fn construct<F: FieldExt>(meta: &mut ConstraintSystem<F>) -> Self {
        Self([
            meta.advice_column(),               // Address
            meta.advice_column_in(SecondPhase), // Storage key
            meta.advice_column(),               // Proof type
            meta.advice_column_in(SecondPhase), // New root
            meta.advice_column_in(SecondPhase), // Old root
            meta.advice_column_in(SecondPhase), // New value
            meta.advice_column_in(SecondPhase), // Old value
        ])
    }

    pub(crate) fn assign_row<F: Field>(
        &self,
        region: &mut Region<F>,
        offset: usize,
        row: MptTableRow<F>,
    ) -> Result<(), Error> {
        let table_column = <MptTable as LookupTable<F>>::advice_columns(self);

        for (column, value) in table_column.iter().zip_eq(row) {
            region.assign_advice(
                || format!("mpt table row {}", offset),
                *column,
                offset,
                || value,
            )?;
        }
        Ok(())
    }

    /// load for MptTable
    pub(crate) fn load<F: Field>(
        &self,
        layouter: &mut impl Layouter<F>,
        updates: &MptUpdates,
        randomness: Value<F>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "mpt table",
            |mut region| {
                let mut offset: usize = 0;
                self.assign_row(&mut region, offset, [Value::known(F::zero()); 7])?;

                offset += 1;
                for row in updates.table_assignments(randomness).iter() {
                    self.assign_row(&mut region, offset, row.0)?;

                    offset += 1;
                }
                Ok(())
            },
        )
    }
}
