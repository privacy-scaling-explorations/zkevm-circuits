use eth_types::Field;
use halo2_proofs::{
    circuit::Region,
    plonk::{Advice, Column, ConstraintSystem, *},
    poly::Rotation,
};

use crate::evm_circuit::table::Table;

use super::cell_manager::EvmCellType;

/// LookupTable impl for raw columns.
/// Must define a existing CellType to instantiate this impelmentation
impl<F: Field, CA: Into<Column<Any>> + Copy, const W: usize> LookupTable<F> for [CA; W] {
    type TableCellType = EvmCellType;

    fn get_type(&self) -> EvmCellType {
        EvmCellType::Lookup(Table::Fixed)
    }

    fn phase(&self) -> u8 {
        // default phase is 0
        0
    }

    fn table_exprs(&self, meta: &mut VirtualCells<F>) -> Vec<Expression<F>> {
        self.iter()
            .map(|column| meta.query_any(*column, Rotation::cur()))
            .collect()
    }

    fn columns(&self) -> Vec<Column<Any>> {
        self.iter().map(|&col| col.into()).collect()
    }

    fn annotations(&self) -> Vec<String> {
        vec![]
    }
}

/// Trait used to define lookup tables
pub trait LookupTable<F: Field> {
    type TableCellType;

    fn get_type(&self) -> Self::TableCellType;

    fn phase(&self) -> u8;

    /// Returns the list of ALL the table columns following the table order.
    fn columns(&self) -> Vec<Column<Any>>;

    /// Returns the list of ALL the table advice columns following the table
    /// order.
    fn advice_columns(&self) -> Vec<Column<Advice>> {
        self.columns()
            .iter()
            .map(|&col| col.try_into())
            .filter_map(|res| res.ok())
            .collect()
    }

    /// Returns the String annotations associated to each column of the table.
    fn annotations(&self) -> Vec<String>;

    /// Return the list of expressions used to define the lookup table.
    fn table_exprs(&self, meta: &mut VirtualCells<F>) -> Vec<Expression<F>> {
        self.columns()
            .iter()
            .map(|&column| meta.query_any(column, Rotation::cur()))
            .collect()
    }

    /// Annotates a lookup table by passing annotations for each of it's
    /// columns.
    fn annotate_columns(&self, cs: &mut ConstraintSystem<F>) {
        self.columns()
            .iter()
            .zip(self.annotations().iter())
            .for_each(|(&col, ann)| cs.annotate_lookup_any_column(col, || ann))
    }

    /// Annotates columns of a table embedded within a circuit region.
    fn annotate_columns_in_region(&self, region: &mut Region<F>) {
        self.columns()
            .iter()
            .zip(self.annotations().iter())
            .for_each(|(&col, ann)| region.name_column(|| ann, col))
    }
}
