use std::collections::HashMap;

use eth_types::Field;
use gadgets::util::Expr;
use halo2_proofs::{
    circuit::{AssignedCell, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, VirtualCells},
    poly::Rotation,
};

use crate::{
    evm_circuit::{table::Table, util::CachedRegion},
    util::query_expression,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
/// CellType
pub(crate) enum CellType {
    StoragePhase1,
    StoragePhase2,
    StoragePermutation,
    LookupByte,
    Lookup(Table),
}

impl CellType {
    // The phase that given `Expression` becomes evaluateable.
    pub(crate) fn expr_phase<F: Field>(expr: &Expression<F>) -> u8 {
        use Expression::*;
        match expr {
            Challenge(challenge) => challenge.phase() + 1,
            Advice(query) => query.phase(),
            Constant(_) | Selector(_) | Fixed(_) | Instance(_) => 0,
            Negated(a) | Expression::Scaled(a, _) => Self::expr_phase(a),
            Sum(a, b) | Product(a, b) => std::cmp::max(Self::expr_phase(a), Self::expr_phase(b)),
        }
    }

    /// Return the storage phase of phase
    pub(crate) fn storage_for_phase(phase: u8) -> CellType {
        match phase {
            0 => CellType::StoragePhase1,
            1 => CellType::StoragePhase2,
            _ => unreachable!(),
        }
    }

    /// Return the storage cell of the expression
    pub(crate) fn storage_for_expr<F: Field>(expr: &Expression<F>) -> CellType {
        Self::storage_for_phase(Self::expr_phase::<F>(expr))
    }
}

#[derive(Clone, Debug)]
/// Cell
pub(crate) struct Cell<F> {
    pub(crate) expression: Expression<F>,
    pub(crate) column_expression: Expression<F>,
    pub(crate) column: Column<Advice>,
    pub(crate) column_idx: usize,
    pub(crate) rotation: usize,

    // DEPRECATED: the same value as column_idx
    pub(crate) cell_column_index: usize,
}

impl<F: Field> Cell<F> {
    pub fn new(
        meta: &mut VirtualCells<F>,
        column: Column<Advice>,
        column_idx: usize,
        rotation: usize,
    ) -> Cell<F> {
        Cell {
            expression: meta.query_advice(column, Rotation(rotation as i32)),
            column_expression: meta.query_advice(column, Rotation::cur()),
            column,
            column_idx,
            rotation,
            cell_column_index: column_idx,
        }
    }
    pub fn new_from_cs(
        meta: &mut ConstraintSystem<F>,
        column: Column<Advice>,
        column_idx: usize,
        rotation: usize,
    ) -> Cell<F> {
        query_expression(meta, |meta| Cell::new(meta, column, column_idx, rotation))
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        value: Value<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        region.assign_advice(
            || {
                format!(
                    "Cell column: {:?} and rotation: {}",
                    self.column, self.rotation
                )
            },
            self.column,
            offset + self.rotation,
            || value,
        )
    }
}

impl<F: Field> Expr<F> for Cell<F> {
    fn expr(&self) -> Expression<F> {
        self.expression.clone()
    }
}

impl<F: Field> Expr<F> for &Cell<F> {
    fn expr(&self) -> Expression<F> {
        self.expression.clone()
    }
}

#[derive(Debug, Clone)]
/// CellColumn
pub(crate) struct CellColumn {
    pub advice: Column<Advice>,
    pub cell_type: CellType,
    pub idx: usize,
}

impl CellColumn {
    pub fn new(advice: Column<Advice>, cell_type: CellType, idx: usize) -> CellColumn {
        CellColumn {
            advice,
            cell_type,
            idx,
        }
    }

    pub fn expr<F: Field>(&self, meta: &mut ConstraintSystem<F>) -> Expression<F> {
        query_expression(meta, |meta| meta.query_advice(self.advice, Rotation::cur()))
    }
}

/// CellManagerStrategy
pub(crate) trait CellManagerStrategy {
    type Stats;

    /// on_creation
    fn on_creation(&mut self, columns: &mut CellManagerColumns);
    /// query_cell
    fn query_cell<F: Field>(
        &mut self,
        columns: &mut CellManagerColumns,
        meta: &mut ConstraintSystem<F>,
        cell_type: CellType,
    ) -> Cell<F>;
    /// get_height
    fn get_height(&self) -> usize;

    fn get_stats(&self, columns: &CellManagerColumns) -> Self::Stats;
}

#[derive(Default, Debug, Clone)]
pub(crate) struct CellManagerColumns {
    columns: HashMap<CellType, Vec<CellColumn>>,
    columns_list: Vec<CellColumn>,
}

impl CellManagerColumns {
    pub fn add_column(&mut self, cell_type: CellType, column: Column<Advice>) {
        let idx = self.columns_list.len();
        let cell_column = CellColumn::new(column, cell_type, idx);

        self.columns_list.push(cell_column.clone());
        self.columns
            .entry(cell_type)
            .and_modify(|columns| columns.push(cell_column.clone()))
            .or_insert(vec![cell_column]);
    }

    pub fn get_cell_type_width(&self, cell_type: CellType) -> usize {
        if let Some(columns) = self.columns.get(&cell_type) {
            columns.len()
        } else {
            0
        }
    }

    pub fn get_column(&self, cell_type: CellType, column_idx: usize) -> Option<&CellColumn> {
        if let Some(columns) = self.columns.get(&cell_type) {
            columns.get(column_idx)
        } else {
            None
        }
    }

    pub fn columns(&self) -> Vec<CellColumn> {
        self.columns_list.clone()
    }

    pub fn get_width(&self) -> usize {
        self.columns_list.len()
    }
}

#[derive(Clone, Debug)]
pub(crate) struct CellManager<S: CellManagerStrategy> {
    columns: CellManagerColumns,
    strategy: S,
}

impl<Stats, S: CellManagerStrategy<Stats = Stats>> CellManager<S> {
    pub fn new(mut strategy: S) -> CellManager<S> {
        let mut columns = CellManagerColumns::default();

        strategy.on_creation(&mut columns);

        CellManager { columns, strategy }
    }

    /// query_cell
    pub fn query_cell<F: Field>(
        &mut self,
        meta: &mut ConstraintSystem<F>,
        cell_type: CellType,
    ) -> Cell<F> {
        self.strategy.query_cell(&mut self.columns, meta, cell_type)
    }
    /// query_cells
    pub fn query_cells<F: Field>(
        &mut self,
        meta: &mut ConstraintSystem<F>,
        cell_type: CellType,
        count: usize,
    ) -> Vec<Cell<F>> {
        (0..count)
            .map(|_| self.query_cell(meta, cell_type))
            .collect()
    }

    /// get_height
    pub fn get_height(&self) -> usize {
        self.strategy.get_height()
    }

    pub fn columns(&self) -> Vec<CellColumn> {
        self.columns.columns()
    }
    /// get_width
    pub fn get_width(&self) -> usize {
        self.columns.get_width()
    }

    pub fn get_stats(&self) -> Stats {
        self.strategy.get_stats(&self.columns)
    }
}

pub(crate) use super::cell_manager_strategy::*;
