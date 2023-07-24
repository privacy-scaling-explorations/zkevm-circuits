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

pub(crate) use super::cell_manager_strategy::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
/// CellType represent a category of cell (and column).
pub(crate) enum CellType {
    StoragePhase1,
    StoragePhase2,
    StoragePermutation,
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

    /// Return the storage phase of phase.
    pub(crate) fn storage_for_phase(phase: u8) -> CellType {
        match phase {
            0 => CellType::StoragePhase1,
            1 => CellType::StoragePhase2,
            _ => unreachable!(),
        }
    }

    /// Return the storage cell of the expression.
    pub(crate) fn storage_for_expr<F: Field>(expr: &Expression<F>) -> CellType {
        Self::storage_for_phase(Self::expr_phase::<F>(expr))
    }
}

#[derive(Clone, Debug)]
/// Cell is a (column, rotation) pair that has been placed and queried by the Cell Manager.
pub struct Cell<F> {
    pub(crate) expression: Expression<F>,
    _column_expression: Expression<F>,
    pub(crate) column: Column<Advice>,
    pub(crate) column_idx: usize,
    pub(crate) rotation: usize,
}

impl<F: Field> Cell<F> {
    /// Creates a Cell from VirtualCells.
    pub fn new(
        meta: &mut VirtualCells<F>,
        column: Column<Advice>,
        _column_idx: usize,
        rotation: usize,
    ) -> Cell<F> {
        Cell {
            expression: meta.query_advice(column, Rotation(rotation as i32)),
            _column_expression: meta.query_advice(column, Rotation::cur()),
            column,
            column_idx: _column_idx,
            rotation,
        }
    }

    /// Creates a Cell from ConstraintSystem.
    pub fn new_from_cs(
        meta: &mut ConstraintSystem<F>,
        column: Column<Advice>,
        column_idx: usize,
        rotation: usize,
    ) -> Cell<F> {
        query_expression(meta, |meta| Cell::new(meta, column, column_idx, rotation))
    }

    /// Assigns a Cell during witness generation.
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

    pub(crate) fn at_offset(&self, meta: &mut ConstraintSystem<F>, offset: i32) -> Self {
        Self::new_from_cs(
            meta,
            self.column,
            self.column_idx,
            (self.rotation as i32 + offset) as usize,
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

#[derive(Clone)]
pub(crate) struct CellValueOnly {
    pub(crate) column_idx: usize,
    pub(crate) rotation: usize,
}

impl CellValueOnly {
    pub fn new(column_idx: usize, rotation: usize) -> Self {
        Self {
            column_idx,
            rotation,
        }
    }
}

impl<F> From<Cell<F>> for CellValueOnly {
    fn from(value: Cell<F>) -> Self {
        CellValueOnly::new(value.column_idx, value.rotation)
    }
}

#[derive(Debug, Clone)]
/// CellColumn represent a column that is managed by a Cell Manager.
pub(crate) struct CellColumn {
    pub advice: Column<Advice>,
    pub cell_type: CellType,
    pub idx: usize,
}

impl CellColumn {
    // Creates a CellColumn from a Column and Cell Type.
    pub fn new(advice: Column<Advice>, cell_type: CellType, idx: usize) -> CellColumn {
        CellColumn {
            advice,
            cell_type,
            idx,
        }
    }

    /// Queries column at rotation 0.
    pub fn expr<F: Field>(&self, meta: &mut ConstraintSystem<F>) -> Expression<F> {
        query_expression(meta, |meta| meta.query_advice(self.advice, Rotation::cur()))
    }

    pub fn expr_vc<F: Field>(&self, meta: &mut VirtualCells<F>) -> Expression<F> {
        meta.query_advice(self.advice, Rotation::cur())
    }
}

/// CellManagerStrategy is a strategy to place cells by the Cell Manager.
pub(crate) trait CellManagerStrategy {
    type Stats;

    type Affinity;

    /// The cell manager will call on_creation when built, so the columns can be set up by the
    /// strategy.
    fn on_creation(&mut self, columns: &mut CellManagerColumns);

    /// Queries a cell from the strategy.
    fn query_cell<F: Field>(
        &mut self,
        columns: &mut CellManagerColumns,
        meta: &mut ConstraintSystem<F>,
        cell_type: CellType,
    ) -> Cell<F>;

    fn query_cell_with_affinity<F: Field>(
        &mut self,
        columns: &mut CellManagerColumns,
        meta: &mut ConstraintSystem<F>,
        cell_type: CellType,
        affinity: Self::Affinity,
    ) -> Cell<F>;

    fn query_cell_value(
        &mut self,
        columns: &mut CellManagerColumns,
        cell_type: CellType,
    ) -> CellValueOnly;

    fn query_cell_value_with_affinity(
        &mut self,
        columns: &mut CellManagerColumns,
        cell_type: CellType,
        affinity: Self::Affinity,
    ) -> CellValueOnly;

    /// Gets the current height of the cell manager, the max rotation of any cell (without
    /// considering offset).
    fn get_height(&self) -> usize;

    /// Returns stats about this cells placement.
    fn get_stats(&self, columns: &CellManagerColumns) -> Self::Stats;
}

/// CellManagerColumns contains the columns of the Cell Manager and is the main interface between
/// the Cell Manager and the used strategy.
#[derive(Default, Debug, Clone)]
pub(crate) struct CellManagerColumns {
    columns: HashMap<CellType, Vec<CellColumn>>,
    columns_list: Vec<CellColumn>,
}

impl CellManagerColumns {
    /// Adds a column.
    pub fn add_column(&mut self, cell_type: CellType, column: Column<Advice>) {
        let idx = self.columns_list.len();
        let cell_column = CellColumn::new(column, cell_type, idx);

        self.columns_list.push(cell_column.clone());
        self.columns
            .entry(cell_type)
            .and_modify(|columns| columns.push(cell_column.clone()))
            .or_insert(vec![cell_column]);
    }

    /// Get the number of columns for a given Cell Type.
    pub fn get_cell_type_width(&self, cell_type: CellType) -> usize {
        if let Some(columns) = self.columns.get(&cell_type) {
            columns.len()
        } else {
            0
        }
    }

    /// Returns a column of a given cell type and index amoung all columns of that cell type.
    pub fn get_column(&self, cell_type: CellType, column_idx: usize) -> Option<&CellColumn> {
        if let Some(columns) = self.columns.get(&cell_type) {
            columns.get(column_idx)
        } else {
            None
        }
    }

    /// Returns an array with all the columns.
    pub fn columns(&self) -> Vec<CellColumn> {
        self.columns_list.clone()
    }

    #[allow(dead_code, reason = "under active development")]
    /// Returns the number of columns.
    pub fn get_width(&self) -> usize {
        self.columns_list.len()
    }
}

/// CellManager places and return cells in an area of the plonkish table given a strategy.
#[derive(Clone, Debug)]
pub(crate) struct CellManager<S: CellManagerStrategy> {
    columns: CellManagerColumns,
    strategy: S,
}

impl<Stats, S: CellManagerStrategy<Stats = Stats>> CellManager<S> {
    /// Creates a Cell Manager with a given strategy.
    pub fn new(mut strategy: S) -> CellManager<S> {
        let mut columns = CellManagerColumns::default();

        strategy.on_creation(&mut columns);

        CellManager { columns, strategy }
    }

    /// Places, and returns a Cell for a given cell type following the strategy.
    pub fn query_cell<F: Field>(
        &mut self,
        meta: &mut ConstraintSystem<F>,
        cell_type: CellType,
    ) -> Cell<F> {
        self.strategy.query_cell(&mut self.columns, meta, cell_type)
    }

    pub fn query_cell_with_affinity<F: Field>(
        &mut self,
        meta: &mut ConstraintSystem<F>,
        cell_type: CellType,
        affinity: S::Affinity,
    ) -> Cell<F> {
        self.strategy
            .query_cell_with_affinity(&mut self.columns, meta, cell_type, affinity)
    }

    /// Places, and returns `count` Cells for a given cell type following the strategy.
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

    pub fn query_cell_value(&mut self, cell_type: CellType) -> CellValueOnly {
        self.strategy.query_cell_value(&mut self.columns, cell_type)
    }

    pub fn query_cell_value_with_affinity(
        &mut self,
        cell_type: CellType,
        affinity: S::Affinity,
    ) -> CellValueOnly {
        self.strategy
            .query_cell_value_with_affinity(&mut self.columns, cell_type, affinity)
    }

    /// Gets the current height of the cell manager, the max rotation of any cell (without
    /// considering offset).
    pub fn get_height(&self) -> usize {
        self.strategy.get_height()
    }

    /// Returns all the columns managed by this Cell Manager.
    pub fn columns(&self) -> Vec<CellColumn> {
        self.columns.columns()
    }

    #[allow(dead_code, reason = "under active development")]
    /// Returns the number of columns managed by this Cell Manager.
    pub fn get_width(&self) -> usize {
        self.columns.get_width()
    }

    /// Returns the statistics about this Cell Manager.
    pub fn get_stats(&self) -> Stats {
        self.strategy.get_stats(&self.columns)
    }

    pub fn get_strategy(&mut self) -> &mut S {
        &mut self.strategy
    }
}
