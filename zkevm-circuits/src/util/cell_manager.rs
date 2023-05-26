use std::collections::{BTreeMap, HashMap};

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
}

impl<F: Field> Cell<F> {
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
    advice: Column<Advice>,
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
        if let Some(columns) = self.columns.get_mut(&cell_type) {
            columns.push(cell_column);
        } else {
            self.columns.insert(cell_type, vec![cell_column]);
        }
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
        self.columns.values().fold(0, |acc, g| acc + g.len())
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
        let mut acc = vec![];

        for _ in 0..count {
            let cell = self.query_cell(meta, cell_type);
            acc.push(cell);
        }

        acc
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

#[derive(Clone, Debug, Default)]
pub(crate) struct CMFixedWidthStrategyDistribution(HashMap<CellType, Vec<Column<Advice>>>);

impl CMFixedWidthStrategyDistribution {
    pub(crate) fn add(&mut self, cell_type: CellType, advice: Column<Advice>) {
        if let Some(v) = self.0.get_mut(&cell_type) {
            v.push(advice);
        } else {
            self.0.insert(cell_type, vec![advice]);
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct CMFixedWidthStrategy {
    advices: CMFixedWidthStrategyDistribution,
    height_offset: usize,

    next: HashMap<CellType, (usize, usize)>,
}

impl CMFixedWidthStrategy {
    pub fn new_from_advice<F: Field>(
        advices: CMFixedWidthStrategyDistribution,
        height_offset: usize,
    ) -> CMFixedWidthStrategy {
        CMFixedWidthStrategy {
            advices,
            height_offset,
            next: HashMap::default(),
        }
    }

    fn get_next(&self, cell_type: &CellType) -> (usize, usize) {
        *self.next.get(&cell_type).unwrap_or(&(0, 0))
    }

    fn set_next(&mut self, cell_type: &CellType, column_idx: usize, row: usize) {
        self.next.insert(*cell_type, (column_idx, row));
    }

    fn cells_used(&self, cell_type: &CellType, columns: &CellManagerColumns) -> usize {
        let (next_column_idx, next_row) = self.get_next(cell_type);
        let current_row = if next_column_idx == 0 {
            if next_row == 0 {
                return 0;
            }

            next_row - 1
        } else {
            next_row
        };

        let filled_rows_cells = if current_row == 0 {
            0
        } else {
            (current_row - 1) * columns.get_cell_type_width(*cell_type)
        };

        filled_rows_cells + next_column_idx
    }
}

impl CellManagerStrategy for CMFixedWidthStrategy {
    fn on_creation(&mut self, columns: &mut CellManagerColumns) {
        for (cell_type, advices) in self.advices.0.iter() {
            for column in advices.iter() {
                columns.add_column(*cell_type, *column)
            }
        }
    }

    fn query_cell<F: Field>(
        &mut self,
        columns: &mut CellManagerColumns,
        meta: &mut ConstraintSystem<F>,
        cell_type: CellType,
    ) -> Cell<F> {
        let (mut column_idx, mut row) = self.get_next(&cell_type);
        if cell_type == CellType::StoragePhase1 {
            let (_, row_perm) = self.get_next(&CellType::StoragePermutation);
            if row_perm < row {
                return self.query_cell(columns, meta, CellType::StoragePermutation);
            }
        }

        let column = columns
            .get_column(cell_type, column_idx)
            .expect("column not found");

        let cell = Cell::new_from_cs(meta, column.advice, column.idx, self.height_offset + row);

        column_idx += 1;
        if column_idx >= columns.get_cell_type_width(cell_type) {
            column_idx = 0;
            row += 1;
        }

        self.set_next(&cell_type, column_idx, row);

        cell
    }

    fn get_height(&self) -> usize {
        self.next
            .keys()
            .map(|cell_type| {
                let next = self.get_next(cell_type);
                if next.0 == 0 {
                    next.1
                } else {
                    next.1 + 1
                }
            })
            .max()
            .unwrap_or(0)
    }

    type Stats = BTreeMap<CellType, (usize, usize, usize)>;

    fn get_stats(&self, columns: &CellManagerColumns) -> Self::Stats {
        let mut data = BTreeMap::new();
        for cell_type in self.next.keys() {
            let next = self.get_next(cell_type);
            let height = if next.0 == 0 { next.1 } else { next.1 + 1 };
            data.insert(
                *cell_type,
                (
                    columns.get_cell_type_width(*cell_type),
                    height,
                    self.cells_used(cell_type, columns),
                ),
            );
        }
        data
    }
}

pub(crate) struct CMFixedHeigthStrategy {
    row_width: Vec<usize>,
    cell_type: CellType,
}

impl CMFixedHeigthStrategy {
    pub fn new(height: usize, cell_type: CellType) -> CMFixedHeigthStrategy {
        CMFixedHeigthStrategy {
            row_width: vec![0; height],
            cell_type,
        }
    }
}

impl CellManagerStrategy for CMFixedHeigthStrategy {
    fn on_creation(&mut self, _columns: &mut CellManagerColumns) {}

    fn query_cell<F: Field>(
        &mut self,
        columns: &mut CellManagerColumns,
        meta: &mut ConstraintSystem<F>,
        cell_type: CellType,
    ) -> Cell<F> {
        assert_eq!(
            cell_type, self.cell_type,
            "CMFixedHeigthStrategy can only work with one cell type"
        );

        let (row_idx, column_idx) = self.get_next();

        let cell = self.query_cell_at_pos(columns, meta, row_idx, column_idx);

        self.inc_row_width(row_idx);

        cell
    }

    fn get_height(&self) -> usize {
        todo!()
    }

    type Stats = ();

    fn get_stats(&self, columns: &CellManagerColumns) -> Self::Stats {
        todo!()
    }
}

impl CMFixedHeigthStrategy {
    fn get_next(&mut self) -> (usize, usize) {
        let mut best_row_idx = 0usize;
        let mut best_row_pos = 100000usize; // TODO: eliminate this magic number?
        for (row_idx, row) in self.row_width.iter().enumerate() {
            if *row < best_row_pos {
                best_row_pos = *row;
                best_row_idx = row_idx;
            }
        }

        (best_row_idx, best_row_pos)
    }

    fn inc_row_width(&mut self, row_idx: usize) {
        self.row_width[row_idx] += 1;
    }

    fn query_cell_at_pos<F: Field>(
        &mut self,
        columns: &mut CellManagerColumns,
        meta: &mut ConstraintSystem<F>,
        row_idx: usize,
        column_idx: usize,
    ) -> Cell<F> {
        let advice = if column_idx < columns.get_cell_type_width(self.cell_type) {
            columns
                .get_column(self.cell_type, column_idx)
                .expect("column not found")
                .advice
        } else {
            let advice = meta.advice_column();

            columns.add_column(self.cell_type, advice);

            advice
        };

        Cell::new_from_cs(meta, advice, column_idx, row_idx)
    }
}
