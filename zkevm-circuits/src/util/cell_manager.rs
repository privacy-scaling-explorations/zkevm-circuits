use std::collections::HashMap;

use halo2_proofs::{
    arithmetic::Field,
    halo2curves::FieldExt,
    plonk::{Advice, Column, ConstraintSystem, Expression, VirtualCells},
    poly::Rotation,
};

use crate::{evm_circuit::table::Table, util::query_expression};

#[derive(Eq, Hash, PartialEq, Clone, Copy, Debug)]
/// CellType
pub(crate) enum CellType {
    StoragePhase1,
    StoragePhase2,
    StoragePermutation,
    LookupByte,
    Lookup(Table),
}

#[derive(Clone, Debug)]
/// Cell
pub(crate) struct Cell<F> {
    pub(crate) expression: Expression<F>,
    pub(crate) column_expression: Expression<F>,
    pub(crate) column: Column<Advice>,
    pub(crate) column_idx: usize,
    pub(crate) rotation: i32,

    // DEPRECATED: the same value as column_idx
    pub(crate) cell_column_index: usize,
}

impl<F: Field> Cell<F> {
    pub fn new(
        meta: &mut VirtualCells<F>,
        column: Column<Advice>,
        column_idx: usize,
        rotation: i32,
    ) -> Cell<F> {
        Cell {
            expression: meta.query_advice(column, Rotation(rotation)),
            column_expression: meta.query_advice(column, Rotation::cur()),
            column,
            column_idx,
            rotation,
            cell_column_index: column_idx,
        }
    }
}

#[derive(Debug, Clone)]
/// CellColumn
pub struct CellColumn {
    advice: Column<Advice>,
}

impl CellColumn {
    fn new(advice: Column<Advice>) -> CellColumn {
        CellColumn { advice }
    }
}

/// CellManagerStrategy
pub(crate) trait CellManagerStrategy<F: Field> {
    /// on_creation
    fn on_creation(&mut self, columns: &mut CellManagerColumns);
    /// query_cell
    fn query_cell(
        &mut self,
        columns: &mut CellManagerColumns,
        meta: &mut ConstraintSystem<F>,
        cell_type: CellType,
    ) -> Cell<F>;
    /// get_height
    fn get_height(&self) -> usize;
}

#[derive(Default)]
pub(crate) struct CellManagerColumns {
    columns: HashMap<CellType, Vec<CellColumn>>,
}

impl CellManagerColumns {
    pub fn add_column(&mut self, cell_type: CellType, column: Column<Advice>) {
        if let Some(columns) = self.columns.get_mut(&cell_type) {
            columns.push(CellColumn::new(column));
        } else {
            self.columns
                .insert(cell_type, vec![CellColumn::new(column)]);
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
        let mut acc = vec![];

        for g in self.columns.values() {
            acc.extend((*g).clone());
        }

        acc
    }

    pub fn get_width(&self) -> usize {
        self.columns.values().fold(0, |acc, g| acc + g.len())
    }
}

pub(crate) struct CellManager<F> {
    columns: CellManagerColumns,
    strategy: dyn CellManagerStrategy<F>,
}

impl<F: Field> CellManager<F> {
    /// query_cell
    fn query_cell(&mut self, meta: &mut ConstraintSystem<F>, cell_type: CellType) -> Cell<F> {
        self.strategy.query_cell(&mut self.columns, meta, cell_type)
    }
    /// query_cells
    fn query_cells(
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
    fn get_height(&self) -> usize {
        self.strategy.get_height()
    }
}

impl<F> CellManager<F> {
    /// columns
    fn columns(&self) -> Vec<CellColumn> {
        self.columns.columns()
    }
    /// get_width
    fn get_width(&self) -> usize {
        self.columns.get_width()
    }
}

pub(crate) struct CMFixedWidthStrategy {
    advices: HashMap<CellType, Vec<Column<Advice>>>,
    height_offset: usize,

    next: HashMap<CellType, (usize, usize)>,
}

impl CMFixedWidthStrategy {
    pub fn new_from_advice<F: Field>(
        advices: HashMap<CellType, Vec<Column<Advice>>>,
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
}

impl<F: FieldExt> CellManagerStrategy<F> for CMFixedWidthStrategy {
    fn on_creation(&mut self, columns: &mut CellManagerColumns) {
        for (cell_type, advices) in self.advices.iter() {
            for column in advices.iter() {
                columns.add_column(*cell_type, *column)
            }
        }
    }

    fn query_cell(
        &mut self,
        columns: &mut CellManagerColumns,
        meta: &mut ConstraintSystem<F>,
        cell_type: CellType,
    ) -> Cell<F> {
        let (mut column_idx, mut row) = self.get_next(&cell_type);

        let column = columns
            .get_column(cell_type, column_idx)
            .expect("column not found");

        let cell = query_expression(meta, |meta| {
            Cell::new(
                meta,
                column.advice,
                column_idx,
                (self.height_offset + row) as i32,
            )
        });

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

impl<F: FieldExt> CellManagerStrategy<F> for CMFixedHeigthStrategy {
    fn on_creation(&mut self, _columns: &mut CellManagerColumns) {}

    fn query_cell(
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

    fn query_cell_at_pos<F: FieldExt>(
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

        query_expression(meta, |meta| {
            Cell::new(meta, advice, column_idx, row_idx as i32)
        })
    }
}
