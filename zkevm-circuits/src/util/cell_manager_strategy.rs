use std::collections::{BTreeMap, HashMap};

use eth_types::Field;
use halo2_proofs::plonk::{Advice, Column, ConstraintSystem};

use super::cell_manager::{Cell, CellManagerColumns, CellManagerStrategy, CellType};

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

/// CMFixedWidthStrategy is a Cell Manager strategy that places the cells in the column that has
/// less height for a given CellType.
/// When a cell is queried for a CellType the strategy will find the column of that Cell Type that
/// has a lower height and add it there.
#[derive(Clone, Debug)]
pub(crate) struct CMFixedWidthStrategy {
    advices: CMFixedWidthStrategyDistribution,
    height_offset: usize,

    next: HashMap<CellType, (usize, usize)>,

    perm_substitution: bool,
}

impl CMFixedWidthStrategy {
    /// Creates a CMFixedWidthStrategy from a CMFixedWidthStrategyDistribution that contains advice
    /// columns categorized by Cell Type.
    /// The argument height_offset will be added to the rotation of the Cells, which is useful for a
    /// next step.
    pub fn new(
        advices: CMFixedWidthStrategyDistribution,
        height_offset: usize,
    ) -> CMFixedWidthStrategy {
        CMFixedWidthStrategy {
            advices,
            height_offset,
            next: HashMap::default(),
            perm_substitution: false,
        }
    }

    /// Enables the StoragePhase1 to StoragePermutation.
    /// When enabled if a  StoragePhase1 Cell is requested but the height would be lower if placed
    /// on a StoragePermutation column, then the StoragePermutation is used.
    pub fn with_perm_substitution(mut self) -> Self {
        self.perm_substitution = true;

        self
    }

    fn get_next(&self, cell_type: &CellType) -> (usize, usize) {
        *self.next.get(cell_type).unwrap_or(&(0, 0))
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
    type Stats = BTreeMap<CellType, (usize, usize, usize)>;

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
        if self.perm_substitution && cell_type == CellType::StoragePhase1 {
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

// TODO: This strategy is unfinished.
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

    fn get_stats(&self, _columns: &CellManagerColumns) -> Self::Stats {
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
