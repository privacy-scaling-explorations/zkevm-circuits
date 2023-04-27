use std::{collections::HashMap, marker::PhantomData};

use halo2_proofs::plonk::{Advice, Column};

use crate::evm_circuit::table::Table;

#[derive(Eq, Hash, PartialEq)]
/// CellType
pub(crate) enum CellType {
    StoragePhase1,
    StoragePhase2,
    StoragePermutation,
    LookupByte,
    Lookup(Table),
}

/// Cell
pub struct Cell<F> {
    _p: PhantomData<F>,
}

/// CellColumn
pub struct CellColumn<F> {
    _p: PhantomData<F>,
}

/// CellManagerStrategy
pub(crate) trait CellManagerStrategy<F> {
    // /// query_top_aligned_cell
    // fn query_top_aligned_cell(&mut self, cell_type: CellType) -> Cell<F>;
    // query_cell
    // fn query_cell(&mut self, cell_type: CellType) -> Cell<F>;
    // query_cells
    // fn query_cells(&mut self, cell_type: CellType, count: usize) -> Vec<Cell<F>>;
    // columns
    // fn columns(&self) -> &[CellColumn<F>];
    // get_width
    // fn get_width(&self) -> usize;
    // get_height
    // fn get_height(&self) -> usize;

    /// on_creation
    fn on_creation(&mut self, columns: &mut CellManagerColumns);
    /// query_cell
    fn query_cell(&mut self, columns: &mut CellManagerColumns, cell_type: CellType);
    /// get_height
    fn get_height(&self) -> usize;
}

#[derive(Default)]
pub(crate) struct CellManagerColumns {
    columns: HashMap<CellType, Vec<Column<Advice>>>,
}

impl CellManagerColumns {
    pub fn add_column(&mut self, cell_type: CellType, column: Column<Advice>) {
        if let Some(columns) = self.columns.get_mut(&cell_type) {
            columns.push(column);
        } else {
            self.columns.insert(cell_type, vec![column]);
        }
    }

    pub fn get_cell_type_width(&self, cell_type: CellType) -> usize {
        if let Some(columns) = self.columns.get(&cell_type) {
            columns.len()
        } else {
            0
        }
    }

    pub fn get_column(&self, cell_type: CellType, column_idx: usize) -> Option<&Column<Advice>> {
        if let Some(columns) = self.columns.get(&cell_type) {
            columns.get(column_idx)
        } else {
            None
        }
    }

    pub fn columns<F>(&self) -> &[CellColumn<F>] {
        todo!()
    }

    pub fn get_width(&self) -> usize {
        todo!()
    }
}

pub(crate) struct CellManager<F> {
    columns: CellManagerColumns,
    strategy: dyn CellManagerStrategy<F>,
}

impl<F> CellManager<F> {
    /// query_top_aligned_cell
    fn query_top_aligned_cell(&mut self, cell_type: CellType) -> Cell<F> {
        todo!()
    }
    /// query_cell
    fn query_cell(&mut self, cell_type: CellType) -> Cell<F> {
        todo!()
    }
    /// query_cells
    fn query_cells(&mut self, cell_type: CellType, count: usize) -> Vec<Cell<F>> {
        todo!()
    }
    /// columns
    fn columns(&self) -> &[CellColumn<F>] {
        todo!()
    }
    /// get_width
    fn get_width(&self) -> usize {
        todo!()
    }
    /// get_height
    fn get_height(&self) -> usize {
        todo!()
    }
}
