//! Cell manager
use crate::{
    circuit_tools::cached_region::CachedRegion,
    util::{query_expression, Expr}, evm_circuit::util::rlc,
};

use crate::table::LookupTable;
use eth_types::Field;
use halo2_proofs::{
    circuit::{AssignedCell, Value},
    plonk::{
        Advice, Any, Column, ConstraintSystem, Error, Expression, FirstPhase, SecondPhase,
        ThirdPhase, VirtualCells,
    },
    poly::Rotation,
};
use std::{cmp::Ordering, collections::BTreeMap, fmt::Debug, hash::Hash};

#[derive(Clone, Debug, Default)]
pub(crate) struct Cell<F> {
    // expression for constraint
    expression: Option<Expression<F>>,
    pub column: Option<Column<Advice>>,
    // relative position to selector for synthesis
    pub rotation: usize,
}

impl<F: Field> Cell<F> {
    pub(crate) fn new(meta: &mut VirtualCells<F>, column: Column<Advice>, rotation: usize) -> Self {
        Self {
            expression: Some(meta.query_advice(column, Rotation(rotation as i32))),
            column: Some(column),
            rotation,
        }
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        value: F,
    ) -> Result<AssignedCell<F, F>, Error> {
        region.assign_advice(
            || {
                format!(
                    "Cell column: {:?} and rotation: {}",
                    self.column, self.rotation
                )
            },
            self.column.unwrap(),
            offset + self.rotation,
            || Value::known(value),
        )
    }

    pub(crate) fn assign_value(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        value: Value<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        region.assign_advice(
            || {
                format!(
                    "Cell column: {:?} and rotation: {}",
                    self.column.unwrap(),
                    self.rotation
                )
            },
            self.column.unwrap(),
            offset + self.rotation,
            || value,
        )
    }

    pub(crate) fn column(&self) -> Column<Advice> {
        self.column.unwrap()
    }

    pub(crate) fn rotation(&self) -> usize {
        self.rotation
    }

    pub(crate) fn rot(&self, meta: &mut VirtualCells<F>, rot: usize) -> Expression<F> {
        meta.query_advice(self.column.unwrap(), Rotation((self.rotation + rot) as i32))
    }

    pub(crate) fn identifier(&self) -> String {
        self.expr().identifier()
    }
}

impl<F: Field> Expr<F> for Cell<F> {
    fn expr(&self) -> Expression<F> {
        self.expression.as_ref().unwrap().clone()
    }
}

impl<F: Field> Expr<F> for &Cell<F> {
    fn expr(&self) -> Expression<F> {
        self.expression.as_ref().unwrap().clone()
    }
}

#[derive(Clone, Debug)]
pub struct CellConfig<C: CellType> {
    pub cell_type: C,
    pub num_columns: usize,
    pub phase: u8,
    pub is_permute: bool,
}

impl<C: CellType> From<(C, usize, u8, bool)> for CellConfig<C> {
    fn from((cell_type, num_columns, phase, is_permute): (C, usize, u8, bool)) -> Self {
        Self {
            cell_type,
            num_columns,
            phase,
            is_permute,
        }
    }
}

impl<C: CellType> CellConfig<C> {
    pub fn init_columns<F: Field>(&self, meta: &mut ConstraintSystem<F>) -> Vec<Column<Advice>> {
        let mut columns = Vec::with_capacity(self.num_columns);
        for _ in 0..self.num_columns {
            let tmp = match self.phase {
                1 => meta.advice_column_in(FirstPhase),
                2 => meta.advice_column_in(SecondPhase),
                3 => meta.advice_column_in(ThirdPhase),
                _ => unreachable!(),
            };
            columns.push(tmp);
        }
        println!("cm init {:?} column: {:?}", self.cell_type, self.num_columns);
        if self.is_permute {
            let _ = columns
                .iter()
                .map(|c| meta.enable_equality(*c))
                .collect::<Vec<()>>();
        }
        columns
    }
}

pub trait CellType:
    Clone + Copy + Debug + PartialEq + Eq + PartialOrd + Ord + Hash + Default
{
    fn byte_type() -> Option<Self>;

    // The phase that given `Expression` becomes evaluateable.
    fn expr_phase<F: Field>(expr: &Expression<F>) -> u8 {
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
    fn storage_for_phase(phase: u8) -> Self;

    /// Return the storage cell of the expression
    fn storage_for_expr<F: Field>(expr: &Expression<F>) -> Self {
        Self::storage_for_phase(Self::expr_phase::<F>(expr))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum DefaultCellType {
    StoragePhase1,
    StoragePhase2,
    StoragePhase3,
}

impl Default for DefaultCellType {
    fn default() -> Self {
        Self::StoragePhase1
    }
}

impl CellType for DefaultCellType {
    fn byte_type() -> Option<Self> {
        Some(DefaultCellType::StoragePhase1)
    }

    fn storage_for_phase(phase: u8) -> Self {
        match phase {
            1 => DefaultCellType::StoragePhase1,
            2 => DefaultCellType::StoragePhase2,
            3 => DefaultCellType::StoragePhase3,
            _ => unreachable!(),
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct CellColumn<F, C: CellType> {
    pub(crate) column: Column<Advice>,
    pub(crate) cell_type: C,
    pub(crate) cells: Vec<Cell<F>>,
    pub(crate) expr: Expression<F>,
    height: usize,
    index: usize,
}

impl<F: Field, C: CellType> PartialEq for CellColumn<F, C> {
    fn eq(&self, other: &Self) -> bool {
        self.index == other.index
            && self.cell_type == other.cell_type
            && self.height == other.height
    }
}

impl<F: Field, C: CellType> Eq for CellColumn<F, C> {}

impl<F: Field, C: CellType> PartialOrd for CellColumn<F, C> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.height.partial_cmp(&other.height)
    }
}

impl<F: Field, C: CellType> Ord for CellColumn<F, C> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.height.cmp(&other.height)
    }
}

impl<F: Field, C: CellType> Expr<F> for CellColumn<F, C> {
    fn expr(&self) -> Expression<F> {
        self.expr.clone()
    }
}


#[derive(Clone, Debug, Default)]
pub struct CellManager<F, C: CellType> {
    configs: Vec<CellConfig<C>>,
    columns: Vec<CellColumn<F, C>>,
    height: usize,
    height_limit: usize,
}

impl<F: Field, C: CellType> CellManager<F, C> {
    pub(crate) fn new(
        meta: &mut ConstraintSystem<F>,
        configs: Vec<(C, usize, u8, bool)>,
        offset: usize,
        max_height: usize,
    ) -> Self {
        let mut cm = CellManager::default();
        cm.height_limit = max_height;
        configs
            .into_iter()
            .for_each(|c| cm.add_celltype(meta, c, offset));
        cm.height = max_height;
        cm
    }

    pub(crate) fn add_celltype(
        &mut self,
        meta: &mut ConstraintSystem<F>,
        config: (C, usize, u8, bool),
        offset: usize,
    ) {
        if self.get_typed_columns(config.0).len() != 0 {
            panic!("CellManager: cell type {:?} already exists", config.0);
        }
        let config = CellConfig::from(config);
        for col in config.init_columns(meta).iter() {
            let mut cells = Vec::new();
            for r in 0..self.height_limit {
                query_expression(meta, |meta| {
                    cells.push(Cell::new(meta, *col, offset + r));
                });
            }
            self.columns.push(CellColumn {
                column: *col,
                index: self.columns.len(),
                cell_type: config.cell_type,
                height: 0,
                expr: cells[0].expr(),
                cells,
            });
        }
        self.configs.push(config);
    }

    pub(crate) fn restart(&mut self) {
        self.height = self.height_limit;
        for col in self.columns.iter_mut() {
            col.height = 0;
        }
    }

    pub(crate) fn query_cells(&mut self, cell_type: C, count: usize) -> Vec<Cell<F>> {
        let mut cells = Vec::with_capacity(count);
        while cells.len() < count {
            let column_idx = self.next_column(cell_type);
            let column = &mut self.columns[column_idx];
            cells.push(column.cells[column.height].clone());
            column.height += 1;
        }
        cells
    }

    pub(crate) fn query_cell(&mut self, cell_type: C) -> Cell<F> {
        self.query_cells(cell_type, 1)[0].clone()
    }

    pub(crate) fn reset(&mut self, height_limit: usize) {
        assert!(height_limit <= self.height);
        self.height_limit = height_limit;
        for column in self.columns.iter_mut() {
            column.height = 0;
        }
    }

    fn next_column(&self, cell_type: C) -> usize {
        let mut best_index: Option<usize> = None;
        let mut best_height = self.height;
        for column in self.columns.iter() {
            if column.cell_type == cell_type && column.height < best_height {
                best_index = Some(column.index);
                best_height = column.height;
            }
        }
        if best_height >= self.height_limit {
            best_index = None;
        }
        match best_index {
            Some(index) => index,
            None => unreachable!("not enough cells for query: {:?}", cell_type),
        }
    }

    pub(crate) fn get_height(&self) -> usize {
        self.columns
            .iter()
            .map(|column| column.height)
            .max()
            .unwrap()
    }

    /// Returns a map of CellType -> (width, height, num_cells)
    pub(crate) fn get_stats(&self) -> BTreeMap<C, (usize, usize, usize)> {
        let mut data = BTreeMap::new();
        for column in self.columns.iter() {
            let (mut count, mut height, mut num_cells) =
                data.get(&column.cell_type).unwrap_or(&(0, 0, 0));
            count += 1;
            height = height.max(column.height);
            num_cells += column.height;
            data.insert(column.cell_type, (count, height, num_cells));
        }
        data
    }

    pub(crate) fn columns(&self) -> &[CellColumn<F, C>] {
        &self.columns
    }

    pub(crate) fn get_typed_columns(&self, cell_type: C) -> Vec<CellColumn<F, C>> {
        let mut columns = Vec::new();
        for column in self.columns.iter() {
            if column.cell_type == cell_type {
                columns.push(column.clone());
            }
        }
        columns
    }

    pub(crate) fn get_config(&self, cell_type: C) -> Option<CellConfig<C>> {
        for config in self.configs.iter() {
            if config.cell_type == cell_type {
                return Some(config.clone());
            }
        }
        None
    }
}

/// LookupTable created dynamically and stored in an advice column
#[derive(Clone, Debug)]
pub struct DynamicLookupTable {
    /// Table
    pub table: Column<Advice>,
}

impl DynamicLookupTable {
    /// Construct a new BlockTable
    pub fn from<F: Field, C: CellType>(cm: &CellManager<F, C>, cell_type: C) -> Self {
        let table_columns = cm.get_typed_columns(cell_type);
        assert_eq!(table_columns.len(), 1);
        Self {
            table: table_columns[0].column,
        }
    }
}

impl<F: Field> LookupTable<F> for DynamicLookupTable {
    fn columns(&self) -> Vec<Column<Any>> {
        vec![self.table.into()]
    }

    fn annotations(&self) -> Vec<String> {
        vec![String::from("generated")]
    }
}
