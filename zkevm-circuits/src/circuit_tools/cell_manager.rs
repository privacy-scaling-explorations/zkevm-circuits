//! Cell manager
use super::constraint_builder::ConstraintBuilder;
use crate::{
    circuit_tools::cached_region::CachedRegion,
    evm_circuit::util::rlc,
    table::LookupTable,
    util::{query_expression, word::Word, Expr},
};
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

pub(crate) type WordCell<F> = Word<Cell<F>>;

impl<F: Field> WordCell<F> {
    pub fn expr(&self) -> Word<Expression<F>> {
        Word::new([self.lo().expr(), self.hi().expr()])
    }
}

#[derive(Clone, Debug)]
pub struct CellConfig<C: CellType> {
    pub cell_type: C,
    pub phase: u8,
    pub is_permute: bool,
}

impl<C: CellType> CellConfig<C> {
    fn new(cell_type: C, phase: u8, is_permute: bool) -> Self {
        Self {
            cell_type,
            phase,
            is_permute,
        }
    }

    pub fn init_column<F: Field>(&self, meta: &mut ConstraintSystem<F>) -> Column<Advice> {
        let column = match self.phase {
            0 => meta.advice_column_in(FirstPhase),
            1 => meta.advice_column_in(SecondPhase),
            2 => meta.advice_column_in(ThirdPhase),
            _ => unreachable!(),
        };
        if self.is_permute {
            meta.enable_equality(column);
        }
        column
    }
}

pub trait CellType:
    Clone + Copy + Debug + PartialEq + Eq + PartialOrd + Ord + Hash + Default
{
    /// This is the table type for lookups
    type TableType: Clone + Copy + Debug + PartialEq + Eq + PartialOrd + Ord + Hash;

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

    /// Creates a type from a unique id
    fn create_type(id: usize) -> Self;

    /// Returns the table type of the lookup (if it's a lookup)
    fn lookup_table_type(&self) -> Option<Self::TableType>;

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

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum DefaultLookupType {}

impl Default for DefaultCellType {
    fn default() -> Self {
        Self::StoragePhase1
    }
}

impl CellType for DefaultCellType {
    type TableType = DefaultLookupType;

    fn byte_type() -> Option<Self> {
        Some(DefaultCellType::StoragePhase1)
    }

    fn storage_for_phase(phase: u8) -> Self {
        match phase {
            0 => DefaultCellType::StoragePhase1,
            1 => DefaultCellType::StoragePhase2,
            2 => DefaultCellType::StoragePhase3,
            _ => unreachable!(),
        }
    }

    fn create_type(_id: usize) -> Self {
        unreachable!()
    }

    fn lookup_table_type(&self) -> Option<Self::TableType> {
        None
    }
}

#[derive(Clone, Debug)]
pub(crate) struct CellColumn<F, C: CellType> {
    pub(crate) column: Column<Advice>,
    pub(crate) cell_type: C,
    pub(crate) cells: Vec<Cell<F>>,
    pub(crate) expr: Expression<F>,
    pub(super) height: usize,
    pub(super) index: usize,
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
    offset: usize,
}

impl<F: Field, C: CellType> CellManager<F, C> {
    pub(crate) fn new(max_height: usize, offset: usize) -> Self {
        Self {
            configs: Vec::new(),
            columns: Vec::new(),
            height: max_height,
            height_limit: max_height,
            offset,
        }
    }

    pub(crate) fn add_columns(
        &mut self,
        meta: &mut ConstraintSystem<F>,
        cb: &mut ConstraintBuilder<F, C>,
        cell_type: C,
        phase: u8,
        permutable: bool,
        num_columns: usize,
    ) {
        for _ in 0..num_columns {
            // Add a column of the specified type
            let config = CellConfig::new(cell_type, phase, permutable);
            let col = config.init_column(meta);
            let mut cells = Vec::new();
            for r in 0..self.height_limit {
                query_expression(meta, |meta| {
                    cells.push(Cell::new(meta, col, self.offset + r));
                });
            }
            let column_expr = cells[0].expr();
            self.columns.push(CellColumn {
                column: col,
                index: self.columns.len(),
                cell_type: config.cell_type,
                height: 0,
                expr: column_expr.expr(),
                cells,
            });
            self.configs.push(config);

            // For cell types that are lookups, generate the lookup here
            if let Some(table) = cell_type.lookup_table_type() {
                cb.add_lookup(
                    format!("{:?}", table),
                    vec![column_expr.expr()],
                    vec![rlc::expr(
                        &cb.table(table),
                        cb.lookup_challenge.clone().unwrap(),
                    )],
                );
            }
        }
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
