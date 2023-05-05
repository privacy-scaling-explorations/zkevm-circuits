//! Cell manager
use crate::util::{Expr, query_expression};
use crate::circuit_tools::cached_region::CachedRegion;

use eth_types::Field;
use halo2_proofs::{
    circuit::{AssignedCell, Value},
    plonk::{ConstraintSystem, Advice, Column, Error, Expression, VirtualCells},
    poly::Rotation,
};
use halo2_proofs::arithmetic::FieldExt;
use std::collections::BTreeMap;
use std::fmt::Debug;
use std::hash::Hash;
use strum_macros::EnumIter;

#[derive(Clone, Debug, Default)]
pub(crate) struct Cell<F> {
    // expression for constraint
    expression: Option<Expression<F>>,
    column: Option<Column<Advice>>,
    // relative position to selector for synthesis
    rotation: usize,
    cell_column_index: usize,
}


impl<F: Field> Cell<F> {
    pub(crate) fn new(
        meta: &mut VirtualCells<F>,
        column: Column<Advice>,
        rotation: usize,
        cell_column_index: usize,
    ) -> Self {
        Self {
            expression: Some(meta.query_advice(column, Rotation(rotation as i32))),
            column: Some(column),
            rotation,
            cell_column_index,
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
                    self.column.unwrap(), self.rotation
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

// #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
// pub(crate) enum CellType {
//     StoragePhase1,
//     StoragePhase2,
//     StoragePermutation,
//     LookupByte,
//     Lookup(Table),
// }

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum CellType_<T: CustomTable> {
    StoragePhase1,
    StoragePhase2,
    StoragePermutation,
    LookupByte,
    Lookup(T),
}

pub trait CustomTable: Clone + Copy + Debug + PartialEq + Eq + PartialOrd + Ord + Hash{
    fn matches_to(&self, other: &Self) -> bool;
}

/// Example 
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, EnumIter)]
pub(crate) enum TestTable { 
    Fixed,
    Tx,
    Rw,
    Bytecode,
    Block,
    Copy,
    Keccak,
    Exp,
}

impl CustomTable for TestTable {
    fn matches_to(&self, other: &Self) -> bool {
        self == other
    }
}

fn works_like_this(table: TestTable, _config: &[(TestTable, usize)]) {
    if table.matches_to(&TestTable::Fixed) {
        println!("matched");
    }
}


impl<T: CustomTable> CellType_<T> {
    // The phase that given `Expression` becomes evaluateable.
    fn expr_phase<F: FieldExt>(expr: &Expression<F>) -> u8 {
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
    pub(crate) fn storage_for_phase<F: FieldExt>(phase: u8) -> CellType_<T> {
        match phase {
            0 => CellType_::StoragePhase1,
            1 => CellType_::StoragePhase2,
            _ => unreachable!(),
        }
    }

    /// Return the storage cell of the expression
    pub(crate) fn storage_for_expr<F: FieldExt>(expr: &Expression<F>) -> CellType_<T> {
        Self::storage_for_phase::<F>(Self::expr_phase::<F>(expr))
    }
}

#[derive(Clone, Debug)]
pub(crate) struct CellColumn<F, T: CustomTable> {
    index: usize,
    cell_type: CellType_<T>,
    height: usize,
    expr: Expression<F>,
}

impl<F: Field, T: Debug + CustomTable> Expr<F> for CellColumn<F, T> {
    fn expr(&self) -> Expression<F> {
        self.expr.clone()
    }
}

#[derive(Clone, Debug)]
pub struct CellManager<F, T: CustomTable> {
    // Thoughts (Cecilia): Integrate CellManager's function into Halo2's VirtualCell
    //                     They do the same things by saving queried Exressions
    //                     CM is just slightly smarter.
    //                     Make VC into trait, let CM impl VC.
    pub(crate) width: usize,
    pub(crate) height: usize,
    pub(crate) cells: Vec<Cell<F>>,
    // 对cell的抽象表示和对columns的抽象表示是分开的
    // Cell<F> 不用 T
    pub(crate) columns: Vec<CellColumn<F, T>>,
    pub(crate) phase_config: PhaseConfig<T>,
    pub(crate) copy_columns: usize,
}

#[derive(Clone, Debug)]
pub struct PhaseConfig<T> {
    phase3: Vec<(T, usize)>, //lookup
    phase2: usize, // rlc
    phase1: usize, // byte
}

impl<F: Field, T: CustomTable> CellManager<F, T> {
    pub(crate) fn new(
        meta: &mut ConstraintSystem<F>, // meta只出现一次，new的时候把所有cover的cells都query一遍
        height: usize,                  // 拿到 Expr 存起来，后面 cb.query_cell 直接给对应格子的 Expr
        advices: &[Column<Advice>],
        height_offset: usize,
        phase_config: PhaseConfig<T>,
        copy_columns: usize,
    ) -> Self {
        // Setup the columns and query the cells
        let width = advices.len();
        let mut cells = Vec::with_capacity(height * width);
        let mut columns = Vec::with_capacity(width);
        
        // 这个是meta.create_gate的替代
        // 主要是想 query 新的 column
        // 在会加一个0.expr()为constraint，因为里面调的create_gate要求
        query_expression(meta, |meta| {
            for c in 0..width {
                for r in 0..height {
                    cells.push(Cell::new(meta, advices[c], height_offset + r, c));
                }
                columns.push(CellColumn {
                    index: c,
                    cell_type: CellType_::StoragePhase1,
                    height: 0,
                    expr: cells[c * height].expr(),
                });
            }
        });

        let mut column_idx = 0;

        // Mark columns used for lookups in Phase3
        for (table, count) in &phase_config.phase3 {
            for _ in 0usize..*count {
                columns[column_idx].cell_type = CellType_::Lookup(table.clone());
                column_idx += 1;
            }
        }

        // Mark columns used for Phase2 constraints
        for _ in 0..phase_config.phase2 {
            columns[column_idx].cell_type = CellType_::StoragePhase2;
            column_idx += 1;
        }

        // Mark columns used for byte lookup
        for _ in 0..phase_config.phase1 {
            columns[column_idx].cell_type = CellType_::LookupByte;
            assert_eq!(advices[column_idx].column_type().phase(), 0);
            column_idx += 1;
        }

        // Mark columns used for copy constraints
        for _ in 0..copy_columns {
            meta.enable_equality(advices[column_idx]);
            columns[column_idx].cell_type = CellType_::StoragePermutation;
            column_idx += 1;
        }



        Self {
            width,
            height,
            cells,
            columns,
            phase_config,
            copy_columns,
        }
    }

    pub(crate) fn query_cells(&mut self, cell_type: CellType_<T>, count: usize) -> Vec<Cell<F>> {
        let mut cells = Vec::with_capacity(count);
        while cells.len() < count {
            let column_idx = self.next_column(cell_type);
            let column = &mut self.columns[column_idx];
            cells.push(self.cells[column_idx * self.height + column.height].clone());
            column.height += 1;
        }
        cells
    }

    pub(crate) fn query_cell(&mut self, cell_type: CellType_<T>) -> Cell<F> {
        self.query_cells(cell_type, 1)[0].clone()
    }

    pub(crate) fn reset(&mut self, height: usize) {
        assert!(height <= self.height);
        self.height = height;
        for column in self.columns.iter_mut() {
            column.height = 0;
        }
    }

    fn next_column(&self, cell_type: CellType_<T>) -> usize {
        let mut best_index: Option<usize> = None;
        let mut best_height = self.height;
        for column in self.columns.iter() {
            if column.cell_type == cell_type && column.height < best_height {
                best_index = Some(column.index);
                best_height = column.height;
            }
        }
        // Replace a CellType_::Storage by CellType_::StoragePermutation if the later has
        // better height
        if cell_type == CellType_::StoragePhase1 {
            for column in self.columns.iter() {
                if column.cell_type == CellType_::StoragePermutation && column.height < best_height {
                    best_index = Some(column.index);
                    best_height = column.height;
                }
            }
        }
        match best_index {
            Some(index) => index,
            // If we reach this case, it means that all the columns of cell_type have assignments
            // taking self.height rows, so there's no more space.
            None => panic!("not enough cells for query: {:?}", cell_type),
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
    pub(crate) fn get_stats(&self) -> BTreeMap<CellType_<T>, (usize, usize, usize)> {
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

    pub(crate) fn columns(&self) -> &[CellColumn<F, T>] {
        &self.columns
    }
}