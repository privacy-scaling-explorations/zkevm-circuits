//! Cell manager
use crate::util::{Expr, query_expression};
use crate::circuit_tools::{table::LookupTable, cached_region::{CachedRegion, ChallengeSet}};

use eth_types::Field;
use halo2_proofs::plonk::{Any, SecondPhase, ThirdPhase, FirstPhase};
use halo2_proofs::{
    circuit::{AssignedCell, Value},
    plonk::{ConstraintSystem, Advice, Column, Error, Expression, VirtualCells},
    poly::Rotation,
};
use halo2_proofs::arithmetic::FieldExt;
use std::collections::{BTreeMap, HashMap};
use std::fmt::Debug;
use std::hash::Hash;
use strum_macros::EnumIter;

use super::table::LookupTable_;

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


    pub(crate) fn assign<C: ChallengeSet<F>>(
        &self,
        region: &mut CachedRegion<'_, '_, F, C>,
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

    pub(crate) fn assign_value<C: ChallengeSet<F>>(
        &self,
        region: &mut CachedRegion<'_, '_, F, C>,
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

#[derive(Clone, Debug)]
pub struct CellConfig<C: CellTypeTrait> {
    cell_type: C,
    num_columns: usize,
    phase: u8,
    is_permute: bool,
}

impl<C: CellTypeTrait> CellConfig<C> {
    pub fn init_columns<F: Field>(&self, meta: &mut ConstraintSystem<F>) -> Vec<Column<Advice>>{
        let mut columns = Vec::with_capacity(self.num_columns);
        match self.phase {
            0 => columns.iter_mut()
                    .map(|c| *c = meta.advice_column_in(FirstPhase))
                    .collect::<Vec<()>>(),
            1 => columns.iter_mut()
                    .map(|c| *c = meta.advice_column_in(SecondPhase))
                    .collect::<Vec<()>>(),
            2 => columns.iter_mut()
                    .map(|c| *c = meta.advice_column_in(ThirdPhase))
                    .collect::<Vec<()>>(),
            _ => unreachable!(),
        };
        if self.is_permute {
            columns.iter().map(|c| meta.enable_equality(c.clone()));
        }
        columns
    }
}


pub trait CellTypeTrait: 
    Clone + Copy + Debug + PartialEq + Eq + PartialOrd + Ord + Hash {}


#[derive(Clone, Debug)]
pub(crate) struct CellColumn_<F, C> {
    index: usize,
    cell_type: C,
    height: usize,
    expr: Expression<F>,
}


#[derive(Clone, Debug)]
pub struct CellManager_<F, C: CellTypeTrait> {
    max_height: usize,
    total_width: usize,
    cells: HashMap<C, (usize, Vec<Cell<F>>)>,
    cell_configs: Vec<CellConfig<C>>,
    columns: Vec<CellColumn_<F, C>>,
}

impl<F: Field, C: CellTypeTrait> CellManager_<F, C> {
    
    // 一步到位
    pub(crate) fn new<T: TableType + Into<C>>(
        meta: &mut ConstraintSystem<F>,
        mut cell_configs: Vec<CellConfig<C>>,
        tables: Vec<&dyn LookupTable_<F, TableType_ = T>>,
        offset: usize,
        max_height: usize,
    ) -> Self {

        let mut cells = HashMap::new();
        let mut cell_columns = Vec::new();
        let mut total_width = 0;

        // User need to put fixed columns after advice if have any
        // permutation is not enable by default
        for table in tables {
            if !table.advice_columns().is_empty() {
                cell_configs.push(CellConfig {
                    cell_type: table.get_type_().into(),
                    num_columns: table.advice_columns().len(),
                    phase: table.phase(),
                    is_permute: false,
                });
            }
            if !table.fixed_columns().is_empty() {
                cell_configs.push(CellConfig {
                    cell_type: table.get_type_().into(),
                    num_columns: table.fixed_columns().len(),
                    phase: table.phase(),
                    is_permute: false,
                });
            }
        };

        cell_configs
            .iter()
            .map(|c| {
                let cols = c.init_columns(meta);
                let mut cell_list = Vec::with_capacity(cols.len() * max_height);
                let start_width = total_width;
                query_expression(meta, |meta| {
                    for w in 0..cols.len() {
                        for h in 0..max_height {
                            let cell: Cell<_> = Cell::new(meta, cols[w], offset + h, total_width);
                            cell_list.push(cell);
                        }
                        cell_columns.push(CellColumn_ {
                            index: w,
                            cell_type: c.cell_type,
                            height: 0,
                            expr: cell_list[cols.len()-1].expr().clone(),
                        });
                        total_width += 1;
                    }
                });
                cells.insert(c.cell_type, (start_width, cell_list));
            }).collect::<Vec<()>>();

        Self {
            max_height,
            total_width,
            cells,
            cell_configs,
            columns: cell_columns,
        }
    }

    pub(crate) fn get_width(&self) -> usize {
        self.total_width
    }

    pub(crate) fn get_max_height(&self) -> usize {
        self.max_height
    }

    pub(crate) fn set_max_height(&mut self, max_height: usize) {
        self.max_height = max_height;
    }

    pub(crate) fn get_used_height(&self) -> usize {
        self.columns
            .iter()
            .map(|column| column.height)
            .max()
            .unwrap()
    }

    pub(crate) fn get_config(&self, cell_type: C) -> &CellConfig<C> {
        self.cell_configs
            .iter()
            .find(|c| c.cell_type == cell_type)
            .expect("Cell type not found")
    }

    pub(crate) fn get_typed_columns(&self, cell_type: C) -> Vec<CellColumn_<F, C>> {
        let (start_width, _) = self.cells.get(&cell_type).expect("Cell type not found");
        let window = self.get_config(cell_type).num_columns;
        self.columns[*start_width..window].to_owned()
    }

    pub(crate) fn query_cells(&mut self, cell_type: C, count: usize) -> Vec<Cell<F>> {
        let mut targets = Vec::with_capacity(count);
        let (start_width, cell_list) = self.cells.get(&cell_type).expect("Cell type not found");
        let window = self.get_config(cell_type).num_columns;

        while targets.len() < count {
            // Iterate the window of columns designated for this CellType
            // No need to find the best height because cells should be return in order
            self.columns[*start_width..start_width + window]
                .iter_mut()
                .enumerate()
                .map(|(i, c)| {
                    assert!(c.cell_type == cell_type);
                    if c.height < self.max_height { 
                        targets.push(cell_list[i + c.height].clone());
                        c.height += 1;
                    }
                }).collect::<Vec<()>>();
        }
        targets
    }

    pub(crate) fn query_cell(&mut self, cell_type: C) -> Cell<F> {
        self.query_cells(cell_type, 1)[0].clone()
    }
}



// ============================== Old Version =================================




#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum CellType_<T: TableType> {
    StoragePhase1,
    StoragePhase2,
    StoragePermutation,
    LookupByte,
    Lookup(T),
}

impl<T: TableType> Default for CellType_<T> {
    fn default() -> Self {
        CellType_::StoragePhase1
    }
}

pub trait TableType: Clone + Copy + Debug + PartialEq + Eq + PartialOrd + Ord + Hash {}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, EnumIter)]
pub enum SingleTable {
    Default,
}
impl TableType for SingleTable {}
/// Example

// use super::table::{TestTableType, MptTable, BytecodeTable};

// fn work_like_this<F: Field>(meta: &mut ConstraintSystem<F>) {
//     let config: PhaseConfig<TestTableType> = PhaseConfig::new(
//         &[MptTable::construct(meta), BytecodeTable::construct(meta)],
//         2,
//         3
//     );
// }


impl<T: TableType> CellType_<T> {
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
pub(crate) struct CellColumn<F, T: TableType> {
    index: usize,
    cell_type: CellType_<T>,
    height: usize,
    expr: Expression<F>,
}


impl<F: Field, T: Debug + TableType> Expr<F> for CellColumn<F, T> {
    fn expr(&self) -> Expression<F> {
        self.expr.clone()
    }
}
#[derive(Clone, Debug)]
pub struct CellManager<F, T: TableType> {
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
    phase1: usize,
    phase2: usize,
    phase3: Vec<(T, usize)>, //lookup
}

impl<T: TableType> PhaseConfig<T> {
    pub fn new<F: Field>(
        phase1: usize,
        phase2: usize, 
        tables: Vec<&dyn LookupTable<F, T>>
    ) -> Self {
        let phase3   = tables.iter().map(|t|
             (t.get_type(), t.columns().len())
            ).collect::<Vec<_>>();
        Self {
            phase1,
            phase2,
            phase3,
        }
    }
}

impl<F: Field, T: TableType> CellManager<F, T> {
    

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


        // Mark columns used for byte lookup
        for _ in 0..phase_config.phase1 {
            assert_eq!(advices[column_idx].column_type().phase(), 0);
            column_idx += 1;
        }
        
        // Mark columns used for Phase2 constraints
        for _ in 0..phase_config.phase2 {
            assert_eq!(advices[column_idx].column_type().phase(), 1u8);
            columns[column_idx].cell_type = CellType_::StoragePhase2;
            column_idx += 1;
        }

        // Mark columns used for lookups in Phase3
        for (table, count) in &phase_config.phase3 {
            for _ in 0usize..*count {
                assert_eq!(advices[column_idx].column_type().phase(), 2u8);
                columns[column_idx].cell_type = CellType_::Lookup(*table);
                column_idx += 1;
            }
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