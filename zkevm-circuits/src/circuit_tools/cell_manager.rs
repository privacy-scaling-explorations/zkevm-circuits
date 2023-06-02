//! Cell manager
use crate::evm_circuit::table::Table;
use crate::util::{Expr, query_expression};
use crate::circuit_tools::{table::LookupTable_, cached_region::{CachedRegion, ChallengeSet}};

use eth_types::Field;
use halo2_proofs::plonk::{Any, SecondPhase, ThirdPhase, FirstPhase, Phase};
use halo2_proofs::{
    circuit::{AssignedCell, Value},
    plonk::{ConstraintSystem, Advice, Column, Error, Expression, VirtualCells},
    poly::Rotation,
};
use halo2_proofs::arithmetic::FieldExt;
use std::cell;
use std::collections::{BTreeMap, HashMap};
use std::fmt::Debug;
use std::hash::Hash;
use strum_macros::EnumIter;

#[derive(Clone, Debug, Default)]
pub(crate) struct Cell<F> {
    // expression for constraint
    expression: Option<Expression<F>>,
    pub column: Option<Column<Advice>>,
    // relative position to selector for synthesis
    pub rotation: usize,
}


impl<F: Field> Cell<F> {
    pub(crate) fn new(
        meta: &mut VirtualCells<F>,
        column: Column<Advice>,
        rotation: usize,
    ) -> Self {
        Self {
            expression: Some(meta.query_advice(column, Rotation(rotation as i32))),
            column: Some(column),
            rotation,
        }
    }


    pub(crate) fn assign<S: ChallengeSet<F>>(
        &self,
        region: &mut CachedRegion<'_, '_, F, S>,
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

    pub(crate) fn assign_value<S: ChallengeSet<F>>(
        &self,
        region: &mut CachedRegion<'_, '_, F, S>,
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

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum EvmCellType {
    StoragePhase1,
    StoragePhase2,
    StoragePermutation,
    LookupByte,
    Lookup(Table),
}

impl Default for EvmCellType {
    fn default() -> Self {
        Self::StoragePhase1
    }
}

impl CellTypeTrait for EvmCellType {
    fn byte_type() -> Option<Self> {
        Some(EvmCellType::LookupByte)
    }

    fn storage_for_phase(phase: u8) -> Self {
        match phase {
            0 => EvmCellType::StoragePhase1,
            1 => EvmCellType::StoragePhase2,
            _ => unreachable!(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct CellConfig<C: CellTypeTrait> {
    pub cell_type: C,
    pub num_columns: usize,
    pub phase: u8,
    pub is_permute: bool,
}

impl<C: CellTypeTrait> From<(C, usize, u8, bool)> for CellConfig<C> {
    fn from((cell_type, num_columns, phase, is_permute): (C, usize, u8, bool)) -> Self {
        Self {
            cell_type,
            num_columns,
            phase,
            is_permute,
        }
    }
}

impl<C: CellTypeTrait> CellConfig<C> {
    pub fn init_columns<F: Field>(&self, meta: &mut ConstraintSystem<F>) -> Vec<Column<Advice>>{
        let mut columns = Vec::with_capacity(self.num_columns);
        for _ in 0..self.num_columns {
            let tmp = match self.phase {
                0 => meta.advice_column_in(FirstPhase),
                1 => meta.advice_column_in(SecondPhase),
                2 => meta.advice_column_in(ThirdPhase),
                _ => unreachable!(),
            };
            columns.push(tmp);
        }
        if self.is_permute {
            let _ = columns.iter().map(|c| meta.enable_equality(c.clone())).collect::<Vec<()>>();
        }
        columns
    }
}


pub trait CellTypeTrait: 
    Clone + Copy + Debug + PartialEq + Eq + PartialOrd + Ord + Hash + Default 
{
    fn byte_type() -> Option<Self>;

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
    fn storage_for_phase(phase: u8) -> Self;

    /// Return the storage cell of the expression
    fn storage_for_expr<F: FieldExt>(expr: &Expression<F>) -> Self {
        Self::storage_for_phase(Self::expr_phase::<F>(expr))
    }
}



/// this new cell manager has been in the planning for some time https://github.com/privacy-scaling-explorations/zkevm-circuits/issues/1203
/// Chiquito has a cell manager that is more abstracted out even: https://github.com/privacy-scaling-explorations/chiquito/blob/main/src/compiler/cell_manager.rs

#[derive(Clone, Debug)]
pub(crate) struct CellColumn_<F, C> {
    column: Column<Advice>,
    index: usize,
    pub(crate) cell_type: C,
    height: usize,
    pub(crate) expr: Expression<F>,
}


#[derive(Clone, Debug)]
pub struct CellManager_<F, C: CellTypeTrait> {
    // cell_type -> (start_width, cell_list)
    cells: HashMap<C, (usize, Vec<Cell<F>>)>,
    cell_configs: Vec<CellConfig<C>>,
    columns: Vec<CellColumn_<F, C>>,
    offset: usize,
    max_height: usize,
    total_width: usize,
    cell_history: Vec<Cell<F>>,
}

impl<F: Field, C: CellTypeTrait> CellManager_<F, C> {
    
    pub(crate) fn new(
        meta: &mut ConstraintSystem<F>,
        cell_configs: Vec<(C, usize, u8, bool)>,
        tables: Vec<&dyn LookupTable_<F, TableCellType = C>>,
        offset: usize,
        max_height: usize,
    ) -> Self {

        let mut cells = HashMap::new();
        let mut cell_columns = Vec::new();
        let mut total_width = 0;

        let mut cell_configs = cell_configs.into_iter().map(|c| c.into()).collect::<Vec<_>>();

        // User need to put fixed columns after advice if have any
        // permutation is not enable by default
        for table in tables {
            cell_configs.push(CellConfig {
                cell_type: table.get_type_().into(),
                num_columns: table.columns().len(),
                phase: table.phase(),
                is_permute: false,
            });
        };

        //println!("\nInitiating cm:");
        cell_configs
            .iter()
            .for_each(|c| {
                let cols = c.init_columns(meta);
                let mut cell_list = Vec::with_capacity(cols.len() * max_height);
                query_expression(meta, |meta| {
                    //println!("cols.len() init {} * {}", cols.len(), max_height);
                    for w in 0..cols.len() {
                        for h in 0..max_height {
                            let cell: Cell<_> = Cell::new(meta, cols[w], offset + h);
                            cell_list.push(cell);
                        }
                        cell_columns.push(CellColumn_ {
                            column: cols[w],
                            index: w,
                            cell_type: c.cell_type,
                            height: 0,
                            expr: cell_list[cell_list.len()-1].expr().clone(),
                        });
                    }
                });
                cells.insert(c.cell_type, (total_width, cell_list.clone()));
                //println!("cell type {:?} start with {} for window {}, cell_list {}", c.cell_type, total_width, c.num_columns, cell_list.len());
                total_width += cols.len();
            });

        Self {
            cells,
            cell_configs,
            columns: cell_columns,
            offset,
            max_height,
            total_width,
            cell_history: Vec::new(),
        }
    }

    pub(crate) fn get_columns(&self) -> Vec<Column<Advice>> {
        self.columns
            .iter()
            .map(|c| c.column.clone())
            .collect()
    }

    pub(crate) fn cell_columns(&self) -> &Vec<CellColumn_<F, C>> {
        &self.columns
    }

    pub(crate) fn get_width(&self) -> usize {
        self.total_width
    }

    pub(crate) fn get_max_height(&self) -> usize {
        self.max_height
    }

    pub(crate) fn get_offset(&self) -> usize {
        self.offset
    }

    pub(crate) fn set_max_height(&mut self, meta: &mut VirtualCells<F>, max_height: usize) {
        let mut new_cells = HashMap::new();
        self.cells
            .iter()
            .for_each(|(cell_type, (start_width, cells))| {
                let window = self.get_config(*cell_type).num_columns;
                let mut tmp = Vec::with_capacity(window * max_height);
                for w in 0..window {
                    if max_height < self.max_height {
                        //println!("\n-- set_max_height: {} -> {}", self.max_height, max_height);
                        tmp.extend_from_slice(&cells[w * self.max_height..w * self.max_height + max_height]);
                    } else {
                        //println!("\n++ set_max_height: {} -> {}", self.max_height, max_height);
                        tmp.extend_from_slice(&cells[w * self.max_height..w * self.max_height + self.max_height]);
                        //print!("    tmp.len() {} -> ", tmp.len());
                        let col = tmp.last().unwrap().column();
                        tmp.extend(
                                (self.max_height..max_height)
                                .map(|h| Cell::new(meta, col, self.offset + h))
                            );
                        //print!("{} ", tmp.len());
                    }
                }
                //println!("added cells for {:?} to {}", cell_type, tmp.len());
                new_cells.insert(*cell_type, (*start_width, tmp));
            });
            self.cells = new_cells;
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
        // let (start_width, _) = self.cells.get(&cell_type).expect("Cell type not found");
        // let window = self.get_config(cell_type).num_columns;
        // self.columns[*start_width..*start_width + window].to_owned()

        if let Some((start_width, _)) = self.cells.get(&cell_type) {
            let window = self.get_config(cell_type).num_columns;
            return self.columns[*start_width..*start_width + window].to_owned();
        } else {
            return Vec::new();
        }
    }

    /// Clears columns record and set new height in cells array
    /// query new cells if needed
    pub(crate) fn reset(&mut self, meta: &mut VirtualCells<F>, new_height: usize) {
        self.columns.iter_mut().for_each(|c| c.height = 0);
        self.set_max_height(meta, new_height);
        self.cell_history.clear();
    }

    pub(crate) fn query_cells(&mut self, cell_type: C, count: usize) -> Vec<Cell<F>> {
        let mut targets = Vec::with_capacity(count);
        let (start_width, cell_list) = self.cells
            .get(&cell_type)
            .expect(&format!("Cell type {:?} not found", cell_type));
        let window = self.get_config(cell_type).num_columns;        

        while targets.len() < count {
            // Search best cell in window of columns designated for this CellType
            let (index, height) = self.next_column(cell_type, &self.columns[*start_width..start_width + window]);
            targets.push(cell_list[index * self.max_height + height].clone());
            //// println!("at ({} * {} + {})", index, self.max_height, height);
            self.columns[start_width + index].height += 1;
        }
        for target in targets.iter() {
            for history in self.cell_history.iter() {
                if history.column().index() == target.column().index() && history.rotation() == target.rotation() {
                    unreachable!("test");
                }
            }
            self.cell_history.push(target.clone());
        }
        targets
    }

    pub(crate) fn query_cell(&mut self, cell_type: C) -> Cell<F> {
        self.query_cells(cell_type, 1)[0].clone()
    }

    fn next_column(&self, cell_type: C, columns: &[CellColumn_<F, C>]) -> (usize, usize) {
        let mut best_pos: Option<(usize, usize)> = None;
        let mut best_height = self.max_height;
        for column in columns.iter() {
            assert!(column.cell_type == cell_type);
            if column.height < best_height {
                best_pos = Some((column.index, column.height));
                best_height = column.height;
            }
        }
        //println!("best pos: {:?}", best_pos);
        match best_pos {
            Some(pos) => pos,
            // If we reach this case, it means that all the columns of cell_type have assignments
            // taking self.height rows, so there's no more space.
            None => panic!("not enough cells for query: {:?}", cell_type),
        }
    }
}

