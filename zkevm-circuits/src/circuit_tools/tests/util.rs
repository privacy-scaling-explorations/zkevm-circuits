use std::vec;

use crate::circuit_tools::cell_manager::{Cell, CellManager, PhaseConfig, SingleTable, TableType};
use crate::circuit_tools::constraint_builder::ConstraintBuilder;
use crate::circuit_tools::memory::Memory;
use crate::util::{Expr, query_expression};
use crate::circuit_tools::{table::LookupTable, cached_region::CachedRegion};

use eth_types::Field;
use gadgets::util::Scalar;
use halo2_proofs::plonk::Any;
use halo2_proofs::{
    circuit::{AssignedCell, Value},
    plonk::{ConstraintSystem, Advice, Column, Error, Expression, VirtualCells},
    poly::Rotation,
};



/// To Test:
///    1. Constrain advices with cells
///    2. Lookup (advices <--> advices) with cells (RAM)
///    3. Lookup (advices <--> fixed) with cells (ROM)
/// 

const MAX_DEG: usize = 5;
const CM_HEIGHT: usize = 10;
const COPY_COL_NUM: usize = 10;

pub struct TestTable {
    pub a: Column<Advice>,
    pub b: Column<Advice>,
}

impl<F: Field> LookupTable<F, SingleTable> for TestTable {
    fn get_type(&self) -> SingleTable {
        SingleTable::Default
    }
    fn columns(&self) -> Vec<Column<Any>> {
        vec![self.a.into(), self.b.into()]
    }
    fn annotations(&self) -> Vec<String> {
        vec![String::from("a"), String::from("b")]
    }
}

pub struct TestConfig<F> {
    pub(crate) q_count: Column<Advice>,
    pub(crate) cell_columns: Vec<Column<Advice>>,
    pub(crate) cell_gadget: CellGadget<F>,
}


impl<F: Field> TestConfig<F> {
    pub fn new(meta: &mut ConstraintSystem<F>, table: TestTable) -> Self {
        
        // Get columns
        let q_count = meta.advice_column();
        let cell_columns = (0..10).map(|_| meta.advice_column()).collect::<Vec<_>>();

        // Init cell manager and constraint builder
        let phase_config: PhaseConfig<SingleTable> = PhaseConfig::new::<F>(vec![&table], 1, 1);
        let mut cm = CellManager::new(
            meta, 
            CM_HEIGHT,
            &cell_columns,
            0,
            phase_config,
            COPY_COL_NUM 
        );
        let mut cb = ConstraintBuilder::new(MAX_DEG, Some(cm));
        
        // Init Gadgets
        let cell_gadget = CellGadget::configure(&mut cb);
        Self {
            q_count,
            cell_columns,
            cell_gadget,
        }
    }

}

#[derive(Clone, Debug, Default)]
pub struct CellGadget<F> {
    // a + b == c
    // a == d
    a: Cell<F>,
    b: Cell<F>,
    c: Cell<F>,
    d: Cell<F>,
}

impl<F: Field> CellGadget<F> {
    pub fn configure(cb: &mut ConstraintBuilder<F, SingleTable>) -> Self {
        let a = cb.query_cell();
        let b = cb.query_cell();
        let c = cb.query_cell();
        let d = cb.query_cell();        
        circuit!([meta, cb], {
            require!((a, b) => @format!("test_lookup"));
            require!(c => a.expr() + b.expr());
            require!(a => d.expr());
        });
        CellGadget { a, b, c, d }
    }

    pub fn assign(&self, region: &mut CachedRegion<'_, '_, F>, offset: usize) -> Result<(), Error>{
        assign!(region, (self.a.column(), offset) => 2u64.scalar())?;
        assign!(region, (self.b.column(), offset) => 3u64.scalar())?;
        assign!(region, (self.c.column(), offset) => 5u64.scalar())?;
        assign!(region, (self.d.column(), offset) => 2u64.scalar())?;
        Ok(())
    }
    
}



#[test]
fn test() {
    
}