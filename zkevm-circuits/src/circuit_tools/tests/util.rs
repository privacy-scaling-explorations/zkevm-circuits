use std::rc::Rc;
use std::vec;

use crate::circuit_tools::cached_region::{self, ChallengeSet};
use crate::circuit_tools::cell_manager::{Cell, CellManager, PhaseConfig, SingleTable, TableType};
use crate::circuit_tools::constraint_builder::ConstraintBuilder;
use crate::circuit_tools::memory::Memory;
use crate::util::{Expr, query_expression};
use crate::circuit_tools::{table::LookupTable, cached_region::CachedRegion};

use eth_types::Field;
use gadgets::util::Scalar;
use halo2_proofs::circuit::{SimpleFloorPlanner, layouter, Layouter, Region};
use halo2_proofs::plonk::{Any, Circuit, FirstPhase, Challenge, SecondPhase, ThirdPhase};
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

#[derive(Clone)]
pub struct TestConfig<F> {
    pub(crate) q_count: Column<Advice>,
    pub(crate) cell_columns: Vec<Column<Advice>>,
    pub(crate) cell_gadget: CellGadget<F>,
}


impl<F: Field> TestConfig<F> {
    pub fn new(
        meta: &mut ConstraintSystem<F>, 
        table: TestTable, 
        r1: Challenge
    ) -> Self {
        
        // Get columns
        let q_count = meta.advice_column_in(FirstPhase);
        let cell_columns: Vec<Column<Advice>> = (0..2).map(|_| meta.advice_column_in(ThirdPhase))
            .chain((3..5).map(|_| meta.advice_column_in(SecondPhase)))
            .chain((6..9).map(|_| meta.advice_column()))
            .collect();

        // Init cell manager and constraint builder
        let phase_config: PhaseConfig<SingleTable> = PhaseConfig::new::<F>(vec![&table], 2, 3);
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
        let cell_gadget = CellGadget::configure(
            &mut cb, 
            // Convert Challenge into Expression<F>
            query_expression(meta, |meta| meta.query_challenge(r1))
        );
        Self {
            q_count,
            cell_columns,
            cell_gadget,
        }
    }

    pub fn assign(
        &self, 
        layouter: &mut impl Layouter<F>,
        r1: Value<F>,
    ) -> Result<(), Error> {
        // layouter.assign_region(
        //     || "cell gadget",
        //     |mut region| {
        //         let cached_region = cached_region::CachedRegion::new(&mut region);
        //         self.cell_gadget.assign(&mut region, 0, r1)
        //     },
        // )
        unimplemented!()
    }

}

#[derive(Clone, Debug, Default)]
pub struct CellGadget<F> {
    // a + r1 * b == c
    //  where r1 is phase1 challenge
    // a == d
    a: Cell<F>,
    b: Cell<F>,
    c: Cell<F>,
    d: Cell<F>,
}


impl<F: Field> CellGadget<F> {
    pub fn configure(cb: &mut ConstraintBuilder<F, SingleTable>, r1: Expression<F>) -> Self {
        let a = cb.query_cell();
        let b = cb.query_cell();
        let c = cb.query_byte();
        let d = cb.query_cell();        
        circuit!([meta, cb], {
            require!((a, b) => @format!("test_lookup"));
            require!(c => a.expr() + b.expr() * r1);
            require!(a => d.expr());
        });
        CellGadget { a, b, c, d }
    }

    pub fn assign<C: ChallengeSet<F>>(
        &self, 
        region: &mut CachedRegion<'_, '_, F, C>, 
        offset: usize, 
        r1: Value<F>
    ) -> Result<(), Error>{

        self.a.assign(region, offset, 2u64.scalar())?;
        self.b.assign(region, offset, 3u64.scalar())?;

        self.c.assign(
            region, 
            offset,
             Value::known(2u64.scalar()) + Value::known(2u64.scalar()) * r1.scalar()
            )?;

        assign!(region, (self.a.column(), offset) => 2u64.scalar())?;
        assign!(region, (self.b.column(), offset) => 3u64.scalar())?;
        assign!(region, (self.c.column(), offset) => 2u64.scalar() + 3u64.scalar() * r1)?;
        assign!(region, (self.d.column(), offset) => 2u64.scalar())?;

        region.get_advice(1, 1, Rotation::cur());
        Ok(())
    }
    
}


struct TestCircuit<F> {
    config: TestConfig<F>,
}

impl<F: Field> Circuit<F> for TestCircuit<F> {
    type Config = (TestConfig<F>, Challenge);
    type FloorPlanner = SimpleFloorPlanner;


    fn without_witnesses(&self) -> Self {
        unimplemented!()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {

        // Build the table and challenge outside
        // since zkevm use them accross circuits
        let table = TestTable {
            a: meta.advice_column(),
            b: meta.advice_column(),
        };
        let r1 = meta.challenge_usable_after(FirstPhase);
        
        let config = TestConfig::new(meta, table, r1);
        (Self { config }, r1)
    }

    fn synthesize(
        &self, 
        (config, r1): Self::Config, 
        layouter: impl halo2_proofs::circuit::Layouter<F>
    ) -> Result<(), Error> {
        let r1 = layouter.get_challenge(r1);
        config.assign(&mut layouter, r1)
    }
}

#[test]
fn test() {
    
}