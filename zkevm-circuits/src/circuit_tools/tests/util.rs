use std::rc::Rc;
use std::vec;

use crate::circuit_tools::cached_region::{self, ChallengeSet};
use crate::circuit_tools::cell_manager::{Cell, CellManager_, CellTypeTrait};
use crate::circuit_tools::constraint_builder::ConstraintBuilder;
use crate::circuit_tools::memory::Memory;
use crate::util::{Expr, query_expression};
use crate::circuit_tools::{table::LookupTable_, cached_region::{CachedRegion, MacroDescr}};

use eth_types::Field;
use gadgets::util::Scalar;
use halo2_proofs::circuit::{SimpleFloorPlanner, layouter, Layouter, Region};
use halo2_proofs::dev::MockProver;
use halo2_proofs::halo2curves::bn256::Fr;
use halo2_proofs::plonk::{Any, Circuit, FirstPhase, Challenge, SecondPhase, ThirdPhase, Fixed, Selector};
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
const COPY_COL_NUM: usize = 1;
const REGION_HEIGHT: usize = 10;

#[derive(Clone)]
pub struct TestTable {
    pub a: Column<Fixed>,
    pub b: Column<Fixed>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CellType {
    LookupTestTable,
    PhaseOne,
    PhaseTwo
}

impl Default for CellType {
    fn default() -> Self {
        CellType::PhaseOne
    }
}

impl CellTypeTrait for CellType {
    fn byte_type() -> Option<Self> {
        Some(CellType::PhaseOne)
    }

    fn storage_for_phase(phase: u8) -> Self {
        match phase {
            0 => CellType::PhaseOne,
            1 => CellType::PhaseTwo,
            _ => unreachable!(),
        }
    }
}

impl<F: Field> LookupTable_<F> for TestTable {
    type TableCellType = CellType;

    fn get_type_(&self) -> CellType {
        CellType::LookupTestTable
    }

    fn phase(&self) -> u8 {
        1
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
    pub(crate) sel: Selector,
    pub(crate) q_enable: Column<Fixed>,
    pub(crate) q_count: Column<Advice>,
    pub(crate) cell_columns: Vec<Column<Advice>>,
    pub(crate) cell_gadget: CellGadget<F>,
    pub(crate) table: TestTable,
}


impl<F: Field> TestConfig<F> {
    pub fn new(
        meta: &mut ConstraintSystem<F>, 
        table: TestTable, 
        r1: Challenge
    ) -> Self {
        
        // Get columns
        let sel = meta.selector();
        let q_enable = meta.fixed_column();
        let q_count = meta.advice_column();
        let cell_columns = (0..10)
            .map(|i| 
                match i {
                    0..=2 => meta.advice_column_in(FirstPhase),
                    3..=5 => meta.advice_column_in(SecondPhase),
                    6..=9 => meta.advice_column_in(ThirdPhase),
                    10 => meta.advice_column_in(FirstPhase), // Copy
                    _ => unreachable!(),
                }
            ).collect::<Vec<_>>();

        // Init cell manager and constraint builder
        let mut cm = CellManager_::new(
            meta,
            vec![
                (CellType::PhaseOne, 3, 0, false),
                (CellType::PhaseTwo, 3, 0, false),
                (CellType::LookupTestTable, 3, 0, false),
            ],
            vec![&table],
            0,
            10
        );
        let mut cb: ConstraintBuilder<F, CellType> = ConstraintBuilder::new(MAX_DEG, Some(cm));

        let mut cell_gadget = CellGadget::default();
        meta.create_gate("Test Gate", |meta| {
            // Config row counts
            circuit!([meta, cb], {
                // All configuration of inner gadgets must be wrapped in ifx!
                // it pushes a condition into cb, which is gonna be multiplied with the upcoming constraints.
                // then if you turn off q_enable, your inner gadgets will be disabled.
                // otherwise you'll see missing selector error.
                ifx!(f!(q_enable) => {
                    require!(a!(q_count, 1) => a!(q_count) + 1.expr());
                    // Init Gadgets
                    cell_gadget = CellGadget::configure(
                        &mut cb, 
                        // Convert Challenge into Expression<F>
                        meta.query_challenge(r1),
                    );
                })
            });
            cb.build_constraints()
        });

        Self {
            sel,
            q_enable,
            q_count,
            cell_columns,
            cell_gadget,
            table,
        }
    }

    pub fn assign(
        &self, 
        layouter: &mut impl Layouter<F>,
        r1: Value<F>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "cell gadget",
            |mut region| {

                self.sel.enable(&mut region, 0);
                
                for offset in 0..20 {
                    assignf!(region, (self.q_enable, offset) => 1.scalar())?;
                    assign!(region, (self.q_count, offset) => offset.scalar())?;
                }
                assign!(region, (self.q_count, 20) => 20.scalar())?;

                // Value of challenge is obtained from layouter.
                // We query it once during synthesis and
                // make it accessable across Config through CachedRegion. 
                let challenges = [r1];
                let mut cached_region = cached_region::CachedRegion::new(&mut region, &challenges);
                self.cell_gadget.assign(&mut cached_region, 0)
            },
        )
    }

    fn load_fixed_table(
        &self,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        // We can use different region for lookup tables,
        // since they are not related to cell gadgets.
        layouter.assign_region(
            || "fixed table",
            |mut region| {
                for offset in 0..10 {
                    // Don't need CachedRegion here since we don't cache intermediate values.
                    assignf!(region, (self.table.a, offset) => offset.scalar())?;
                    assignf!(region, (self.table.b, offset) => (offset + 1).scalar())?;
                }
                Ok(())
            },
        )
    }


}

#[derive(Clone, Debug, Default)]
pub struct CellGadget<F> {
    // (a, b) in lookup
    // a, r1 * b == c
    //  where r1 is phase1 challenge
    // a == d
    a: Cell<F>,
    b: Cell<F>,
    c: Cell<F>,
    d: Cell<F>,
}


impl<F: Field> CellGadget<F> {
    pub fn configure(cb: &mut ConstraintBuilder<F, CellType>, r1: Expression<F>) -> Self {
        let a = cb.query_default();
        let b = cb.query_default();
        // c depends on Phase1 Challenge r1
        let c = cb.query_one(CellType::PhaseTwo);
        let d = cb.query_default();        
        circuit!([meta, cb], {
            //require!((a, b) => @format!("test_lookup"));
            require!(c => a.expr() + b.expr() * r1);
            require!(a => d.expr());
        });

        CellGadget { a, b, c, d }
    }

    pub fn assign<S: ChallengeSet<F>>(
        &self, 
        region: &mut CachedRegion<'_, '_, F, S>, 
        offset: usize, 
    ) -> Result<(), Error>{

        // All challenges are returned as defined struct or Vec<&Value<F>>,
        // we map them to Vec<F> for calculations.
        let mut r = F::one();
        region.challenges().indexed()[0].map(|r_val| r = r_val);

        // Assign values to cells
        self.a.assign(region, offset, 2u64.scalar())?;
        self.b.assign(region, offset, 3u64.scalar())?;
        self.c.assign(
            region, 
            offset,
            F::from(2u64) + F::from(3u64) * r
        )?;
        self.d.assign(region, offset, 2u64.scalar())?;
        Ok(())
    }
}

#[derive(Clone, Debug, Default)]
struct TestCircuit<F> {
    // Don't need anything in this struct,
    // since we don't have precomputed data from outside
    // and Config & Challenges are passed to synthesize.
    _phantom: F,
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
            a: meta.fixed_column(),
            b: meta.fixed_column(),
        };
        let _dummy_phase1 = meta.advice_column_in(FirstPhase);
        let r1 = meta.challenge_usable_after(FirstPhase);
        
        let config = TestConfig::new(meta, table, r1);
        (config, r1)
    }

    fn synthesize(
        &self, 
        (config, r1): Self::Config, 
        mut layouter: impl halo2_proofs::circuit::Layouter<F>
    ) -> Result<(), Error> {
        let r1 = layouter.get_challenge(r1);
        config.load_fixed_table(&mut layouter)?;
        config.assign(&mut layouter, r1)
    }
}

#[cfg(feature = "dev-graph")]
#[test]
fn test() {
    let circuit = TestCircuit::<Fr>::default();
    let prover = MockProver::<Fr>::run(6, &circuit, vec![]).unwrap();
    prover.assert_satisfied_par();

    use plotters::prelude::*;
    let root = BitMapBackend::new("test.png", (1024, 768)).into_drawing_area();
    root.fill(&WHITE).unwrap();
    let root = root
        .titled("Test Layout", ("sans-serif", 60))
        .unwrap();

    halo2_proofs::dev::CircuitLayout::default()
        // Render the circuit onto your area!
        // The first argument is the size parameter for the circuit.
        .show_cell_annotations(true)
        .region_by_name("cell gadget")
        .render(6, &circuit.clone(), &root)
        .unwrap();

}