use std::marker::PhantomData;
use std::rc::Rc;
use std::vec;

use crate::circuit_tools::cached_region::{self, ChallengeSet};
use crate::circuit_tools::cell_manager::{Cell, CellManager, PhaseConfig, SingleTable, TableType, EvmCellType};
use crate::circuit_tools::constraint_builder::ConstraintBuilder;
use crate::circuit_tools::memory::Memory;
use crate::util::{Expr, query_expression};
use crate::circuit_tools::{table::LookupTable, cached_region::CachedRegion};

use eth_types::Field;
use gadgets::util::Scalar;
use halo2_proofs::circuit::layouter::RegionColumn;
use halo2_proofs::circuit::{SimpleFloorPlanner, layouter, Layouter, Region};
use halo2_proofs::dev::MockProver;
use halo2_proofs::halo2curves::bn256::Fr;
use halo2_proofs::plonk::{Any, Circuit, FirstPhase, Challenge, SecondPhase, ThirdPhase, Fixed, Selector};
use halo2_proofs::{
    circuit::{AssignedCell, Value},
    plonk::{ConstraintSystem, Advice, Column, Error, Expression, VirtualCells},
    poly::Rotation,
};




#[derive(Clone)]
pub struct TestConfig<F> {
    pub q_usable: Selector,
    pub a: Column<Advice>,
    pub b: Column<Advice>,
    pub c: Column<Advice>,
    pub d: Column<Advice>,
    pub e: Column<Advice>,
    _phantom: PhantomData<F>
}


impl<F: Field> TestConfig<F> {
    pub fn new(
        meta: &mut ConstraintSystem<F>, 
        // r1: Challenge
    ) -> Self {
        
        // Get columns
        let q_usable = meta.selector();
        let a = meta.advice_column();
        let b = meta.advice_column();
        let c = meta.advice_column();
        let d = meta.advice_column();
        let e = meta.advice_column();

        meta.create_gate("Test Gate", |meta: &mut VirtualCells<F>| {
            
            let mut exprs = Vec::new();
            let q = meta.query_selector(q_usable);

            let a1 = meta.query_advice(a, Rotation(0));
            let b1 = meta.query_advice(b, Rotation(0));
            let c1 = meta.query_advice(c, Rotation(0));
            exprs.push((a1*b1 - c1) * q.clone());
            
            let b2 = meta.query_advice(b, Rotation(1));
            let c2 = meta.query_advice(c, Rotation(1));
            let d2 = meta.query_advice(d, Rotation(1));
            exprs.push((b2*c2 - d2) * q.clone());
            
            let c3 = meta.query_advice(c, Rotation(2));
            let d3 = meta.query_advice(d, Rotation(2));
            let e3 = meta.query_advice(e, Rotation(2));
            exprs.push((c3*d3 - e3) * q.clone());

            exprs
        });

        Self {
            q_usable,
            a, b, c, d, e,
            _phantom: PhantomData
        }
    }

    pub fn assign(
        &self, 
        layouter: &mut impl Layouter<F>,
        // r1: Value<F>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "Test Region",
            |mut region| {
                self.q_usable.enable(&mut region, "q_usable_0", 0);
                
                region.name_column(|| "a", self.a);
                region.name_column(|| "b", self.b);
                region.name_column(|| "c", self.c);
                region.name_column(|| "d", self.d);
                region.name_column(|| "e", self.e);



                assign!(region, (self.a, 0) => 2.scalar())?;
                assign!(region, (self.b, 0) => 3.scalar())?;
                assign!(region, (self.c, 0) => 6.scalar())?;

                assign!(region, (self.b, 1) => 4.scalar())?;
                assign!(region, (self.c, 1) => 5.scalar())?;
                assign!(region, (self.d, 1) => 20.scalar())?;

                assign!(region, (self.c, 2) => 7.scalar())?;
                assign!(region, (self.d, 2) => 8.scalar())?;
                assign!(region, (self.e, 2) => 56.scalar())?;

                Ok(())
            },
        )
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
    type Config = TestConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;


    fn without_witnesses(&self) -> Self {
        unimplemented!()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let _dummy_phase1 = meta.advice_column();
        let r1 = meta.challenge_usable_after(FirstPhase);
        
        let config = TestConfig::new(meta);
        config
    }

    fn synthesize(
        &self, 
        config: Self::Config, 
        mut layouter: impl halo2_proofs::circuit::Layouter<F>
    ) -> Result<(), Error> {
        // let r1 = layouter.get_challenge(r1);
        config.assign(&mut layouter)
    }
}

#[test]
fn test() {
    let circuit = TestCircuit::<Fr>::default();
    let prover = MockProver::<Fr>::run(5, &circuit, vec![]).unwrap();
    prover.assert_satisfied_par();

}

#[cfg(feature = "dev-graph")]
#[test]
fn test_graph() {
    use plotters::prelude::*;

    let circuit = TestCircuit::<Fr>::default();

    println!("Start graphing");

    let root = BitMapBackend::new("test.png", (512, 1024)).into_drawing_area();
    root.fill(&WHITE).unwrap();
    let root = root.titled("Test Chip Layout", ("sans-serif", 60)).unwrap();

    halo2_proofs::dev::CircuitLayout::default()
        .show_labels(true)
        .show_equality_constraints(true)
        .render(4, &circuit, &root)
        .unwrap();

    // Generate the DOT graph string.
    let dot_string = halo2_proofs::dev::circuit_dot_graph(&circuit);
    print!("{}", dot_string);


}
