use std::{marker::PhantomData};

use eth_types::Field;
use gadgets::util::Scalar;
use halo2_proofs::{
    plonk::{Circuit, ConstraintSystem, Advice, Fixed, Column, FirstPhase, Challenge, Error, SecondPhase}, 
    circuit::{SimpleFloorPlanner, Layouter, layouter, Value},
    poly::Rotation,
};

use crate::circuit_tools::{constraint_builder:: ConstraintBuilder, cell_manager::CellType};

#[derive(Clone)]
pub struct TestConfig {
    pub(crate) q_enable: Column<Fixed>,
    pub(crate) a: Column<Advice>,
    pub(crate) b: Column<Advice>,
    pub(crate) c: Column<Fixed>,
    pub(crate) res: Column<Advice>,
}

#[derive(Clone, Copy, Debug, num_enum::Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u8)]
pub enum TestCellType {
    #[num_enum(default)]
    Storage,
}
impl CellType for TestCellType{
    fn byte_type() -> Option<Self> {
        unimplemented!()
    }
    fn storage_for_phase(phase: u8) -> Self {
        unimplemented!()
    }
}


impl TestConfig {
    pub fn new<F: Field>(meta: &mut ConstraintSystem<F>, r: Challenge) -> Self {
        let q_enable = meta.fixed_column();
        let a = meta.advice_column();
        let b = meta.advice_column_in(SecondPhase);
        let c = meta.fixed_column();
        let res = meta.advice_column();
        

        let mut cb: ConstraintBuilder<F, TestCellType> =  ConstraintBuilder::new(4,  None, None);

        meta.create_gate("Test", |meta| {
            circuit!([meta, cb], {
                // Fixed column with ifx! equivalents to selector
                // BUT Advice does not
                ifx!(f!(q_enable) => {
                    ifx!(a!(a) => {
                        require!(a!(res) => a!(b) + f!(c)); 
                    } elsex {
                        require!(a!(res) => a!(b) + c!(r)); 
                        
                    });
                    // Matchx! adds the same set of constraints as ifx!
                    matchx!(
                        a!(a) => {
                            require!(a!(res) => a!(b) + f!(c)); 
                        },
                        not!(a!(a)) => {
                            require!(a!(res) => a!(b) + c!(r)); 
                            
                        },
                        _ => unreachablex!(),
                    );
                })
            });
            cb.build_constraints()
        });
        TestConfig { 
            q_enable,
            a, 
            b, 
            c, 
            res,
        }
    }

    pub fn assign<F: Field>(
        &self, 
        layouter: &mut impl Layouter<F>,
        r: F,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "Test", 
            |mut region| {
                for offset in 0..10 {
                    assignf!(region, (self.q_enable, offset) => true.scalar());
                    
                    let is_even = (offset / 2) * 2 == offset;
                    assign!(region, (self.a, offset) => is_even.scalar());
                    assign!(region, (self.b, offset) => 887766.scalar());
                    assignf!(region, (self.c, offset) => 112233.scalar());
                    if is_even {
                        assign!(region, (self.res, offset) => (887766 + 112233).scalar());
                    } else {
                        assign!(region, (self.res, offset) => Scalar::<F>::scalar(&887766) + r);
                    }
                }
                Ok(())
            }
        )
    }
}

#[derive(Clone, Debug, Default)]
struct TestCircuit<F> {
    _phantom: F,
}

impl<F: Field> Circuit<F> for TestCircuit<F> {
    type Config = (TestConfig, Challenge);
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        unimplemented!()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        // dummy column for phase1 challange
        meta.advice_column_in(FirstPhase);
        let randomness = meta.challenge_usable_after(FirstPhase); 
        let config = TestConfig::new(meta, randomness);
        
        (config, randomness)
    }

    fn synthesize(
        &self, 
        (config, randomness): Self::Config, 
        mut layouter: impl Layouter<F>
    ) -> Result<(), halo2_proofs::plonk::Error> {
        let mut r = F::ZERO;
        layouter.get_challenge(randomness).map(|randomness| r = randomness);
        config.assign(&mut layouter, r)?;
        Ok(())
    }
}

#[test]
fn test() {

    use halo2_proofs::{ dev::MockProver, halo2curves::bn256::Fr};

    let circuit = TestCircuit::<Fr>::default();
    let prover = MockProver::<Fr>::run(6, &circuit, vec![]).unwrap();
    prover.assert_satisfied_par();
}