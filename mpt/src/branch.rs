use halo2::{
    circuit::{Layouter, Region},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Selector},
    poly::Rotation,
};
use pasta_curves::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::param::HASH_WIDTH;

#[derive(Clone, Debug)]
pub struct BranchConfig<F> {
    q_enable: Selector,
    s_advices: [Column<Advice>; HASH_WIDTH],
    c_advices: [Column<Advice>; HASH_WIDTH],
    _marker: PhantomData<F>,
}

impl<F: FieldExt> BranchConfig<F> {
    pub fn configure(
        q_enable: Selector,
        meta: &mut ConstraintSystem<F>,
        s_advices: [Column<Advice>; HASH_WIDTH],
        c_advices: [Column<Advice>; HASH_WIDTH],
    ) -> BranchConfig<F> {
        meta.create_gate("branch", |meta| {
            let q_enable = meta.query_selector(q_enable);

            let address = meta.query_advice(s_advices[0], Rotation::cur());

            vec![q_enable * address]
        });

        BranchConfig {
            q_enable,
            s_advices,
            c_advices,
            _marker: PhantomData,
        }
    }
    pub fn load(&self, _layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use halo2::{
        circuit::{Layouter, SimpleFloorPlanner},
        dev::{MockProver, VerifyFailure},
        plonk::{Advice, Circuit, Column, ConstraintSystem, Error},
    };
    use pasta_curves::{arithmetic::FieldExt, pallas};
    use std::convert::TryInto;
    use std::marker::PhantomData;

    #[test]
    fn test_branch() {
        #[derive(Default)]
        struct MyCircuit<F> {
            _marker: PhantomData<F>,
            witness: Vec<Vec<u8>>,
        }

        impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
            type Config = BranchConfig<F>;
            type FloorPlanner = SimpleFloorPlanner;

            fn without_witnesses(&self) -> Self {
                Self::default()
            }

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                let q_enable = meta.selector();

                let s_advices = (0..HASH_WIDTH)
                    .map(|_| meta.advice_column())
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap();

                let c_advices = (0..HASH_WIDTH)
                    .map(|_| meta.advice_column())
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap();

                BranchConfig::configure(q_enable, meta, s_advices, c_advices)
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<F>,
            ) -> Result<(), Error> {
                config.load(&mut layouter)?;

                layouter.assign_region(
                    || "assign input state",
                    |mut region| {
                        let offset = 0;
                        config.q_enable.enable(&mut region, offset)?;

                        for (idx, c) in config.s_advices.iter().enumerate() {
                            region.assign_advice(
                                || format!("assign s_advice {}", idx),
                                config.s_advices[idx],
                                offset,
                                || Ok(F::one()),
                            )?;
                        }
                        for (idx, c) in config.c_advices.iter().enumerate() {
                            region.assign_advice(
                                || format!("assign c_advice {}", idx),
                                config.c_advices[idx],
                                offset,
                                || Ok(F::zero()),
                            )?;
                        }

                        Ok(())
                    },
                )?;

                Ok(())
            }
        }

        let circuit = MyCircuit::<pallas::Base> {
            _marker: PhantomData,
        };

        // Test without public inputs
        let prover =
            MockProver::<pallas::Base>::run(9, &circuit, vec![]).unwrap();

        assert_eq!(prover.verify(), Ok(()));
    }
}
