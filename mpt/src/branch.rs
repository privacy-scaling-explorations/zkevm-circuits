use halo2::{
    circuit::{Layouter, Region},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Selector},
    poly::Rotation,
};
use pasta_curves::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::param::HASH_WIDTH;
use crate::param::LAYOUT_OFFSET;
use crate::param::WITNESS_ROW_WIDTH;

#[derive(Clone, Debug)]
pub struct BranchConfig<F> {
    q_enable: Selector,
    s_meta1: Column<Advice>,
    s_meta2: Column<Advice>,
    c_meta1: Column<Advice>,
    c_meta2: Column<Advice>,
    s_advices: [Column<Advice>; HASH_WIDTH],
    c_advices: [Column<Advice>; HASH_WIDTH],
    _marker: PhantomData<F>,
}

impl<F: FieldExt> BranchConfig<F> {
    pub fn configure(
        q_enable: Selector,
        meta: &mut ConstraintSystem<F>,
        s_meta1: Column<Advice>,
        s_meta2: Column<Advice>,
        s_advices: [Column<Advice>; HASH_WIDTH],
        c_meta1: Column<Advice>,
        c_meta2: Column<Advice>,
        c_advices: [Column<Advice>; HASH_WIDTH],
    ) -> BranchConfig<F> {
        meta.create_gate("branch", |meta| {
            let q_enable = meta.query_selector(q_enable);

            let s_meta1 = meta.query_advice(s_meta1, Rotation::cur());

            vec![q_enable * s_meta1]
        });

        BranchConfig {
            q_enable,
            s_meta1,
            s_meta2,
            s_advices,
            c_meta1,
            c_meta2,
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
    use std::marker::PhantomData;
    use std::{convert::TryInto, env};

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

                let s_meta1 = meta.advice_column();
                let s_meta2 = meta.advice_column();
                let s_advices = (0..HASH_WIDTH)
                    .map(|_| meta.advice_column())
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap();

                let c_meta1 = meta.advice_column();
                let c_meta2 = meta.advice_column();
                let c_advices = (0..HASH_WIDTH)
                    .map(|_| meta.advice_column())
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap();

                BranchConfig::configure(
                    q_enable, meta, s_meta1, s_meta2, s_advices, c_meta1,
                    c_meta2, c_advices,
                )
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
                        let mut offset = 0;
                        config.q_enable.enable(&mut region, offset)?;

                        for row in self.witness.iter() {
                            config.q_enable.enable(&mut region, offset)?;

                            region.assign_advice(
                                || format!("assign s_meta1"),
                                config.s_meta1,
                                offset,
                                || Ok(F::from_u64(row[0] as u64)),
                            )?;

                            region.assign_advice(
                                || format!("assign s_meta2"),
                                config.s_meta2,
                                offset,
                                || Ok(F::from_u64(row[1] as u64)),
                            )?;

                            for idx in 0..HASH_WIDTH {
                                region.assign_advice(
                                    || format!("assign s_advice {}", idx),
                                    config.s_advices[idx],
                                    offset,
                                    || {
                                        Ok(F::from_u64(
                                            row[LAYOUT_OFFSET + idx] as u64,
                                        ))
                                    },
                                )?;
                            }

                            region.assign_advice(
                                || format!("assign c_meta1"),
                                config.c_meta1,
                                offset,
                                || {
                                    Ok(F::from_u64(
                                        row[WITNESS_ROW_WIDTH / 2] as u64,
                                    ))
                                },
                            )?;
                            region.assign_advice(
                                || format!("assign c_meta2"),
                                config.c_meta2,
                                offset,
                                || {
                                    Ok(F::from_u64(
                                        row[WITNESS_ROW_WIDTH / 2 + 1] as u64,
                                    ))
                                },
                            )?;

                            for (idx, c) in config.c_advices.iter().enumerate()
                            {
                                region.assign_advice(
                                    || format!("assign c_advice {}", idx),
                                    config.c_advices[idx],
                                    offset,
                                    || {
                                        Ok(F::from_u64(
                                            row[WITNESS_ROW_WIDTH / 2
                                                + LAYOUT_OFFSET
                                                + idx]
                                                as u64,
                                        ))
                                    },
                                )?;
                            }

                            offset += 1
                        }

                        Ok(())
                    },
                )
            }
        }

        let file = std::fs::File::open("mpt/tests/test.json");
        let reader = std::io::BufReader::new(file.unwrap());
        let w: Vec<Vec<u8>> = serde_json::from_reader(reader).unwrap();

        let circuit = MyCircuit::<pallas::Base> {
            _marker: PhantomData,
            witness: w,
        };

        // Test without public inputs
        let prover =
            MockProver::<pallas::Base>::run(9, &circuit, vec![]).unwrap();

        assert_eq!(prover.verify(), Ok(()));
    }
}
