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
    node_index: Column<Advice>,
    key: Column<Advice>,
    s_rlp1: Column<Advice>,
    s_rlp2: Column<Advice>,
    c_rlp1: Column<Advice>,
    c_rlp2: Column<Advice>,
    s_advices: [Column<Advice>; HASH_WIDTH],
    c_advices: [Column<Advice>; HASH_WIDTH],
    _marker: PhantomData<F>,
}

impl<F: FieldExt> BranchConfig<F> {
    pub fn configure(
        q_enable: Selector,
        meta: &mut ConstraintSystem<F>,
        node_index: Column<Advice>,
        key: Column<Advice>,
        s_rlp1: Column<Advice>,
        s_rlp2: Column<Advice>,
        s_advices: [Column<Advice>; HASH_WIDTH],
        c_rlp1: Column<Advice>,
        c_rlp2: Column<Advice>,
        c_advices: [Column<Advice>; HASH_WIDTH],
    ) -> BranchConfig<F> {
        meta.create_gate("branch", |meta| {
            let q_enable = meta.query_selector(q_enable);

            let mut constraints = vec![];
            let node_index = meta.query_advice(key, Rotation::cur());
            let key = meta.query_advice(key, Rotation::cur());

            let s_rlp1 = meta.query_advice(s_rlp1, Rotation::cur());
            let s_rlp2 = meta.query_advice(s_rlp2, Rotation::cur());

            let c_rlp1 = meta.query_advice(c_rlp1, Rotation::cur());
            let c_rlp2 = meta.query_advice(c_rlp2, Rotation::cur());
            constraints.push(
                q_enable.clone()
                    * (s_rlp1 - c_rlp1)
                    * (node_index.clone() - key.clone()),
            );
            constraints.push(
                q_enable.clone()
                    * (s_rlp2 - c_rlp2)
                    * (node_index.clone() - key.clone()),
            );

            for (ind, col) in s_advices.iter().enumerate() {
                let s = meta.query_advice(*col, Rotation::cur());
                let c = meta.query_advice(c_advices[ind], Rotation::cur());
                constraints.push(
                    q_enable.clone()
                        * (s - c)
                        * (node_index.clone() - key.clone()),
                );
            }

            constraints
        });

        BranchConfig {
            q_enable,
            node_index,
            key,
            s_rlp1,
            s_rlp2,
            s_advices,
            c_rlp1,
            c_rlp2,
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

                let node_index = meta.advice_column();
                let key = meta.advice_column();

                let s_rlp1 = meta.advice_column();
                let s_rlp2 = meta.advice_column();
                let s_advices = (0..HASH_WIDTH)
                    .map(|_| meta.advice_column())
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap();

                let c_rlp1 = meta.advice_column();
                let c_rlp2 = meta.advice_column();
                let c_advices = (0..HASH_WIDTH)
                    .map(|_| meta.advice_column())
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap();

                BranchConfig::configure(
                    q_enable, meta, node_index, key, s_rlp1, s_rlp2, s_advices,
                    c_rlp1, c_rlp2, c_advices,
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

                        for (ind, row) in self.witness.iter().enumerate() {
                            if ind == 0 {
                                continue;
                            }
                            config.q_enable.enable(&mut region, offset)?;

                            region.assign_advice(
                                || format!("assign node_index"),
                                config.node_index,
                                offset,
                                || Ok(F::from_u64((ind - 1) as u64)),
                            )?;

                            region.assign_advice(
                                || format!("assign key"),
                                config.key,
                                offset,
                                || Ok(F::from_u64(self.witness[0][4] as u64)),
                            )?;

                            region.assign_advice(
                                || format!("assign s_rlp1"),
                                config.s_rlp1,
                                offset,
                                || Ok(F::from_u64(row[0] as u64)),
                            )?;

                            region.assign_advice(
                                || format!("assign s_rlp2"),
                                config.s_rlp2,
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
                                || format!("assign c_rlp1"),
                                config.c_rlp1,
                                offset,
                                || {
                                    Ok(F::from_u64(
                                        row[WITNESS_ROW_WIDTH / 2] as u64,
                                    ))
                                },
                            )?;
                            region.assign_advice(
                                || format!("assign c_rlp2"),
                                config.c_rlp2,
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

        // for debugging:
        let file = std::fs::File::open("mpt/tests/test.json");
        // let file = std::fs::File::open("tests/test.json");
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
