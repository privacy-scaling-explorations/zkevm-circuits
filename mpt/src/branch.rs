use halo2::{
    circuit::{Layouter, Region},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Selector},
    poly::Rotation,
};
use keccak256::plain::Keccak;
use pasta_curves::arithmetic::FieldExt;
use std::{convert::TryInto, marker::PhantomData};

use crate::param::LAYOUT_OFFSET;
use crate::param::WITNESS_ROW_WIDTH;
use crate::param::{HASH_WIDTH, KECCAK_WIDTH};

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
    keccak_table: [Column<Advice>; KECCAK_WIDTH],
    _marker: PhantomData<F>,
}

impl<F: FieldExt> BranchConfig<F> {
    pub(crate) fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let q_enable = meta.selector();

        let node_index = meta.advice_column();
        let key = meta.advice_column();

        let s_rlp1 = meta.advice_column();
        let s_rlp2 = meta.advice_column();
        let s_advices: [Column<Advice>; HASH_WIDTH] = (0..HASH_WIDTH)
            .map(|_| meta.advice_column())
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let c_rlp1 = meta.advice_column();
        let c_rlp2 = meta.advice_column();
        let c_advices: [Column<Advice>; HASH_WIDTH] = (0..HASH_WIDTH)
            .map(|_| meta.advice_column())
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let keccak_table = (0..KECCAK_WIDTH)
            .map(|_| meta.advice_column())
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        meta.create_gate("branch", |meta| {
            let q_enable = meta.query_selector(q_enable);

            let mut constraints = vec![];
            let node_index = meta.query_advice(node_index, Rotation::cur());
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
            keccak_table,
            _marker: PhantomData,
        }
    }

    pub(crate) fn assign(
        &self,
        mut layouter: impl Layouter<F>,
        witness: &Vec<Vec<u8>>,
    ) {
        layouter
            .assign_region(
                || "assign input state",
                |mut region| {
                    let mut offset = 0;
                    for (ind, row) in witness.iter().enumerate() {
                        if ind == 0 || ind == 17 {
                            continue;
                        }
                        self.q_enable.enable(&mut region, offset)?;

                        region.assign_advice(
                            || format!("assign node_index"),
                            self.node_index,
                            offset,
                            || Ok(F::from_u64((ind - 1) as u64)),
                        )?;

                        region.assign_advice(
                            || format!("assign key"),
                            self.key,
                            offset,
                            || Ok(F::from_u64(witness[0][4] as u64)),
                        )?;

                        region.assign_advice(
                            || format!("assign s_rlp1"),
                            self.s_rlp1,
                            offset,
                            || Ok(F::from_u64(row[0] as u64)),
                        )?;

                        region.assign_advice(
                            || format!("assign s_rlp2"),
                            self.s_rlp2,
                            offset,
                            || Ok(F::from_u64(row[1] as u64)),
                        )?;

                        for idx in 0..HASH_WIDTH {
                            region.assign_advice(
                                || format!("assign s_advice {}", idx),
                                self.s_advices[idx],
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
                            self.c_rlp1,
                            offset,
                            || {
                                Ok(F::from_u64(
                                    row[WITNESS_ROW_WIDTH / 2] as u64,
                                ))
                            },
                        )?;
                        region.assign_advice(
                            || format!("assign c_rlp2"),
                            self.c_rlp2,
                            offset,
                            || {
                                Ok(F::from_u64(
                                    row[WITNESS_ROW_WIDTH / 2 + 1] as u64,
                                ))
                            },
                        )?;

                        for (idx, c) in self.c_advices.iter().enumerate() {
                            region.assign_advice(
                                || format!("assign c_advice {}", idx),
                                self.c_advices[idx],
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
            .ok();
    }

    pub fn load(
        &self,
        _layouter: &mut impl Layouter<F>,
        to_be_hashed: Vec<&Vec<u8>>,
    ) -> Result<(), Error> {
        self.load_keccak_table(_layouter, to_be_hashed);

        Ok(())
    }

    fn load_keccak_table(
        &self,
        layouter: &mut impl Layouter<F>,
        to_be_hashed: Vec<&Vec<u8>>,
    ) -> Result<(), Error> {
        fn compute_keccak(msg: &[u8]) -> Vec<u8> {
            let mut keccak = Keccak::default();
            keccak.update(msg);
            keccak.digest()
        }

        let foo = compute_keccak(&[
            226, 160, 58, 99, 87, 1, 44, 26, 58, 224, 161, 125, 48, 76, 153,
            32, 49, 3, 130, 217, 104, 235, 204, 75, 23, 113, 244, 28, 107, 48,
            66, 5, 181, 112, 2,
        ]);
        println!("{:?}", foo);

        layouter.assign_region(
            || "keccak table",
            |mut region| {
                let mut offset = 0;

                for t in to_be_hashed.iter() {
                    println!("{:?}", t);
                    println!("{:?}", "-======");
                    for (ind, column) in self.keccak_table.iter().enumerate() {
                        println!("{:?}", t[ind]);
                        region.assign_advice(
                            || "Keccak table",
                            *column,
                            offset,
                            || Ok(F::from_u64(t[ind] as u64)),
                        )?;
                    }
                    offset += 1;
                }

                Ok(())
            },
        )
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
                BranchConfig::configure(meta)
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<F>,
            ) -> Result<(), Error> {
                let mut to_be_hashed = vec![];
                to_be_hashed.push(&self.witness[17]);
                config.load(&mut layouter, to_be_hashed)?;
                config.assign(layouter, &self.witness);

                Ok(())
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
