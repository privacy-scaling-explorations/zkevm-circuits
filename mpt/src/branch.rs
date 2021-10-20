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
use crate::param::{HASH_WIDTH, KECCAK_INPUT_WIDTH, KECCAK_OUTPUT_WIDTH};

#[derive(Clone, Debug)]
pub struct BranchConfig<F> {
    q_enable: Selector,
    is_leaf: Column<Advice>,
    node_index: Column<Advice>,
    key: Column<Advice>,
    s_rlp1: Column<Advice>,
    s_rlp2: Column<Advice>,
    c_rlp1: Column<Advice>,
    c_rlp2: Column<Advice>,
    s_advices: [Column<Advice>; HASH_WIDTH],
    c_advices: [Column<Advice>; HASH_WIDTH],
    keccak_input_table: [Column<Advice>; KECCAK_INPUT_WIDTH],
    keccak_output_table: [Column<Advice>; KECCAK_OUTPUT_WIDTH],
    _marker: PhantomData<F>,
}

impl<F: FieldExt> BranchConfig<F> {
    pub(crate) fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let q_enable = meta.selector();

        let is_leaf = meta.advice_column();
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

        let keccak_input_table = (0..KECCAK_INPUT_WIDTH)
            .map(|_| meta.advice_column())
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let keccak_output_table = (0..KECCAK_OUTPUT_WIDTH)
            .map(|_| meta.advice_column())
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let one = Expression::Constant(F::one());

        meta.create_gate("branch", |meta| {
            let q_enable = meta.query_selector(q_enable);

            let mut constraints = vec![];
            let is_leaf = meta.query_advice(is_leaf, Rotation::cur());

            let bool_check_is_leaf =
                is_leaf.clone() * (one.clone() - is_leaf.clone());
            let node_index = meta.query_advice(node_index, Rotation::cur());
            let key = meta.query_advice(key, Rotation::cur());

            let s_rlp1 = meta.query_advice(s_rlp1, Rotation::cur());
            let s_rlp2 = meta.query_advice(s_rlp2, Rotation::cur());

            let c_rlp1 = meta.query_advice(c_rlp1, Rotation::cur());
            let c_rlp2 = meta.query_advice(c_rlp2, Rotation::cur());

            let not_leaf = one.clone() - is_leaf;

            constraints.push(q_enable.clone() * bool_check_is_leaf);
            constraints.push(
                q_enable.clone()
                    * not_leaf.clone()
                    * (s_rlp1 - c_rlp1)
                    * (node_index.clone() - key.clone()),
            );
            constraints.push(
                q_enable.clone()
                    * not_leaf.clone()
                    * (s_rlp2 - c_rlp2)
                    * (node_index.clone() - key.clone()),
            );

            for (ind, col) in s_advices.iter().enumerate() {
                let s = meta.query_advice(*col, Rotation::cur());
                let c = meta.query_advice(c_advices[ind], Rotation::cur());
                constraints.push(
                    q_enable.clone()
                        // * not_leaf.clone()
                        * (s - c)
                        * (node_index.clone() - key.clone()),
                );
            }

            constraints
        });

        BranchConfig {
            q_enable,
            is_leaf,
            node_index,
            key,
            s_rlp1,
            s_rlp2,
            s_advices,
            c_rlp1,
            c_rlp2,
            c_advices,
            keccak_input_table,
            keccak_output_table,
            _marker: PhantomData,
        }
    }

    fn assign_row(
        &self,
        region: &mut Region<'_, F>,
        row: &Vec<u8>,
        is_leaf: bool,
        offset: usize,
    ) -> Result<(), Error> {
        region.assign_advice(
            || format!("assign is_leaf"),
            self.is_leaf,
            offset,
            || Ok(F::from_u64(is_leaf as u64)),
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
                || Ok(F::from_u64(row[LAYOUT_OFFSET + idx] as u64)),
            )?;
        }

        region.assign_advice(
            || format!("assign c_rlp1"),
            self.c_rlp1,
            offset,
            || Ok(F::from_u64(row[WITNESS_ROW_WIDTH / 2] as u64)),
        )?;
        region.assign_advice(
            || format!("assign c_rlp2"),
            self.c_rlp2,
            offset,
            || Ok(F::from_u64(row[WITNESS_ROW_WIDTH / 2 + 1] as u64)),
        )?;

        for (idx, c) in self.c_advices.iter().enumerate() {
            let val;
            if WITNESS_ROW_WIDTH / 2 + LAYOUT_OFFSET + idx >= row.len() {
                // leaf might not need all columns
                val = 0;
            } else {
                val = row[WITNESS_ROW_WIDTH / 2 + LAYOUT_OFFSET + idx];
            }
            region.assign_advice(
                || format!("assign c_advice {}", idx),
                self.c_advices[idx],
                offset,
                || Ok(F::from_u64(val as u64)),
            )?;
        }
        Ok(())
    }

    fn assign_leaf(
        &self,
        region: &mut Region<'_, F>,
        row: &Vec<u8>,
        offset: usize,
    ) -> Result<(), Error> {
        region.assign_advice(
            || format!("assign node_index"),
            self.node_index,
            offset,
            || Ok(F::zero()),
        )?;

        region.assign_advice(
            || format!("assign key"),
            self.key,
            offset,
            || Ok(F::zero()),
        )?;

        self.assign_row(region, row, true, offset)?;

        Ok(())
    }

    fn assign_branch_row(
        &self,
        region: &mut Region<'_, F>,
        ind: usize,
        key: u8,
        row: &Vec<u8>,
        offset: usize,
    ) -> Result<(), Error> {
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
            || Ok(F::from_u64(key as u64)),
        )?;

        self.assign_row(region, row, false, offset)?;

        Ok(())
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
                        if ind > 0 && ind < 17 {
                            self.q_enable.enable(&mut region, offset)?;
                            self.assign_branch_row(
                                &mut region,
                                ind,
                                witness[0][4],
                                row,
                                offset,
                            )?;
                            offset += 1
                        }
                        if ind == 17 {
                            self.q_enable.enable(&mut region, offset)?;
                            self.assign_leaf(&mut region, row, offset)?;
                            offset += 1
                        }
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

    fn pad(&self, input: &[u8]) -> Vec<u8> {
        let rate = 136;
        let padding_total = rate - (input.len() % rate);
        let mut padding: Vec<u8>;

        if padding_total == 1 {
            padding = vec![0x81];
        } else {
            padding = vec![0x01];
            padding.resize(padding_total - 1, 0x00);
            padding.push(0x80);
        }

        let message = [input, &padding].concat();
        message
    }

    // see bits_to_u64_words_le
    fn into_words(&self, message: &[u8]) -> Vec<u64> {
        let words_total = message.len() / 8;
        let mut words: Vec<u64> = vec![0; words_total];

        for i in 0..words_total {
            let mut word_bits: [u8; 8] = Default::default();
            word_bits.copy_from_slice(&message[i * 8..i * 8 + 8]);
            words[i] = u64::from_le_bytes(word_bits);
        }

        words
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

        layouter.assign_region(
            || "keccak table",
            |mut region| {
                let mut offset = 0;

                for t in to_be_hashed.iter() {
                    let hash = compute_keccak(t);
                    let padded = self.pad(t);
                    let keccak_input = self.into_words(&padded);
                    let keccak_output = self.into_words(&hash);

                    for (ind, column) in
                        self.keccak_input_table.iter().enumerate()
                    {
                        region.assign_advice(
                            || "Keccak input table",
                            *column,
                            offset,
                            || Ok(F::from_u64(keccak_input[ind] as u64)),
                        )?;
                    }
                    for (ind, column) in
                        self.keccak_output_table.iter().enumerate()
                    {
                        region.assign_advice(
                            || "Keccak output table",
                            *column,
                            offset,
                            || Ok(F::from_u64(keccak_output[ind] as u64)),
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
