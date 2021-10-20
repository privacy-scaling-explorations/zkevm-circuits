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
    is_branch_child: Column<Advice>,
    is_compact_leaf: Column<Advice>,
    node_index: Column<Advice>,
    key: Column<Advice>,
    s_rlp1: Column<Advice>,
    s_rlp2: Column<Advice>,
    c_rlp1: Column<Advice>,
    c_rlp2: Column<Advice>,
    s_advices: [Column<Advice>; HASH_WIDTH],
    c_advices: [Column<Advice>; HASH_WIDTH],
    s_keccak: [Column<Advice>; KECCAK_OUTPUT_WIDTH],
    c_keccak: [Column<Advice>; KECCAK_OUTPUT_WIDTH],
    keccak_input_table: [Column<Advice>; KECCAK_INPUT_WIDTH],
    keccak_output_table: [Column<Advice>; KECCAK_OUTPUT_WIDTH],
    _marker: PhantomData<F>,
}

impl<F: FieldExt> BranchConfig<F> {
    pub(crate) fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let q_enable = meta.selector();

        let is_compact_leaf = meta.advice_column();
        let is_branch_child = meta.advice_column();
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

        let s_keccak = (0..KECCAK_OUTPUT_WIDTH)
            .map(|_| meta.advice_column())
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let c_keccak = (0..KECCAK_OUTPUT_WIDTH)
            .map(|_| meta.advice_column())
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let one = Expression::Constant(F::one());

        meta.create_gate("branch", |meta| {
            let q_enable = meta.query_selector(q_enable);

            let mut constraints = vec![];
            let is_compact_leaf =
                meta.query_advice(is_compact_leaf, Rotation::cur());
            let is_branch_child =
                meta.query_advice(is_branch_child, Rotation::cur());

            let bool_check_is_compact_leaf = is_compact_leaf.clone()
                * (one.clone() - is_compact_leaf.clone());
            let bool_check_is_branch_child = is_branch_child.clone()
                * (one.clone() - is_branch_child.clone());

            let node_index = meta.query_advice(node_index, Rotation::cur());
            let key = meta.query_advice(key, Rotation::cur());

            let s_rlp1 = meta.query_advice(s_rlp1, Rotation::cur());
            let s_rlp2 = meta.query_advice(s_rlp2, Rotation::cur());

            let c_rlp1 = meta.query_advice(c_rlp1, Rotation::cur());
            let c_rlp2 = meta.query_advice(c_rlp2, Rotation::cur());

            /*
            TODO for leaf:
            Let's say we have a leaf n where
                n.Key = [10,6,3,5,7,0,1,2,12,1,10,3,10,14,0,10,1,7,13,3,0,4,12,9,9,2,0,3,1,0,3,8,2,13,9,6,8,14,11,12,12,4,11,1,7,7,1,15,4,1,12,6,11,3,0,4,2,0,5,11,5,7,0,16]
                n.Val = [2].
            Before put in a proof, a leaf is hashed:
            https://github.com/ethereum/go-ethereum/blob/master/trie/proof.go#L78
            But before being hashed, Key is put in compact form:
            https://github.com/ethereum/go-ethereum/blob/master/trie/hasher.go#L110
            Key becomes:
                [58,99,87,1,44,26,58,224,161,125,48,76,153,32,49,3,130,217,104,235,204,75,23,113,244,28,107,48,66,5,181,112]
            Then the node is RLP encoded:
            https://github.com/ethereum/go-ethereum/blob/master/trie/hasher.go#L157
            RLP:
                [226,160,58,99,87,1,44,26,58,224,161,125,48,76,153,32,49,3,130,217,104,235,204,75,23,113,244,28,107,48,66,5,181,112,2]
            Finally, the RLP is hashed:
                [32,34,39,131,73,65,47,37,211,142,206,231,172,16,11,203,33,107,30,7,213,226,2,174,55,216,4,117,220,10,186,68]

            In a proof (witness), we have [226, 160, ...] in columns s_rlp1, s_rlp2, ...
            Constraint 1: We need to compute a hash of this value and compare it with [32, 34, ...] which should be
                one of the branch children. lookup ...
                Constraint 1.1: s_keccak, c_keccak the same for all 16 children
                Constraint 1.2: for key = ind: s_keccak = converted s_advice and c_keccak = converted c_advice
                Constraint 1.3: we add additional row for a leaf prepared for keccak (17 words),
                  we do a lookup on this 17 words in s_keccak / c_keccak
            Constraint 2: We need to convert it back to non-compact format to get the remaining key.
                We need to verify the key until now (in nodes above) concatenated with the remaining key
                gives us the key where the storage change is happening.
            */

            constraints.push(q_enable.clone() * bool_check_is_compact_leaf);
            constraints.push(q_enable.clone() * bool_check_is_branch_child);
            // TODO: is_compact_leaf + is_branch_child = 1
            // TODO: might be similar structure as in evm circuit - having branch child, compact leaf ...
            // as opcodes
            // TODO: node_index is increasing by 1 for is_branch_child
            constraints.push(
                q_enable.clone()
                    * is_branch_child.clone()
                    * (s_rlp1 - c_rlp1)
                    * (node_index.clone() - key.clone()),
            );
            constraints.push(
                q_enable.clone()
                    * is_branch_child.clone()
                    * (s_rlp2 - c_rlp2)
                    * (node_index.clone() - key.clone()),
            );

            for (ind, col) in s_advices.iter().enumerate() {
                let s = meta.query_advice(*col, Rotation::cur());
                let c = meta.query_advice(c_advices[ind], Rotation::cur());
                constraints.push(
                    q_enable.clone()
                        * is_branch_child.clone()
                        * (s - c)
                        * (node_index.clone() - key.clone()),
                );
            }

            constraints
        });

        BranchConfig {
            q_enable,
            is_branch_child,
            is_compact_leaf,
            node_index,
            key,
            s_rlp1,
            s_rlp2,
            c_rlp1,
            c_rlp2,
            s_advices,
            c_advices,
            s_keccak,
            c_keccak,
            keccak_input_table,
            keccak_output_table,
            _marker: PhantomData,
        }
    }

    fn assign_row(
        &self,
        region: &mut Region<'_, F>,
        row: &Vec<u8>,
        is_branch_child: bool,
        is_compact_leaf: bool,
        offset: usize,
    ) -> Result<(), Error> {
        region.assign_advice(
            || format!("assign is_branch_child"),
            self.is_branch_child,
            offset,
            || Ok(F::from_u64(is_branch_child as u64)),
        )?;

        region.assign_advice(
            || format!("assign is_compact_leaf"),
            self.is_compact_leaf,
            offset,
            || Ok(F::from_u64(is_compact_leaf as u64)),
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

        self.assign_row(region, row, false, true, offset)?;

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

        self.assign_row(region, row, true, false, offset)?;

        Ok(())
    }

    pub(crate) fn assign(
        &self,
        mut layouter: impl Layouter<F>,
        witness: &Vec<Vec<u8>>,
    ) {
        layouter
            .assign_region(
                || "assign MPT proof",
                |mut region| {
                    let mut offset = 0;

                    // TODO: if row type == branch, traverse to key = ind, convert hash
                    // into 4-words format, assign s_keccak and c_keccak

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

        let prover =
            MockProver::<pallas::Base>::run(9, &circuit, vec![]).unwrap();

        assert_eq!(prover.verify(), Ok(()));
    }
}
