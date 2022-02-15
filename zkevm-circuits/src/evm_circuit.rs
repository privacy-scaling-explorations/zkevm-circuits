//! The EVM circuit implementation.

#![allow(missing_docs)]
use halo2::{
    arithmetic::FieldExt,
    circuit::{Layouter, Region},
    plonk::*,
    poly::Rotation,
};

mod execution;
pub mod param;
mod step;
pub(crate) mod util;

pub mod table;
pub mod witness;

use execution::ExecutionConfig;
use table::{FixedTableTag, LookupTable};
use witness::Block;

use self::witness::RwRow;

#[derive(Clone, Copy)]
pub struct RwTable {
    pub rw_counter: Column<Advice>,
    pub is_write: Column<Advice>,
    pub tag: Column<Advice>,
    pub key2: Column<Advice>,
    pub key3: Column<Advice>,
    pub key4: Column<Advice>,
    pub value: Column<Advice>,
    pub value_prev: Column<Advice>,
    pub aux1: Column<Advice>,
    pub aux2: Column<Advice>,
}

impl<F: FieldExt> LookupTable<F, 10> for RwTable {
    fn table_exprs(&self, meta: &mut VirtualCells<F>) -> [Expression<F>; 10] {
        [
            meta.query_advice(self.rw_counter, Rotation::cur()),
            meta.query_advice(self.is_write, Rotation::cur()),
            meta.query_advice(self.tag, Rotation::cur()),
            meta.query_advice(self.key2, Rotation::cur()),
            meta.query_advice(self.key3, Rotation::cur()),
            meta.query_advice(self.key4, Rotation::cur()),
            meta.query_advice(self.value, Rotation::cur()),
            meta.query_advice(self.value_prev, Rotation::cur()),
            meta.query_advice(self.aux1, Rotation::cur()),
            meta.query_advice(self.aux2, Rotation::cur()),
        ]
    }
}
impl RwTable {
    pub fn construct<F: FieldExt>(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            rw_counter: meta.advice_column(),
            is_write: meta.advice_column(),
            tag: meta.advice_column(),
            key2: meta.advice_column(),
            key3: meta.advice_column(),
            key4: meta.advice_column(),
            value: meta.advice_column(),
            value_prev: meta.advice_column(),
            aux1: meta.advice_column(),
            aux2: meta.advice_column(),
        }
    }
    pub fn assign<F: FieldExt>(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        row: &RwRow<F>,
    ) -> Result<(), Error> {
        for (column, value) in [
            (self.rw_counter, row.rw_counter),
            (self.is_write, row.is_write),
            (self.tag, row.tag),
            (self.key2, row.key2),
            (self.key3, row.key3),
            (self.key4, row.key4),
            (self.value, row.value),
            (self.value_prev, row.value_prev),
            (self.aux1, row.aux1),
            (self.aux2, row.aux2),
        ] {
            region.assign_advice(|| "rw table all-zero row", column, offset, || Ok(value))?;
        }
        Ok(())
    }
}

/// EvmCircuit implements verification of execution trace of a block.
#[derive(Clone, Debug)]
pub struct EvmCircuit<F> {
    fixed_table: [Column<Fixed>; 4],
    execution: ExecutionConfig<F>,
}

impl<F: FieldExt> EvmCircuit<F> {
    /// Configure EvmCircuit
    pub fn configure<TxTable, RwTable, BytecodeTable, BlockTable>(
        meta: &mut ConstraintSystem<F>,
        power_of_randomness: [Expression<F>; 31],
        tx_table: TxTable,
        rw_table: RwTable,
        bytecode_table: BytecodeTable,
        block_table: BlockTable,
    ) -> Self
    where
        TxTable: LookupTable<F, 4>,
        RwTable: LookupTable<F, 10>,
        BytecodeTable: LookupTable<F, 4>,
        BlockTable: LookupTable<F, 3>,
    {
        let fixed_table = [(); 4].map(|_| meta.fixed_column());

        let execution = ExecutionConfig::configure(
            meta,
            power_of_randomness,
            fixed_table,
            tx_table,
            rw_table,
            bytecode_table,
            block_table,
        );

        Self {
            fixed_table,
            execution,
        }
    }

    /// Load fixed table
    pub fn load_fixed_table(
        &self,
        layouter: &mut impl Layouter<F>,
        fixed_table_tags: Vec<FixedTableTag>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "fixed table",
            |mut region| {
                for (offset, row) in std::iter::once([F::zero(); 4])
                    .chain(fixed_table_tags.iter().map(|tag| tag.build()).flatten())
                    .enumerate()
                {
                    for (column, value) in self.fixed_table.iter().zip(row) {
                        region.assign_fixed(|| "", *column, offset, || Ok(value))?;
                    }
                }

                Ok(())
            },
        )
    }

    /// Assign block
    pub fn assign_block(
        &self,
        layouter: &mut impl Layouter<F>,
        block: &Block<F>,
    ) -> Result<(), Error> {
        self.execution.assign_block(layouter, block)
    }

    /// Assign exact steps in block without padding for unit test purpose
    pub fn assign_block_exact(
        &self,
        layouter: &mut impl Layouter<F>,
        block: &Block<F>,
    ) -> Result<(), Error> {
        self.execution.assign_block_exact(layouter, block)
    }
}

#[cfg(test)]
pub(crate) mod test {
    use crate::{
        evm_circuit::{
            param::STEP_HEIGHT,
            table::FixedTableTag,
            witness::{Block, BlockContext, Bytecode, Rw, Transaction},
            EvmCircuit,
        },
        util::Expr,
    };
    use eth_types::Word;
    use halo2::{
        arithmetic::{BaseExt, FieldExt},
        circuit::{Layouter, SimpleFloorPlanner},
        dev::{MockProver, VerifyFailure},
        plonk::{Advice, Circuit, Column, ConstraintSystem, Error},
        poly::Rotation,
    };
    use pairing::bn256::Fr as Fp;
    use rand::{
        distributions::uniform::{SampleRange, SampleUniform},
        random, thread_rng, Rng,
    };

    use super::RwTable;

    pub(crate) fn rand_range<T, R>(range: R) -> T
    where
        T: SampleUniform,
        R: SampleRange<T>,
    {
        thread_rng().gen_range(range)
    }

    pub(crate) fn rand_bytes(n: usize) -> Vec<u8> {
        vec![random(); n]
    }

    pub(crate) fn rand_bytes_array<const N: usize>() -> [u8; N] {
        [(); N].map(|_| random())
    }

    pub(crate) fn rand_word() -> Word {
        Word::from_big_endian(&rand_bytes_array::<32>())
    }

    pub(crate) fn rand_fp() -> Fp {
        Fp::rand()
    }

    #[derive(Clone)]
    pub(crate) struct TestCircuitConfig<F> {
        tx_table: [Column<Advice>; 4],
        rw_table: RwTable,
        bytecode_table: [Column<Advice>; 4],
        block_table: [Column<Advice>; 3],
        evm_circuit: EvmCircuit<F>,
    }

    impl<F: FieldExt> TestCircuitConfig<F> {
        fn load_txs(
            &self,
            layouter: &mut impl Layouter<F>,
            txs: &[Transaction<F>],
            randomness: F,
        ) -> Result<(), Error> {
            layouter.assign_region(
                || "tx table",
                |mut region| {
                    let mut offset = 0;
                    for column in self.tx_table {
                        region.assign_advice(
                            || "tx table all-zero row",
                            column,
                            offset,
                            || Ok(F::zero()),
                        )?;
                    }
                    offset += 1;

                    for tx in txs.iter() {
                        for row in tx.table_assignments(randomness) {
                            for (column, value) in self.tx_table.iter().zip(row) {
                                region.assign_advice(
                                    || format!("tx table row {}", offset),
                                    *column,
                                    offset,
                                    || Ok(value),
                                )?;
                            }
                            offset += 1;
                        }
                    }
                    Ok(())
                },
            )
        }

        fn load_rws(
            &self,
            layouter: &mut impl Layouter<F>,
            rws: &[Rw],
            randomness: F,
        ) -> Result<(), Error> {
            layouter.assign_region(
                || "rw table",
                |mut region| {
                    let mut offset = 0;
                    self.rw_table
                        .assign(&mut region, offset, &Default::default())?;
                    offset += 1;

                    for rw in rws.iter() {
                        self.rw_table.assign(
                            &mut region,
                            offset,
                            &rw.table_assignment(randomness),
                        )?;
                        offset += 1;
                    }
                    Ok(())
                },
            )
        }

        fn load_bytecodes(
            &self,
            layouter: &mut impl Layouter<F>,
            bytecodes: &[Bytecode],
            randomness: F,
        ) -> Result<(), Error> {
            layouter.assign_region(
                || "bytecode table",
                |mut region| {
                    let mut offset = 0;
                    for column in self.bytecode_table {
                        region.assign_advice(
                            || "bytecode table all-zero row",
                            column,
                            offset,
                            || Ok(F::zero()),
                        )?;
                    }
                    offset += 1;

                    for bytecode in bytecodes.iter() {
                        for row in bytecode.table_assignments(randomness) {
                            for (column, value) in self.bytecode_table.iter().zip(row) {
                                region.assign_advice(
                                    || format!("bytecode table row {}", offset),
                                    *column,
                                    offset,
                                    || Ok(value),
                                )?;
                            }
                            offset += 1;
                        }
                    }
                    Ok(())
                },
            )
        }

        fn load_blocks(
            &self,
            layouter: &mut impl Layouter<F>,
            block: &BlockContext<F>,
            randomness: F,
        ) -> Result<(), Error> {
            layouter.assign_region(
                || "block table",
                |mut region| {
                    let mut offset = 0;
                    for column in self.block_table {
                        region.assign_advice(
                            || "block table all-zero row",
                            column,
                            offset,
                            || Ok(F::zero()),
                        )?;
                    }
                    offset += 1;

                    for row in block.table_assignments(randomness) {
                        for (column, value) in self.block_table.iter().zip(row) {
                            region.assign_advice(
                                || format!("block table row {}", offset),
                                *column,
                                offset,
                                || Ok(value),
                            )?;
                        }
                        offset += 1;
                    }

                    Ok(())
                },
            )
        }
    }

    #[derive(Default)]
    pub(crate) struct TestCircuit<F> {
        block: Block<F>,
        fixed_table_tags: Vec<FixedTableTag>,
    }

    impl<F> TestCircuit<F> {
        pub fn new(block: Block<F>, fixed_table_tags: Vec<FixedTableTag>) -> Self {
            Self {
                block,
                fixed_table_tags,
            }
        }
    }

    impl<F: FieldExt> Circuit<F> for TestCircuit<F> {
        type Config = TestCircuitConfig<F>;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let tx_table = [(); 4].map(|_| meta.advice_column());
            let rw_table = RwTable::construct(meta);
            let bytecode_table = [(); 4].map(|_| meta.advice_column());
            let block_table = [(); 3].map(|_| meta.advice_column());

            let power_of_randomness = {
                let columns = [(); 31].map(|_| meta.instance_column());
                let mut power_of_randomness = None;

                meta.create_gate("", |meta| {
                    power_of_randomness =
                        Some(columns.map(|column| meta.query_instance(column, Rotation::cur())));

                    [0.expr()]
                });

                power_of_randomness.unwrap()
            };

            Self::Config {
                tx_table,
                rw_table,
                bytecode_table,
                block_table,
                evm_circuit: EvmCircuit::configure(
                    meta,
                    power_of_randomness,
                    tx_table,
                    rw_table,
                    bytecode_table,
                    block_table,
                ),
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            config
                .evm_circuit
                .load_fixed_table(&mut layouter, self.fixed_table_tags.clone())?;
            config.load_txs(&mut layouter, &self.block.txs, self.block.randomness)?;
            config.load_rws(&mut layouter, &self.block.rws, self.block.randomness)?;
            config.load_bytecodes(&mut layouter, &self.block.bytecodes, self.block.randomness)?;
            config.load_blocks(&mut layouter, &self.block.context, self.block.randomness)?;
            config
                .evm_circuit
                .assign_block_exact(&mut layouter, &self.block)
        }
    }

    pub(crate) fn run_test_circuit<F: FieldExt>(
        block: Block<F>,
        fixed_table_tags: Vec<FixedTableTag>,
    ) -> Result<(), Vec<VerifyFailure>> {
        let log2_ceil = |n| u32::BITS - (n as u32).leading_zeros() - (n & (n - 1) == 0) as u32;

        let k = log2_ceil(
            64 + fixed_table_tags
                .iter()
                .map(|tag| tag.build::<F>().count())
                .sum::<usize>(),
        );
        let k = k.max(log2_ceil(
            64 + block
                .bytecodes
                .iter()
                .map(|bytecode| bytecode.bytes.len())
                .sum::<usize>(),
        ));

        let power_of_randomness = (1..32)
            .map(|exp| {
                vec![
                    block.randomness.pow(&[exp, 0, 0, 0]);
                    block.txs.iter().map(|tx| tx.steps.len()).sum::<usize>() * STEP_HEIGHT
                ]
            })
            .collect();
        let circuit = TestCircuit::<F>::new(block, fixed_table_tags);

        let prover = MockProver::<F>::run(k, &circuit, power_of_randomness).unwrap();
        prover.verify()
    }

    pub(crate) fn run_test_circuit_incomplete_fixed_table<F: FieldExt>(
        block: Block<F>,
    ) -> Result<(), Vec<VerifyFailure>> {
        run_test_circuit(
            block,
            vec![
                FixedTableTag::Range16,
                FixedTableTag::Range32,
                FixedTableTag::Range256,
                FixedTableTag::Range512,
                FixedTableTag::SignByte,
                FixedTableTag::ResponsibleOpcode,
            ],
        )
    }

    pub(crate) fn run_test_circuit_complete_fixed_table<F: FieldExt>(
        block: Block<F>,
    ) -> Result<(), Vec<VerifyFailure>> {
        run_test_circuit(block, FixedTableTag::iterator().collect())
    }
}
