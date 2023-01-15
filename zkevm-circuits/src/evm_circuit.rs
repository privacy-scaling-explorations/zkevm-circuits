//! The EVM circuit implementation.

#![allow(missing_docs)]
use halo2_proofs::{
    circuit::{Layouter, Value},
    plonk::*,
};

mod execution;
pub mod param;
pub(crate) mod step;
pub mod table;
/// evm circuit tests
#[cfg(any(feature = "test", test))]
pub mod test;
pub(crate) mod util;

use crate::table::{BlockTable, BytecodeTable, CopyTable, ExpTable, KeccakTable, RwTable, TxTable};
use crate::util::{log2_ceil, Challenges, SubCircuit, SubCircuitConfig};
pub use crate::witness;
use bus_mapping::evm::OpcodeId;
use eth_types::Field;
use execution::ExecutionConfig;
use itertools::Itertools;
use strum::IntoEnumIterator;
use table::FixedTableTag;
use witness::Block;

/// EvmCircuitConfig implements verification of execution trace of a block.
#[derive(Clone, Debug)]
pub struct EvmCircuitConfig<F> {
    fixed_table: [Column<Fixed>; 4],
    byte_table: [Column<Fixed>; 1],
    pub(crate) execution: Box<ExecutionConfig<F>>,
    // External tables
    tx_table: TxTable,
    rw_table: RwTable,
    bytecode_table: BytecodeTable,
    block_table: BlockTable,
    copy_table: CopyTable,
    keccak_table: KeccakTable,
    exp_table: ExpTable,
}

/// Circuit configuration arguments
pub struct EvmCircuitConfigArgs<F: Field> {
    /// Challenge
    pub challenges: Challenges<Expression<F>>,
    /// TxTable
    pub tx_table: TxTable,
    /// RwTable
    pub rw_table: RwTable,
    /// BytecodeTable
    pub bytecode_table: BytecodeTable,
    /// BlockTable
    pub block_table: BlockTable,
    /// CopyTable
    pub copy_table: CopyTable,
    /// KeccakTable
    pub keccak_table: KeccakTable,
    /// ExpTable
    pub exp_table: ExpTable,
}

impl<F: Field> SubCircuitConfig<F> for EvmCircuitConfig<F> {
    type ConfigArgs = EvmCircuitConfigArgs<F>;

    /// Configure EvmCircuitConfig
    #[allow(clippy::too_many_arguments)]
    fn new(
        meta: &mut ConstraintSystem<F>,
        Self::ConfigArgs {
            challenges,
            tx_table,
            rw_table,
            bytecode_table,
            block_table,
            copy_table,
            keccak_table,
            exp_table,
        }: Self::ConfigArgs,
    ) -> Self {
        let fixed_table = [(); 4].map(|_| meta.fixed_column());
        let byte_table = [(); 1].map(|_| meta.fixed_column());
        let execution = Box::new(ExecutionConfig::configure(
            meta,
            challenges,
            &fixed_table,
            &byte_table,
            &tx_table,
            &rw_table,
            &bytecode_table,
            &block_table,
            &copy_table,
            &keccak_table,
            &exp_table,
        ));

        Self {
            fixed_table,
            byte_table,
            execution,
            tx_table,
            rw_table,
            bytecode_table,
            block_table,
            copy_table,
            keccak_table,
            exp_table,
        }
    }
}

impl<F: Field> EvmCircuitConfig<F> {
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
                    .chain(fixed_table_tags.iter().flat_map(|tag| tag.build()))
                    .enumerate()
                {
                    for (column, value) in self.fixed_table.iter().zip_eq(row) {
                        region.assign_fixed(|| "", *column, offset, || Value::known(value))?;
                    }
                }

                Ok(())
            },
        )
    }

    /// Load byte table
    pub fn load_byte_table(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_region(
            || "byte table",
            |mut region| {
                for offset in 0..256 {
                    region.assign_fixed(
                        || "",
                        self.byte_table[0],
                        offset,
                        || Value::known(F::from(offset as u64)),
                    )?;
                }

                Ok(())
            },
        )
    }

    /// Calculate which rows are "actually" used in the circuit
    pub fn get_active_rows(&self, block: &Block<F>) -> (Vec<usize>, Vec<usize>) {
        let max_offset = self.get_num_rows_required(block);
        // some gates are enabled on all rows
        let gates_row_ids = (0..max_offset).collect();
        // lookups are enabled at "q_step" rows and byte lookup rows
        let lookup_row_ids = (0..max_offset).collect();
        (gates_row_ids, lookup_row_ids)
    }

    pub fn get_num_rows_required(&self, block: &Block<F>) -> usize {
        // Start at 1 so we can be sure there is an unused `next` row available
        let mut num_rows = 1;
        let evm_rows = block.evm_circuit_pad_to;
        if evm_rows == 0 {
            for transaction in &block.txs {
                for step in &transaction.steps {
                    num_rows += self.execution.get_step_height(step.execution_state);
                }
            }
            num_rows += 1; // EndBlock
        } else {
            num_rows += block.evm_circuit_pad_to;
        }
        num_rows
    }
}

/// Tx Circuit for verifying transaction signatures
#[derive(Clone, Default, Debug)]
pub struct EvmCircuit<F: Field> {
    /// Block
    pub block: Option<Block<F>>,
    fixed_table_tags: Vec<FixedTableTag>,
}

impl<F: Field> EvmCircuit<F> {
    /// Return a new EvmCircuit
    pub fn new(block: Block<F>) -> Self {
        Self {
            block: Some(block),
            fixed_table_tags: FixedTableTag::iter().collect(),
        }
    }

    // get_required_num_rows of EvmCircuit
    pub fn get_num_rows_required(block: &Block<F>) -> usize {
        let mut cs = ConstraintSystem::default();
        let config = EvmCircuit::<F>::configure(&mut cs);
        config.0.get_num_rows_required(block)
    }
}

impl<F: Field> SubCircuit<F> for EvmCircuit<F> {
    type Config = EvmCircuitConfig<F>;

    fn new_from_block(block: &witness::Block<F>) -> Self {
        Self::new(block.clone())
    }

    /// Return the minimum number of rows required to prove the block
    fn min_num_rows_block(block: &witness::Block<F>) -> (usize, usize) {
        let num_rows_required_for_execution_steps: usize =
            EvmCircuit::<F>::get_num_rows_required(block);
        let num_rows_required_for_fixed_table: usize = detect_fixed_table_tags(block)
            .iter()
            .map(|tag| tag.build::<F>().count())
            .sum();
        (
            std::cmp::max(
                num_rows_required_for_execution_steps,
                num_rows_required_for_fixed_table,
            ),
            block.evm_circuit_pad_to,
        )
    }

    /// Make the assignments to the EvmCircuit
    fn synthesize_sub(
        &self,
        config: &Self::Config,
        challenges: &Challenges<Value<F>>,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        let block = self.block.as_ref().unwrap();

        config.load_fixed_table(layouter, self.fixed_table_tags.clone())?;
        config.load_byte_table(layouter)?;
        config.execution.assign_block(layouter, block, challenges)
    }
}

/// create fixed_table_tags needed given witness block
pub(crate) fn detect_fixed_table_tags<F: Field>(block: &Block<F>) -> Vec<FixedTableTag> {
    let need_bitwise_lookup = block.txs.iter().any(|tx| {
        tx.steps.iter().any(|step| {
            matches!(
                step.opcode,
                Some(OpcodeId::AND)
                    | Some(OpcodeId::OR)
                    | Some(OpcodeId::XOR)
                    | Some(OpcodeId::NOT)
            )
        })
    });
    FixedTableTag::iter()
        .filter(|t| {
            !matches!(
                t,
                FixedTableTag::BitwiseAnd | FixedTableTag::BitwiseOr | FixedTableTag::BitwiseXor
            ) || need_bitwise_lookup
        })
        .collect()
}

// TODO: Move this `impl` into test mod later.
// Keeping this outsize of test-mode is for that the get_required_num_rows of
// EvmCircuit relies on EvmCircuit::<F>::configure.
use halo2_proofs::{
    circuit::SimpleFloorPlanner,
    plonk::{Circuit, ConstraintSystem, Error},
};
impl<F: Field> Circuit<F> for EvmCircuit<F> {
    type Config = (EvmCircuitConfig<F>, Challenges);
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let tx_table = TxTable::construct(meta);
        let rw_table = RwTable::construct(meta);
        let bytecode_table = BytecodeTable::construct(meta);
        let block_table = BlockTable::construct(meta);
        let q_copy_table = meta.fixed_column();
        let copy_table = CopyTable::construct(meta, q_copy_table);
        let keccak_table = KeccakTable::construct(meta);
        let exp_table = ExpTable::construct(meta);
        let challenges = Challenges::construct(meta);
        let challenges_expr = challenges.exprs(meta);

        (
            EvmCircuitConfig::new(
                meta,
                EvmCircuitConfigArgs {
                    challenges: challenges_expr,
                    tx_table,
                    rw_table,
                    bytecode_table,
                    block_table,
                    copy_table,
                    keccak_table,
                    exp_table,
                },
            ),
            challenges,
        )
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let block = self.block.as_ref().unwrap();

        let (config, challenges) = config;
        let challenges = challenges.values(&mut layouter);

        config.tx_table.load(
            &mut layouter,
            &block.txs,
            block.circuits_params.max_txs,
            &challenges,
        )?;
        block.rws.check_rw_counter_sanity();
        config.rw_table.load(
            &mut layouter,
            &block.rws.table_assignments(),
            block.circuits_params.max_rws,
            challenges.evm_word(),
        )?;
        config
            .bytecode_table
            .load(&mut layouter, block.bytecodes.values(), &challenges)?;
        config
            .block_table
            .load(&mut layouter, &block.context, challenges.evm_word())?;
        config.copy_table.load(&mut layouter, block, &challenges)?;
        config
            .keccak_table
            .dev_load(&mut layouter, &block.sha3_inputs, &challenges)?;
        config.exp_table.load(&mut layouter, block)?;

        self.synthesize_sub(&config, &challenges, &mut layouter)
    }
}
