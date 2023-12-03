//! The EVM circuit implementation.

use gadgets::{
    is_zero::{IsZeroChip, IsZeroConfig, IsZeroInstruction},
    permutation::{PermutationChip, PermutationChipConfig},
    util::Expr,
};
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, SimpleFloorPlanner, Value},
    plonk::*,
    poly::Rotation,
};

mod execution;
pub mod param;
pub mod step;
pub mod table;
pub(crate) mod util;

#[cfg(test)]
pub(crate) mod test;
#[cfg(feature = "test-circuits")]
pub use self::EvmCircuit as TestEvmCircuit;
use self::{step::HasExecutionState, witness::rw::ToVec};

pub use crate::witness;
use crate::{
    evm_circuit::{
        param::{MAX_STEP_HEIGHT, STEP_STATE_HEIGHT},
        util::rlc,
    },
    table::{
        chunkctx_table::{ChunkCtxFieldTag, ChunkCtxTable},
        BlockTable, BytecodeTable, CopyTable, ExpTable, KeccakTable, LookupTable, RwTable, TxTable,
        UXTable,
    },
    util::{Challenges, SubCircuit, SubCircuitConfig},
    witness::{Chunk, RwMap},
};
use bus_mapping::{circuit_input_builder::ChunkContext, evm::OpcodeId};
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
    u8_table: UXTable<8>,
    u16_table: UXTable<16>,
    /// The execution config
    pub execution: Box<ExecutionConfig<F>>,
    // External tables
    tx_table: TxTable,
    rw_table: RwTable,
    bytecode_table: BytecodeTable,
    block_table: BlockTable,
    copy_table: CopyTable,
    keccak_table: KeccakTable,
    exp_table: ExpTable,
    chunkctx_table: ChunkCtxTable,

    // rw permutation config
    rw_permutation_config: PermutationChipConfig<F>,

    // pi for carry over previous chunk context
    pi_pre_continuity: Column<Instance>,
    // pi for carry over chunk context to the next chunk
    pi_next_continuity: Column<Instance>,
    // pi for permutation challenge
    pi_permutation_challenges: Column<Instance>,

    // chunk context related field
    chunk_index: Column<Advice>,
    chunk_index_next: Column<Advice>,
    totalchunks: Column<Advice>,
    qchunk_context: Selector,
    is_firstchunk: IsZeroConfig<F>,
    is_lastchunk: IsZeroConfig<F>,
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
    /// U8Table
    pub u8_table: UXTable<8>,
    /// U16Table
    pub u16_table: UXTable<16>,
}

impl<F: Field> SubCircuitConfig<F> for EvmCircuitConfig<F> {
    type ConfigArgs = EvmCircuitConfigArgs<F>;

    /// Configure EvmCircuitConfig
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
            u8_table,
            u16_table,
        }: Self::ConfigArgs,
    ) -> Self {
        // chunk context
        let chunk_index = meta.advice_column();
        let chunk_index_inv = meta.advice_column();
        let chunk_index_next = meta.advice_column();
        let chunk_diff = meta.advice_column();
        let totalchunks = meta.advice_column();
        let qchunk_context = meta.complex_selector();

        let fixed_table = [(); 4].map(|_| meta.fixed_column());
        let chunkctx_table = ChunkCtxTable::construct(meta);

        [
            (ChunkCtxFieldTag::CurrentChunkIndex.expr(), chunk_index),
            (ChunkCtxFieldTag::NextChunkIndex.expr(), chunk_index_next),
            (ChunkCtxFieldTag::TotalChunks.expr(), totalchunks),
        ]
        .iter()
        .for_each(|(tag_expr, value_col)| {
            meta.lookup_any("chunk context lookup", |meta| {
                let qchunk_context = meta.query_selector(qchunk_context);
                let value_col_expr = meta.query_advice(*value_col, Rotation::cur());

                vec![(
                    qchunk_context
                        * rlc::expr(
                            &[tag_expr.clone(), value_col_expr],
                            challenges.lookup_input(),
                        ),
                    rlc::expr(&chunkctx_table.table_exprs(meta), challenges.lookup_input()),
                )]
            });
        });

        let is_firstchunk = IsZeroChip::configure(
            meta,
            |meta| meta.query_selector(qchunk_context),
            |meta| meta.query_advice(chunk_index, Rotation::cur()),
            chunk_index_inv,
        );

        let is_lastchunk = IsZeroChip::configure(
            meta,
            |meta| meta.query_selector(qchunk_context),
            |meta| {
                let chunk_index = meta.query_advice(chunk_index, Rotation::cur());
                let totalchunks = meta.query_advice(totalchunks, Rotation::cur());

                totalchunks - chunk_index - 1.expr()
            },
            chunk_diff,
        );

        let execution = Box::new(ExecutionConfig::configure(
            meta,
            challenges,
            &fixed_table,
            &u8_table,
            &u16_table,
            &tx_table,
            &rw_table,
            &bytecode_table,
            &block_table,
            &copy_table,
            &keccak_table,
            &exp_table,
            &chunkctx_table,
            &is_firstchunk,
            &is_lastchunk,
        ));

        fixed_table.iter().enumerate().for_each(|(idx, &col)| {
            meta.annotate_lookup_any_column(col, || format!("fix_table_{}", idx))
        });
        tx_table.annotate_columns(meta);
        rw_table.annotate_columns(meta);
        bytecode_table.annotate_columns(meta);
        block_table.annotate_columns(meta);
        copy_table.annotate_columns(meta);
        keccak_table.annotate_columns(meta);
        exp_table.annotate_columns(meta);
        u8_table.annotate_columns(meta);
        u16_table.annotate_columns(meta);
        chunkctx_table.annotate_columns(meta);

        let rw_permutation_config = PermutationChip::configure(
            meta,
            <RwTable as LookupTable<F>>::advice_columns(&rw_table),
        );

        let pi_pre_continuity = meta.instance_column();
        let pi_next_continuity = meta.instance_column();
        let pi_permutation_challenges = meta.instance_column();

        meta.enable_equality(pi_pre_continuity);
        meta.enable_equality(pi_next_continuity);
        meta.enable_equality(pi_permutation_challenges);
        meta.enable_equality(chunk_index);
        meta.enable_equality(chunk_index_next);
        meta.enable_equality(totalchunks);

        Self {
            fixed_table,
            u8_table,
            u16_table,
            execution,
            tx_table,
            rw_table,
            bytecode_table,
            block_table,
            copy_table,
            keccak_table,
            exp_table,
            chunkctx_table,
            rw_permutation_config,
            pi_pre_continuity,
            pi_next_continuity,
            pi_permutation_challenges,
            chunk_index,
            chunk_index_next,
            totalchunks,
            is_firstchunk,
            is_lastchunk,
            qchunk_context,
        }
    }
}

/// chunk_index, chunk_index_next, totalchunk, initial_rwc, end_rwc
type AssignedChunkContextCell<F> = (
    AssignedCell<F, F>,
    AssignedCell<F, F>,
    AssignedCell<F, F>,
    AssignedCell<F, F>,
    AssignedCell<F, F>,
);

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
                for (offset, row) in std::iter::once([F::ZERO; 4])
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

    /// assign chunk context
    pub fn assignchunk_context(
        &self,
        layouter: &mut impl Layouter<F>,
        chunk_ctx: &ChunkContext,
        max_offset_index: usize,
    ) -> Result<AssignedChunkContextCell<F>, Error> {
        let (
            chunk_index_cell,
            chunk_index_next_cell,
            totalchunk_cell,
            initial_rwc_cell,
            end_rwc_cell,
        ) = self.chunkctx_table.load(layouter, chunk_ctx)?;

        let is_firstchunk = IsZeroChip::construct(self.is_firstchunk.clone());
        let is_lastchunk = IsZeroChip::construct(self.is_lastchunk.clone());
        layouter.assign_region(
            || "chunk context",
            |mut region| {
                for offset in 0..max_offset_index + 1 {
                    self.qchunk_context.enable(&mut region, offset)?;

                    region.assign_advice(
                        || "chunk_index",
                        self.chunk_index,
                        offset,
                        || Value::known(F::from(chunk_ctx.idx as u64)),
                    )?;

                    region.assign_advice(
                        || "chunk_index_next",
                        self.chunk_index_next,
                        offset,
                        || Value::known(F::from(chunk_ctx.idx as u64 + 1u64)),
                    )?;

                    region.assign_advice(
                        || "totalchunks",
                        self.totalchunks,
                        offset,
                        || Value::known(F::from(chunk_ctx.totalchunks as u64)),
                    )?;

                    is_firstchunk.assign(
                        &mut region,
                        offset,
                        Value::known(F::from(chunk_ctx.idx as u64)),
                    )?;
                    is_lastchunk.assign(
                        &mut region,
                        offset,
                        Value::known(F::from((chunk_ctx.totalchunks - chunk_ctx.idx - 1) as u64)),
                    )?;
                }
                Ok(())
            },
        )?;
        Ok((
            chunk_index_cell,
            chunk_index_next_cell,
            totalchunk_cell,
            initial_rwc_cell,
            end_rwc_cell,
        ))
    }
}

/// Tx Circuit for verifying transaction signatures
#[derive(Clone, Default, Debug)]
pub struct EvmCircuit<F: Field> {
    /// Block
    pub block: Option<Block<F>>,
    /// Chunk
    pub chunk: Option<Chunk<F>>,
    fixed_table_tags: Vec<FixedTableTag>,
}

impl<F: Field> EvmCircuit<F> {
    /// Return a new EvmCircuit
    pub fn new(block: Block<F>, chunk:Chunk<F>) -> Self {
        Self {
            block: Some(block),
            chunk: Some(chunk),
            fixed_table_tags: FixedTableTag::iter().collect(),
        }
    }
    #[cfg(any(test, feature = "test-circuits"))]
    /// Construct the EvmCircuit with only subset of Fixed table tags required by tests to save
    /// testing time
    pub(crate) fn get_test_circuit_from_block(block: Block<F>, chunk: Option<Chunk<F>>) -> Self {
        let fixed_table_tags = detect_fixed_table_tags(&block);
        Self {
            block: Some(block),
            chunk,
            fixed_table_tags,
        }
    }
    #[cfg(any(test, feature = "test-circuits"))]
    /// Calculate which rows are "actually" used in the circuit
    pub(crate) fn get_active_rows(block: &Block<F>, chunk: &Chunk<F>) -> (Vec<usize>, Vec<usize>) {
        let max_offset = Self::get_num_rows_required(block, chunk);
        // some gates are enabled on all rows
        let gates_row_ids = (0..max_offset).collect();
        // lookups are enabled at "q_step" rows and byte lookup rows
        let lookup_row_ids = (0..max_offset).collect();
        (gates_row_ids, lookup_row_ids)
    }
    /// Get the minimum number of rows required to process the block
    /// If unspecified, then compute it
    pub(crate) fn get_num_rows_required(block: &Block<F>, chunk: &Chunk<F>) -> usize {
        let evm_rows = chunk.fixed_param.max_evm_rows;
        if evm_rows == 0 {
            Self::get_min_num_rows_required(block, chunk)
        } else {
            // It must have at least one unused row.
            chunk.fixed_param.max_evm_rows + 1
        }
    }
    /// Compute the minimum number of rows required to process the block
    fn get_min_num_rows_required(block: &Block<F>, chunk: &Chunk<F>) -> usize {
        let mut num_rows = 0;
        for transaction in &block.txs {
            for step in transaction.steps() {
                if chunk.chunk_context.initial_rwc <= step.rwc.0 || step.rwc.0 <= chunk.chunk_context.end_rwc {
                    num_rows += step.execution_state().get_step_height();
                }
            }
        }

        // It must have one row for EndBlock and at least one unused one
        num_rows + 2
    }
}

impl<F: Field> SubCircuit<F> for EvmCircuit<F> {
    type Config = EvmCircuitConfig<F>;

    fn unusable_rows() -> usize {
        // Most columns are queried at MAX_STEP_HEIGHT + STEP_STATE_HEIGHT distinct rotations, so
        // returns (MAX_STEP_HEIGHT + STEP_STATE_HEIGHT + 3) unusable rows.
        MAX_STEP_HEIGHT + STEP_STATE_HEIGHT + 3
    }

    fn new_from_block(block: &witness::Block<F>, chunk: &witness::Chunk<F>) -> Self {
        Self::new(block.clone(), chunk.clone())
    }

    /// Return the minimum number of rows required to prove the block
    fn min_num_rows_block(block: &witness::Block<F>, chunk: &Chunk<F>) -> (usize, usize) {
        let num_rows_required_for_execution_steps: usize = Self::get_num_rows_required(block, chunk);
        let num_rows_required_for_fixed_table: usize = detect_fixed_table_tags(block)
            .iter()
            .map(|tag| tag.build::<F>().count())
            .sum();
        (
            std::cmp::max(
                num_rows_required_for_execution_steps,
                num_rows_required_for_fixed_table,
            ),
            chunk.fixed_param.max_evm_rows,
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
        let chunk = self.chunk.as_ref().unwrap();

        config.load_fixed_table(layouter, self.fixed_table_tags.clone())?;

        let max_offset_index = config
            .execution
            .assign_block(layouter, block, chunk, challenges)?;

        let (prevchunk_index, nextchunk_index_next, totalchunks, initial_rwc, end_rwc) =
            config.assignchunk_context(layouter, &chunk.chunk_context, max_offset_index)?;

        let (rw_rows_padding, _) = RwMap::table_assignments_padding(
            &block.rws.table_assignments(true),
            chunk.fixed_param.max_rws,
            chunk.chunk_context.is_firstchunk(),
        );
        let (
            alpha_cell,
            gamma_cell,
            prev_continuous_fingerprint_cell,
            next_continuous_fingerprint_cell,
        ) = layouter.assign_region(
            || "evm circuit",
            |mut region| {
                region.name_column(|| "EVM_pi_pre_continuity", config.pi_pre_continuity);
                region.name_column(|| "EVM_pi_next_continuity", config.pi_next_continuity);
                region.name_column(
                    || "EVM_pi_permutation_challenges",
                    config.pi_permutation_challenges,
                );
                config.rw_table.load_with_region(
                    &mut region,
                    // pass non-padding rws to `load_with_region` since it will be padding inside
                    &block.rws.table_assignments(true),
                    // align with state circuit to padding to same max_rws
                    chunk.fixed_param.max_rws,
                    chunk.chunk_context.is_firstchunk(),
                )?;
                let permutation_cells = config.rw_permutation_config.assign(
                    &mut region,
                    Value::known(chunk.permu_alpha),
                    Value::known(chunk.permu_gamma),
                    Value::known(chunk.chrono_rw_prev_fingerprint),
                    &rw_rows_padding.to2dvec(),
                    "evm circuit",
                )?;
                Ok(permutation_cells)
            },
        )?;

        // constrain permutation challenges
        [alpha_cell, gamma_cell]
            .iter()
            .enumerate()
            .try_for_each(|(i, cell)| {
                layouter.constrain_instance(cell.cell(), config.pi_permutation_challenges, i)
            })?;
        // constraints prev,next fingerprints
        [vec![
            prev_continuous_fingerprint_cell,
            prevchunk_index,
            totalchunks.clone(),
            initial_rwc,
        ]]
        .iter()
        .flatten()
        .enumerate()
        .try_for_each(|(i, cell)| {
            layouter.constrain_instance(cell.cell(), config.pi_pre_continuity, i)
        })?;
        [vec![
            next_continuous_fingerprint_cell,
            nextchunk_index_next,
            totalchunks,
            end_rwc,
        ]]
        .iter()
        .flatten()
        .enumerate()
        .try_for_each(|(i, cell)| {
            layouter.constrain_instance(cell.cell(), config.pi_next_continuity, i)
        })?;
        Ok(())
    }

    /// Compute the public inputs for this circuit.
    fn instance(&self) -> Vec<Vec<F>> {
        let _block = self.block.as_ref().unwrap();
        let chunk = self.chunk.as_ref().unwrap();

        let (rw_tablechunked_index, rw_table_totalchunks) =
            (chunk.chunk_context.idx, chunk.chunk_context.totalchunks);

        vec![
            vec![
                chunk.chrono_rw_prev_fingerprint,
                F::from(rw_tablechunked_index as u64),
                F::from(rw_table_totalchunks as u64),
                F::from(chunk.chunk_context.initial_rwc as u64),
            ],
            vec![
                chunk.chrono_rw_fingerprint,
                F::from(rw_tablechunked_index as u64) + F::ONE,
                F::from(rw_table_totalchunks as u64),
                F::from(chunk.chunk_context.end_rwc as u64),
            ],
            vec![chunk.permu_alpha, chunk.permu_gamma],
        ]
    }
}

/// create fixed_table_tags needed given witness block
pub(crate) fn detect_fixed_table_tags<F: Field>(block: &Block<F>) -> Vec<FixedTableTag> {
    let need_bitwise_lookup = block.txs.iter().any(|tx| {
        tx.steps().iter().any(|step| {
            matches!(
                step.opcode(),
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

#[cfg(any(feature = "test-util", test))]
pub(crate) mod cached {
    use super::*;
    use halo2_proofs::halo2curves::bn256::Fr;
    use lazy_static::lazy_static;

    struct Cache {
        cs: ConstraintSystem<Fr>,
        config: (EvmCircuitConfig<Fr>, Challenges),
    }

    lazy_static! {
        /// Cached values of the ConstraintSystem after the EVM Circuit configuration and the EVM
        /// Circuit configuration.  These values are calculated just once.
        static ref CACHE: Cache = {
            let mut meta = ConstraintSystem::<Fr>::default();
            let config = EvmCircuit::<Fr>::configure(&mut meta);
            Cache { cs: meta, config }
        };
    }

    /// Wrapper over the EvmCircuit that behaves the same way and also
    /// implements the halo2 Circuit trait, but reuses the precalculated
    /// results of the configuration which are cached in the public variable
    /// `CACHE`.  This wrapper is useful for testing because it allows running
    /// many unit tests while reusing the configuration step of the circuit.
    pub struct EvmCircuitCached(EvmCircuit<Fr>);

    impl Circuit<Fr> for EvmCircuitCached {
        type Config = (EvmCircuitConfig<Fr>, Challenges);
        type FloorPlanner = SimpleFloorPlanner;
        type Params = ();

        fn without_witnesses(&self) -> Self {
            Self(self.0.without_witnesses())
        }

        fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
            *meta = CACHE.cs.clone();
            CACHE.config.clone()
        }

        fn synthesize(
            &self,
            config: Self::Config,
            layouter: impl Layouter<Fr>,
        ) -> Result<(), Error> {
            self.0.synthesize(config, layouter)
        }
    }

    impl EvmCircuitCached {
        pub(crate) fn get_test_circuit_from_block(
            block: Block<Fr>,
            chunk: Option<Chunk<Fr>>,
        ) -> Self {
            Self(EvmCircuit::<Fr>::get_test_circuit_from_block(block, chunk))
        }

        pub(crate) fn instance(&self) -> Vec<Vec<Fr>> {
            self.0.instance()
        }
    }
}

// Always exported because of `EXECUTION_STATE_HEIGHT_MAP`
impl<F: Field> Circuit<F> for EvmCircuit<F> {
    type Config = (EvmCircuitConfig<F>, Challenges);
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

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
        let u8_table = UXTable::construct(meta);
        let u16_table = UXTable::construct(meta);
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
                    u8_table,
                    u16_table,
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
        let chunk = self.chunk.as_ref().unwrap();

        let (config, challenges) = config;
        let challenges = challenges.values(&mut layouter);

        config.tx_table.load(
            &mut layouter,
            &block.txs,
            chunk.fixed_param.max_txs,
            chunk.fixed_param.max_calldata,
        )?;
        block.rws.check_rw_counter_sanity();
        config
            .bytecode_table
            .load(&mut layouter, block.bytecodes.clone())?;
        config.block_table.load(&mut layouter, &block.context)?;
        config.copy_table.load(&mut layouter, block, chunk, &challenges)?;
        config
            .keccak_table
            .dev_load(&mut layouter, &block.sha3_inputs, &challenges)?;
        config.exp_table.load(&mut layouter, block, chunk)?;

        config.u8_table.load(&mut layouter)?;
        config.u16_table.load(&mut layouter)?;

        self.synthesize_sub(&config, &challenges, &mut layouter)
    }
}

#[cfg(test)]
mod evm_circuit_stats {
    use crate::{
        evm_circuit::EvmCircuit,
        test_util::CircuitTestBuilder,
        util::{unusable_rows, SubCircuit},
        witness::{block_convert, chunk_convert},
    };
    use bus_mapping::{circuit_input_builder::FixedCParams, mock::BlockData};

    use eth_types::{bytecode, geth_types::GethData};
    use halo2_proofs::{self, dev::MockProver, halo2curves::bn256::Fr};

    use mock::test_ctx::{
        helpers::{account_0_code_account_1_no_code, tx_from_1_to_0},
        TestContext,
    };

    #[test]
    fn evm_circuit_unusable_rows() {
        assert_eq!(
            EvmCircuit::<Fr>::unusable_rows(),
            unusable_rows::<Fr, EvmCircuit::<Fr>>(()),
        )
    }

    #[test]
    pub fn empty_evm_circuit_no_padding() {
        CircuitTestBuilder::new_from_test_ctx(
            TestContext::<0, 0>::new(None, |_| {}, |_, _| {}, |b, _| b).unwrap(),
        )
        .run();
    }

    #[test]
    pub fn empty_evm_circuit_with_padding() {
        CircuitTestBuilder::new_from_test_ctx(
            TestContext::<0, 0>::new(None, |_| {}, |_, _| {}, |b, _| b).unwrap(),
        )
        .block_modifier(Box::new(|block| {
            chunk.fixed_param.max_evm_rows = (1 << 18) - 100
        }))
        .run();
    }

    #[test]
    fn variadic_size_check() {
        let params = FixedCParams {
            max_evm_rows: 1 << 12,
            ..Default::default()
        };
        // Empty
        let block: GethData = TestContext::<0, 0>::new(None, |_| {}, |_, _| {}, |b, _| b)
            .unwrap()
            .into();
        let mut builder = BlockData::new_from_geth_data_with_params(block.clone(), params)
            .new_circuit_input_builder();
        builder
            .handle_block(&block.eth_block, &block.geth_traces)
            .unwrap();
        let block = block_convert::<Fr>(&builder).unwrap();
        let chunk = chunk_convert::<Fr>(&builder, 0).unwrap();
        let k = block.get_test_degree(&chunk);

        let circuit = EvmCircuit::<Fr>::get_test_circuit_from_block(block, Some(chunk));
        let instance = circuit.instance();
        let prover1 = MockProver::<Fr>::run(k, &circuit, instance).unwrap();

        let code = bytecode! {
            STOP
        };
        let block: GethData = TestContext::<2, 1>::new(
            None,
            account_0_code_account_1_no_code(code),
            tx_from_1_to_0,
            |b, _| b,
        )
        .unwrap()
        .into();
        let mut builder = BlockData::new_from_geth_data_with_params(block.clone(), params)
            .new_circuit_input_builder();
        builder
            .handle_block(&block.eth_block, &block.geth_traces)
            .unwrap();
        let block = block_convert::<Fr>(&builder).unwrap();
        let chunk = chunk_convert::<Fr>(&builder, 0).unwrap();
        let k = block.get_test_degree(&chunk);
        let circuit = EvmCircuit::<Fr>::get_test_circuit_from_block(block, Some(chunk));
        let instance = circuit.instance();
        let prover2 = MockProver::<Fr>::run(k, &circuit, instance).unwrap();

        assert_eq!(prover1.fixed().len(), prover2.fixed().len());
        prover1
            .fixed()
            .iter()
            .zip(prover2.fixed().iter())
            .enumerate()
            .for_each(|(i, (f1, f2))| {
                assert_eq!(
                    f1, f2,
                    "at index {}. Usually it happened when mismatch constant constraint, e.g. region.constrain_constant() are calling in-consisntent", i
                )
            });
        assert_eq!(prover1.fixed(), prover2.fixed());
        assert_eq!(prover1.permutation(), prover2.permutation());
    }
}
