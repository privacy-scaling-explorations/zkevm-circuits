//! This module contains the CircuitInputBuilder, which is an object that takes
//! types from geth / web3 and outputs the circuit inputs.

mod access;
mod block;
mod call;
mod chunk;
mod execution;
mod input_state_ref;
#[cfg(test)]
mod tracer_tests;
mod transaction;
mod withdrawal;

use self::{access::gen_state_access_trace, chunk::Chunk};
use crate::{
    error::Error,
    evm::opcodes::{gen_associated_ops, gen_associated_steps},
    operation::{
        CallContextField, Op, Operation, OperationContainer, PaddingOp, RWCounter, StartOp,
        StepStateField, StepStateOp, RW,
    },
    rpc::GethClient,
    state_db::{self, CodeDB, StateDB},
};
pub use access::{Access, AccessSet, AccessValue, CodeSource};
pub use block::{Block, BlockContext};
pub use call::{Call, CallContext, CallKind};
pub use chunk::ChunkContext;
use core::fmt::Debug;
use eth_types::{
    self, geth_types,
    sign_types::{pk_bytes_le, pk_bytes_swap_endianness, SignData},
    Address, GethExecStep, GethExecTrace, ToWord, Word,
};
use ethers_providers::JsonRpcClient;
pub use execution::{
    CopyDataType, CopyEvent, CopyStep, ExecState, ExecStep, ExpEvent, ExpStep, NumberOrHash,
    PrecompileEvent, PrecompileEvents, N_BYTES_PER_PAIR, N_PAIRING_PER_OP,
};
pub use input_state_ref::CircuitInputStateRef;
use itertools::Itertools;
use log::warn;
use std::{
    collections::{HashMap, HashSet},
    ops::Deref,
};
pub use transaction::{Transaction, TransactionContext};
pub use withdrawal::{Withdrawal, WithdrawalContext};

/// number of execution state fields
pub const N_EXEC_STATE: usize = 10;

/// Runtime Config
///
/// Default to mainnet block
#[derive(Debug, Clone, Copy)]
pub struct FeatureConfig {
    /// Zero difficulty
    pub zero_difficulty: bool,
    /// Free first transaction
    pub free_first_tx: bool,
    /// Enable EIP1559
    pub enable_eip1559: bool,
    /// Allow invalid transactions to be included in a block
    ///
    /// Transactions with mismatched nonce, insufficient gas limit, or insufficient balance
    /// shouldn't be included in a mainnet block. However, rollup developers might want to
    /// include invalid tx in the L2 block to support forced exit feature.
    pub invalid_tx: bool,
}

impl Default for FeatureConfig {
    fn default() -> Self {
        Self {
            zero_difficulty: true,
            free_first_tx: false,
            enable_eip1559: true,
            invalid_tx: false,
        }
    }
}

impl FeatureConfig {
    /// Check if we are mainnet config
    pub fn is_mainnet(&self) -> bool {
        self.zero_difficulty && !self.free_first_tx && self.enable_eip1559 && !self.invalid_tx
    }
}

// RW_BUFFER_SIZE need to set to cover max rwc row contributed by a ExecStep
const RW_BUFFER_SIZE: usize = 30;

/// Circuit Setup Parameters
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct FixedCParams {
    ///
    pub total_chunks: usize,
    /// Maximum number of rw operations in the state circuit (RwTable length /
    /// number of rows). This must be at least the number of rw operations
    /// + 1, in order to allocate at least a Start row.
    pub max_rws: usize,
    // TODO: evm_rows: Maximum number of rows in the EVM Circuit
    /// Maximum number of txs in the Tx Circuit
    pub max_txs: usize,
    /// Maximum number of withdrawals in the Withdrawal Circuit
    pub max_withdrawals: usize,
    /// Maximum number of bytes from all txs calldata in the Tx Circuit
    pub max_calldata: usize,
    /// Max amount of rows that the CopyCircuit can have.
    pub max_copy_rows: usize,
    /// Max number of steps that the ExpCircuit can have. Each step is further
    /// expressed in 7 rows
    pub max_exp_steps: usize,
    /// Maximum number of bytes supported in the Bytecode Circuit
    pub max_bytecode: usize,
    /// Pad evm circuit number of rows.
    /// When 0, the EVM circuit number of rows will be dynamically calculated,
    /// so the same circuit will not be able to proof different witnesses.
    /// In this case it will contain as many rows for all steps + 1 row
    /// for EndBlock.
    pub max_evm_rows: usize,
    /// Pad the keccak circuit with this number of invocations to a static
    /// capacity.  Number of keccak_f that the Keccak circuit will support.
    /// When 0, the Keccak circuit number of rows will be dynamically
    /// calculated, so the same circuit will not be able to prove different
    /// witnesses.
    pub max_keccak_rows: usize,
    /// This number indicate what 100% usage means, for example if we can support up to 2
    /// ecPairing inside circuit, and max_vertical_circuit_rows is set to 1_000_000,
    /// then if there is 1 ecPairing in the input, we will return 500_000 as the "row usage"
    /// for the ec circuit.
    pub max_vertical_circuit_rows: usize,
}

/// Unset Circuits Parameters
///
/// To reduce the testing overhead, we determine the parameters by the testing inputs.
/// A new [`FixedCParams`] will be computed from the generated circuit witness.
#[derive(Debug, Clone, Copy)]
pub struct DynamicCParams {
    /// Toatal number of chunks
    pub total_chunks: usize,
}
/// Circuit Setup Parameters. These can be fixed/concrete or unset/dynamic.
pub trait CircuitsParams: Debug + Copy {
    /// Return the total number of chunks
    fn total_chunks(&self) -> usize;
    /// Set total number of chunks
    fn set_total_chunk(&mut self, total_chunks: usize);
    /// Return the maximun Rw
    fn max_rws(&self) -> Option<usize>;
}

impl CircuitsParams for FixedCParams {
    fn total_chunks(&self) -> usize {
        self.total_chunks
    }
    fn set_total_chunk(&mut self, total_chunks: usize) {
        self.total_chunks = total_chunks;
    }
    fn max_rws(&self) -> Option<usize> {
        Some(self.max_rws)
    }
}
impl CircuitsParams for DynamicCParams {
    fn total_chunks(&self) -> usize {
        self.total_chunks
    }
    fn set_total_chunk(&mut self, total_chunks: usize) {
        self.total_chunks = total_chunks;
    }
    fn max_rws(&self) -> Option<usize> {
        None
    }
}

impl Default for DynamicCParams {
    fn default() -> Self {
        DynamicCParams { total_chunks: 1 }
    }
}
impl Default for FixedCParams {
    /// Default values for most of the unit tests of the Circuit Parameters
    fn default() -> Self {
        FixedCParams {
            total_chunks: 1,
            max_rws: 1000,
            max_txs: 1,
            max_withdrawals: 1,
            max_calldata: 256,
            // TODO: Check whether this value is correct or we should increase/decrease based on
            // this lib tests
            max_copy_rows: 1000,
            max_exp_steps: 1000 / 7, // exp_circuit::OFFSET_INCREMENT = 7
            max_bytecode: 512,
            max_evm_rows: 0,
            max_keccak_rows: 0,
            max_vertical_circuit_rows: 0,
        }
    }
}

/// Builder to generate a complete circuit input from data gathered from a geth
/// instance. This structure is the centre of the crate and is intended to be
/// the only entry point to it. The `CircuitInputBuilder` works in several
/// steps:
///
/// 1. Take a [`eth_types::Block`] to build the circuit input associated with
/// the block. 2. For each [`eth_types::Transaction`] in the block, take the
/// [`eth_types::GethExecTrace`] to build the circuit input associated with
/// each transaction, and the bus-mapping operations associated with each
/// [`eth_types::GethExecStep`] in the [`eth_types::GethExecTrace`]. 3. If `Rw`s
/// generated during Transactions exceed the `max_rws` threshold, seperate witness
/// into multiple chunks.
///
/// The generated bus-mapping operations are:
/// [`StackOp`](crate::operation::StackOp)s,
/// [`MemoryOp`](crate::operation::MemoryOp)s and
/// [`StorageOp`](crate::operation::StorageOp), which correspond to each
/// [`OpcodeId`](crate::evm::OpcodeId)s used in each `ExecTrace` step so that
/// the State Proof witnesses are already generated on a structured manner and
/// ready to be added into the State circuit.
#[derive(Debug, Clone)]
pub struct CircuitInputBuilder<C: CircuitsParams> {
    /// StateDB key-value DB
    pub sdb: StateDB,
    /// Map of account codes by code hash
    pub code_db: CodeDB,
    /// Block
    pub block: Block,
    /// Chunk
    pub chunks: Vec<Chunk>,
    /// Block Context
    pub block_ctx: BlockContext,
    /// Chunk Context
    pub chunk_ctx: ChunkContext,
    /// Circuits Setup Parameters before chunking
    pub circuits_params: C,
    /// Feature config
    pub feature_config: FeatureConfig,
}

impl<'a, C: CircuitsParams> CircuitInputBuilder<C> {
    /// Create a new CircuitInputBuilder from the given `eth_block` and
    /// `constants`.
    pub fn new(
        sdb: StateDB,
        code_db: CodeDB,
        block: Block,
        params: C,
        feature_config: FeatureConfig,
    ) -> Self {
        let total_chunks = params.total_chunks();
        let chunks = vec![Chunk::default(); total_chunks];
        Self {
            sdb,
            code_db,
            block,
            chunks,
            block_ctx: BlockContext::new(),
            chunk_ctx: ChunkContext::new(total_chunks),
            circuits_params: params,
            feature_config,
        }
    }

    /// Set the total number of chunks for existing CircuitInputBuilder,
    /// API for chunking the existing tests then run with a specific chunk
    pub fn set_total_chunk(&mut self, total_chunks: usize) {
        self.circuits_params.set_total_chunk(total_chunks);
        self.chunks = vec![Chunk::default(); total_chunks];
        self.chunk_ctx.total_chunks = total_chunks;
    }

    /// Obtain a mutable reference to the state that the `CircuitInputBuilder`
    /// maintains, contextualized to a particular transaction and a
    /// particular execution step in that transaction.
    pub fn state_ref(
        &'a mut self,
        tx: &'a mut Transaction,
        tx_ctx: &'a mut TransactionContext,
    ) -> CircuitInputStateRef {
        CircuitInputStateRef {
            sdb: &mut self.sdb,
            code_db: &mut self.code_db,
            block: &mut self.block,
            block_ctx: &mut self.block_ctx,
            chunk_ctx: &mut self.chunk_ctx,
            tx,
            tx_ctx,
            max_rws: self.circuits_params.max_rws(),
        }
    }

    /// Create a new Transaction from a [`eth_types::Transaction`].
    pub fn new_tx(
        &mut self,
        id: u64,
        eth_tx: &eth_types::Transaction,
        is_success: bool,
    ) -> Result<Transaction, Error> {
        let call_id = self.block_ctx.rwc.0;

        self.block_ctx.call_map.insert(
            call_id,
            (
                eth_tx
                    .transaction_index
                    .ok_or(Error::EthTypeError(eth_types::Error::IncompleteBlock))?
                    .as_u64() as usize,
                0,
            ),
        );

        Transaction::new(
            id,
            call_id,
            &self.sdb,
            &mut self.code_db,
            eth_tx,
            is_success,
        )
    }

    /// Iterate over all generated CallContext RwCounterEndOfReversion
    /// operations and set the correct value. This is required because when we
    /// generate the RwCounterEndOfReversion operation in
    /// `gen_associated_ops` we don't know yet which value it will take,
    /// so we put a placeholder; so we do it here after the values are known.
    pub fn set_value_ops_call_context_rwc_eor(&mut self) {
        for oper in self.block.container.call_context.iter_mut() {
            let op = oper.op_mut();
            if matches!(op.field, CallContextField::RwCounterEndOfReversion) {
                let (tx_idx, call_idx) = self
                    .block_ctx
                    .call_map
                    .get(&op.call_id)
                    .expect("call_id not found in call_map");
                op.value = self.block.txs[*tx_idx].calls()[*call_idx]
                    .rw_counter_end_of_reversion
                    .into();
            }
        }
    }

    // chunking and mutable bumping chunk_ctx once condition match
    // return true on bumping to next chunk
    fn check_and_chunk(
        &mut self,
        geth_trace: &GethExecTrace,
        tx: Transaction,
        tx_ctx: TransactionContext,
        next_geth_step: Option<(usize, &GethExecStep)>,
        last_call: Option<Call>,
    ) -> Result<bool, Error> {
        // we dont chunk if
        // 1. on last chunk
        // 2. still got some buffer room before max_rws
        let Some(max_rws) = self.circuits_params.max_rws() else {
            // terminiate earlier due to no max_rws
            return Ok(false);
        };

        if self.chunk_ctx.is_last_chunk() || self.chunk_rws() + RW_BUFFER_SIZE < max_rws {
            return Ok(false);
        };

        // Optain the first op of the next GethExecStep, for fixed case also lookahead
        let (mut cib, mut tx, mut tx_ctx) = (self.clone(), tx, tx_ctx);
        let mut cib_ref = cib.state_ref(&mut tx, &mut tx_ctx);
        let mut next_ops = if let Some((i, step)) = next_geth_step {
            log::trace!("chunk at {}th opcode {:?} ", i, step.op);
            gen_associated_ops(&step.op, &mut cib_ref, &geth_trace.struct_logs[i..])?.remove(0)
        } else {
            log::trace!("chunk at EndTx");
            gen_associated_steps(&mut cib_ref, ExecState::EndTx)?
        };

        let last_copy = self.block.copy_events.len();
        // Generate EndChunk and proceed to the next if it's not the last chunk
        // Set next step pre-state as end_chunk state
        self.set_end_chunk(&next_ops, Some(&tx));

        // need to update next_ops.rwc to catch block_ctx.rwc in `set_end_chunk`
        next_ops.rwc = self.block_ctx.rwc;

        // tx.id start from 1, so it's equivalent to `next_tx_index`
        self.commit_chunk_ctx(true, tx.id as usize, last_copy, last_call);
        self.set_begin_chunk(&next_ops, Some(&tx));

        Ok(true)
    }

    /// Handle a transaction with its corresponding execution trace to generate
    /// all the associated operations.  Each operation is registered in
    /// `self.block.container`, and each step stores the
    /// [`OperationRef`](crate::exec_trace::OperationRef) to each of the
    /// generated operations.
    /// When dynamic builder handles Tx with is_chuncked = false, we don't chunk
    /// When fixed builder handles Tx with is_chuncked = true, we chunk
    fn handle_tx(
        &mut self,
        eth_tx: &eth_types::Transaction,
        geth_trace: &GethExecTrace,
        is_last_tx: bool,
        tx_index: u64,
    ) -> Result<(ExecStep, Option<Call>), Error> {
        let mut tx = self.new_tx(tx_index, eth_tx, !geth_trace.failed)?;
        let mut tx_ctx = TransactionContext::new(eth_tx, geth_trace, is_last_tx)?;

        let res = if !geth_trace.invalid {
            // Generate BeginTx step
            let begin_tx_step = gen_associated_steps(
                &mut self.state_ref(&mut tx, &mut tx_ctx),
                ExecState::BeginTx,
            )?;
            let mut last_call = Some(tx.calls().get(begin_tx_step.call_index).unwrap().clone());
            tx.steps_mut().push(begin_tx_step);

            let mut trace = geth_trace.struct_logs.iter().enumerate().peekable();
            while let Some((peek_i, peek_step)) = trace.peek() {
                // Check the peek step and chunk if needed
                self.check_and_chunk(
                    geth_trace,
                    tx.clone(),
                    tx_ctx.clone(),
                    Some((*peek_i, peek_step)),
                    last_call.clone(),
                )?;
                // Proceed to the next step
                let (i, step) = trace.next().expect("Peeked step should exist");
                log::trace!(
                    "handle {}th opcode {:?} {:?} rws = {:?}",
                    i,
                    step.op,
                    step,
                    self.chunk_rws()
                );
                let exec_steps = gen_associated_ops(
                    &step.op,
                    &mut self.state_ref(&mut tx, &mut tx_ctx),
                    &geth_trace.struct_logs[i..],
                )?;
                last_call = exec_steps
                    .last()
                    .map(|step| tx.calls().get(step.call_index).unwrap().clone());
                tx.steps_mut().extend(exec_steps);
            }

            // Peek the end_tx_step
            self.check_and_chunk(
                geth_trace,
                tx.clone(),
                tx_ctx.clone(),
                None,
                last_call.clone(),
            )?;

            // Generate EndTx step
            let end_tx_step =
                gen_associated_steps(&mut self.state_ref(&mut tx, &mut tx_ctx), ExecState::EndTx)?;
            self.sdb.clear_transient_storage();
            tx.steps_mut().push(end_tx_step.clone());
            (end_tx_step, last_call)
        } else if self.feature_config.invalid_tx {
            // Generate InvalidTx step
            let invalid_tx_step = gen_associated_steps(
                &mut self.state_ref(&mut tx, &mut tx_ctx),
                ExecState::InvalidTx,
            )?;
            tx.steps_mut().push(invalid_tx_step.clone());
            // Peek the end_tx_step
            let is_chunk =
                self.check_and_chunk(geth_trace, tx.clone(), tx_ctx.clone(), None, None)?;
            if is_chunk {
                // TODO we dont support chunk after invalid_tx
                // becasuse begin_chunk will constraints what next step execution state.
                // And for next step either begin_tx or invalid_tx will both failed because
                // begin_tx/invalid_tx define new execution state.
                unimplemented!("dont support invalid_tx with multiple chunks")
            }

            (invalid_tx_step, None)
        } else {
            panic!("invalid tx support not enabled")
        };

        self.sdb.commit_tx();
        self.block.txs.push(tx);

        Ok(res)
    }

    // generate chunk related steps
    fn gen_chunk_associated_steps(
        &mut self,
        step: &mut ExecStep,
        rw: RW,
        tx: Option<&Transaction>,
    ) {
        let mut dummy_tx = Transaction::default();
        let mut dummy_tx_ctx = TransactionContext::default();

        let rw_counters = (0..N_EXEC_STATE)
            .map(|_| self.block_ctx.rwc.inc_pre())
            .collect::<Vec<RWCounter>>();
        // just bump rwc in chunk_ctx as block_ctx rwc to assure same delta apply
        let rw_counters_inner_chunk = (0..N_EXEC_STATE)
            .map(|_| self.chunk_ctx.rwc.inc_pre())
            .collect::<Vec<RWCounter>>();

        let tags = {
            let state = self.state_ref(&mut dummy_tx, &mut dummy_tx_ctx);
            let last_call = tx
                .map(|tx| tx.calls()[step.call_index].clone())
                .or_else(|| state.block.txs.last().map(|tx| tx.calls[0].clone()))
                .unwrap();
            [
                (StepStateField::CodeHash, last_call.code_hash.to_word()),
                (StepStateField::CallID, Word::from(last_call.call_id)),
                (StepStateField::IsRoot, Word::from(last_call.is_root as u64)),
                (
                    StepStateField::IsCreate,
                    Word::from(last_call.is_create() as u64),
                ),
                (StepStateField::ProgramCounter, Word::from(step.pc)),
                (
                    StepStateField::StackPointer,
                    Word::from(step.stack_pointer()),
                ),
                (StepStateField::GasLeft, Word::from(step.gas_left)),
                (
                    StepStateField::MemoryWordSize,
                    Word::from(step.memory_word_size()),
                ),
                (
                    StepStateField::ReversibleWriteCounter,
                    Word::from(step.reversible_write_counter),
                ),
                (StepStateField::LogID, Word::from(step.log_id)),
            ]
        };

        debug_assert_eq!(N_EXEC_STATE, tags.len());
        let state = self.state_ref(&mut dummy_tx, &mut dummy_tx_ctx);

        tags.iter()
            .zip_eq(rw_counters)
            .zip_eq(rw_counters_inner_chunk)
            .for_each(|(((tag, value), rw_counter), inner_rw_counter)| {
                push_op(
                    &mut state.block.container,
                    step,
                    rw_counter,
                    inner_rw_counter,
                    rw,
                    StepStateOp {
                        field: tag.clone(),
                        value: *value,
                    },
                );
            });
    }

    /// Set the end status of a chunk including the current globle rwc
    /// and commit the current chunk context, proceed to the next chunk
    /// if needed
    pub fn commit_chunk_ctx(
        &mut self,
        to_next: bool,
        next_tx_index: usize,
        next_copy_index: usize,
        last_call: Option<Call>,
    ) {
        self.chunk_ctx.end_rwc = self.block_ctx.rwc.0;
        self.chunk_ctx.end_tx_index = next_tx_index;
        self.chunk_ctx.end_copy_index = next_copy_index;
        self.cur_chunk_mut().ctx = self.chunk_ctx.clone();
        if to_next {
            // add `-1` to include previous set and deal with transaction cross-chunk case
            self.chunk_ctx
                .bump(self.block_ctx.rwc.0, next_tx_index - 1, next_copy_index);
            self.cur_chunk_mut().prev_last_call = last_call;
        }
    }

    fn set_begin_chunk(&mut self, first_step: &ExecStep, tx: Option<&Transaction>) {
        let mut begin_chunk = ExecStep {
            exec_state: ExecState::BeginChunk,
            rwc: first_step.rwc,
            gas_left: first_step.gas_left,
            call_index: first_step.call_index,
            ..ExecStep::default()
        };
        self.gen_chunk_associated_steps(&mut begin_chunk, RW::READ, tx);
        self.chunks[self.chunk_ctx.idx].begin_chunk = Some(begin_chunk);
    }

    fn set_end_chunk(&mut self, next_step: &ExecStep, tx: Option<&Transaction>) {
        let mut end_chunk = ExecStep {
            exec_state: ExecState::EndChunk,
            rwc: next_step.rwc,
            rwc_inner_chunk: next_step.rwc_inner_chunk,
            gas_left: next_step.gas_left,
            call_index: next_step.call_index,
            ..ExecStep::default()
        };
        self.gen_chunk_associated_steps(&mut end_chunk, RW::WRITE, tx);
        self.gen_chunk_padding(&mut end_chunk);
        self.chunks[self.chunk_ctx.idx].end_chunk = Some(end_chunk);
    }

    fn gen_chunk_padding(&mut self, step: &mut ExecStep) {
        // rwc index start from 1
        let end_rwc = self.chunk_ctx.rwc.0;
        let total_rws = end_rwc - 1;
        let max_rws = self.cur_chunk().fixed_param.max_rws;

        assert!(
            total_rws < max_rws,
            "total_rws <= max_rws, total_rws={}, max_rws={}",
            total_rws,
            max_rws
        );

        let mut padding = step.clone();
        padding.exec_state = ExecState::Padding;
        padding.bus_mapping_instance = vec![]; // there is no rw in padding step

        if self.chunk_ctx.is_first_chunk() {
            push_op(
                &mut self.block.container,
                step,
                RWCounter(1),
                RWCounter(1),
                RW::READ,
                StartOp {},
            );
        }

        if max_rws - total_rws > 1 {
            let (padding_start, padding_end) = (total_rws + 1, max_rws - 1);
            push_op(
                &mut self.block.container,
                step,
                RWCounter(padding_start),
                RWCounter(padding_start),
                RW::READ,
                PaddingOp {},
            );
            if padding_end != padding_start {
                push_op(
                    &mut self.block.container,
                    step,
                    RWCounter(padding_end),
                    RWCounter(padding_end),
                    RW::READ,
                    PaddingOp {},
                );
            }
        }
        self.chunks[self.chunk_ctx.idx].padding = Some(padding);
    }

    /// Get the i-th mutable chunk
    pub fn get_chunk_mut(&mut self, i: usize) -> &mut Chunk {
        self.chunks.get_mut(i).expect("Chunk does not exist")
    }

    /// Get the i-th chunk
    pub fn get_chunk(&self, i: usize) -> Chunk {
        self.chunks.get(i).expect("Chunk does not exist").clone()
    }

    /// Get the current chunk
    pub fn cur_chunk(&self) -> Chunk {
        self.chunks[self.chunk_ctx.idx].clone()
    }

    /// Get a mutable reference of current chunk
    pub fn cur_chunk_mut(&mut self) -> &mut Chunk {
        &mut self.chunks[self.chunk_ctx.idx]
    }

    /// Get the previous chunk
    pub fn prev_chunk(&self) -> Option<Chunk> {
        if self.chunk_ctx.idx == 0 {
            return None;
        }
        self.chunks.get(self.chunk_ctx.idx - 1).cloned()
    }

    /// Total Rw in this chunk
    pub fn chunk_rws(&self) -> usize {
        self.chunk_ctx.rwc.0 - 1
    }
}

impl CircuitInputBuilder<FixedCParams> {
    /// First part of handle_block, only called by fixed Builder
    pub fn begin_handle_block(
        &mut self,
        eth_block: &EthBlock,
        geth_traces: &[eth_types::GethExecTrace],
    ) -> Result<(Option<ExecStep>, Option<Call>), Error> {
        assert!(
            self.circuits_params.max_rws().unwrap_or_default() > self.last_exec_step_rws_reserved(),
            "Fixed max_rws not enough for rws reserve"
        );

        // accumulates gas across all txs in the block
        let mut res = eth_block
            .transactions
            .iter()
            .enumerate()
            .map(|(idx, tx)| {
                let geth_trace = &geth_traces[idx];
                // Transaction index starts from 1
                let tx_id = idx + 1;
                self.handle_tx(
                    tx,
                    geth_trace,
                    tx_id == eth_block.transactions.len(),
                    tx_id as u64,
                )
                .map(|(exec_step, last_call)| (Some(exec_step), last_call))
            })
            .collect::<Result<Vec<(Option<ExecStep>, Option<Call>)>, _>>()?;
        // set eth_block
        self.block.eth_block = eth_block.clone();
        self.set_value_ops_call_context_rwc_eor();
        if !res.is_empty() {
            Ok(res.remove(res.len() - 1))
        } else {
            Ok((None, None))
        }
    }

    /// Handle a block by handling each transaction to generate all the
    /// associated operations.
    pub fn handle_block(
        mut self,
        eth_block: &EthBlock,
        geth_traces: &[eth_types::GethExecTrace],
    ) -> Result<CircuitInputBuilder<FixedCParams>, Error> {
        // accumulates gas across all txs in the block
        let (last_step, last_call) = self.begin_handle_block(eth_block, geth_traces)?;
        // since there is no next step, we cook dummy next step from last step to reuse
        // existing field while update its `rwc`.
        let mut dummy_next_step = {
            let mut dummy_next_step = last_step.unwrap_or_default();
            // raise last step rwc to match with next step
            (0..dummy_next_step.rw_indices_len()).for_each(|_| {
                dummy_next_step.rwc.inc_pre();
                dummy_next_step.rwc_inner_chunk.inc_pre();
            });
            dummy_next_step
        };

        assert!(self.circuits_params.max_rws().is_some());

        let last_copy = self.block.copy_events.len();

        // TODO figure out and resolve generic param type and move fixed_param set inside
        // commit_chunk_ctx. After fixed, then we can set fixed_param on all chunks
        (0..self.circuits_params.total_chunks()).for_each(|idx| {
            self.get_chunk_mut(idx).fixed_param = self.circuits_params;
        });

        // We fill dummy virtual steps: BeginChunk,EndChunk for redundant chunks
        let last_process_chunk_id = self.chunk_ctx.idx;
        (last_process_chunk_id..self.circuits_params.total_chunks()).try_for_each(|idx| {
            if idx == self.circuits_params.total_chunks() - 1 {
                self.set_end_block()?;
                self.commit_chunk_ctx(
                    false,
                    eth_block.transactions.len(),
                    last_copy,
                    last_call.clone(),
                );
            } else {
                self.set_end_chunk(&dummy_next_step, None);

                self.commit_chunk_ctx(
                    true,
                    eth_block.transactions.len(),
                    last_copy,
                    last_call.clone(),
                );
                // update dummy_next_step rwc to be used for next
                dummy_next_step.rwc = self.block_ctx.rwc;
                dummy_next_step.rwc_inner_chunk = self.chunk_ctx.rwc;
                self.set_begin_chunk(&dummy_next_step, None);
                dummy_next_step.rwc = self.block_ctx.rwc;
                dummy_next_step.rwc_inner_chunk = self.chunk_ctx.rwc;
                // update virtual step: end_block/padding so it can carry state context correctly
                // TODO: enhance virtual step updating mechanism by having `running_next_step`
                // defined in circuit_input_builder, so we dont need to
                self.block.end_block = dummy_next_step.clone();
                self.cur_chunk_mut().padding = {
                    let mut padding = dummy_next_step.clone();
                    padding.exec_state = ExecState::Padding;
                    Some(padding)
                };
            }
            Ok::<(), Error>(())
        })?;

        let used_chunks = self.chunk_ctx.idx + 1;
        assert!(
            used_chunks <= self.circuits_params.total_chunks(),
            "Used more chunks than given total_chunks"
        );
        assert!(
            self.chunks.len() == self.chunk_ctx.idx + 1,
            "number of chunks {} mis-match with chunk_ctx id {}",
            self.chunks.len(),
            self.chunk_ctx.idx + 1,
        );

        // Truncate chunks to the actual used amount & correct ctx.total_chunks
        // Set length to the actual used amount of chunks
        self.chunks.truncate(self.chunk_ctx.idx + 1);
        self.chunks.iter_mut().for_each(|chunk| {
            chunk.ctx.total_chunks = used_chunks;
        });

        Ok(self)
    }

    fn set_end_block(&mut self) -> Result<(), Error> {
        let mut end_block = self.block.end_block.clone();
        end_block.rwc = self.block_ctx.rwc;
        end_block.exec_state = ExecState::EndBlock;
        end_block.rwc_inner_chunk = self.chunk_ctx.rwc;

        let mut dummy_tx = Transaction::default();
        let mut dummy_tx_ctx = TransactionContext::default();
        let mut state = self.state_ref(&mut dummy_tx, &mut dummy_tx_ctx);

        if let Some(call_id) = state.block.txs.last().map(|tx| tx.calls[0].call_id) {
            state.call_context_read(
                &mut end_block,
                call_id,
                CallContextField::TxId,
                Word::from(state.block.txs.len() as u64),
            )?;
        }

        // EndBlock step should also be padded to max_rws similar to EndChunk
        self.gen_chunk_padding(&mut end_block);
        self.block.end_block = end_block;
        Ok(())
    }
}

fn push_op<T: Op>(
    container: &mut OperationContainer,
    step: &mut ExecStep,
    rwc: RWCounter,
    rwc_inner_chunk: RWCounter,
    rw: RW,
    op: T,
) {
    let op_ref = container.insert(Operation::new(rwc, rwc_inner_chunk, rw, op));
    step.bus_mapping_instance.push(op_ref);
}

impl<C: CircuitsParams> CircuitInputBuilder<C> {
    /// return the rw row reserved for end_block/end_chunk
    pub fn last_exec_step_rws_reserved(&self) -> usize {
        // rw ops reserved for EndBlock
        let end_block_rws = if self.chunk_ctx.is_last_chunk() && self.chunk_rws() > 0 {
            1
        } else {
            0
        };
        // rw ops reserved for EndChunk
        let end_chunk_rws = if !self.chunk_ctx.is_last_chunk() {
            N_EXEC_STATE
        } else {
            0
        };
        end_block_rws + end_chunk_rws + 1
    }

    fn compute_param(&self, eth_block: &EthBlock) -> FixedCParams {
        let max_txs = eth_block.transactions.len();
        let max_withdrawals = eth_block.withdrawals.as_ref().unwrap().len();
        let max_bytecode = self.code_db.num_rows_required_for_bytecode_table();

        let max_calldata = eth_block
            .transactions
            .iter()
            .fold(0, |acc, tx| acc + tx.input.len());
        let max_exp_steps = self
            .block
            .exp_events
            .iter()
            .fold(0usize, |acc, e| acc + e.steps.len());
        // The `+ 2` is used to take into account the two extra empty copy rows needed
        // to satisfy the query at `Rotation(2)` performed inside of the
        // `rows[2].value == rows[0].value * r + rows[1].value` requirement in the RLC
        // Accumulation gate.
        let max_copy_rows = self
            .block
            .copy_events
            .iter()
            .fold(0, |acc, c| acc + c.bytes.len())
            * 2
            + 4; // disabled and unused rows.

        let max_rws = <RWCounter as Into<usize>>::into(self.block_ctx.rwc) - 1
            + self.last_exec_step_rws_reserved();

        // Computing the number of rows for the EVM circuit requires the size of ExecStep,
        // which is determined in the code of zkevm-circuits and cannot be imported here.
        // When the evm circuit receives a 0 value it dynamically computes the minimum
        // number of rows necessary.
        let max_evm_rows = 0;
        // Similarly, computing the number of rows for the Keccak circuit requires
        // constants that cannot be accessed from here (NUM_ROUNDS and KECCAK_ROWS).
        // With a 0 value the keccak circuit computes dynamically the minimum number of rows
        // needed.
        let max_keccak_rows = 0;
        FixedCParams {
            total_chunks: self.circuits_params.total_chunks(),
            max_rws,
            max_txs,
            max_withdrawals,
            max_calldata,
            max_copy_rows,
            max_exp_steps,
            max_bytecode,
            max_evm_rows,
            max_keccak_rows,
            max_vertical_circuit_rows: 0,
        }
    }
}

impl CircuitInputBuilder<DynamicCParams> {
    fn dry_run(
        &self,
        eth_block: &EthBlock,
        geth_traces: &[eth_types::GethExecTrace],
    ) -> Result<CircuitInputBuilder<DynamicCParams>, Error> {
        let mut cib = self.clone();
        cib.circuits_params.total_chunks = 1;
        cib.chunk_ctx.total_chunks = 1;
        // accumulates gas across all txs in the block
        for (idx, tx) in eth_block.transactions.iter().enumerate() {
            let geth_trace = &geth_traces[idx];
            // Transaction index starts from 1
            let tx_id = idx + 1;
            cib.handle_tx(
                tx,
                geth_trace,
                tx_id == eth_block.transactions.len(),
                tx_id as u64,
            )?;
        }
        // set eth_block
        cib.block.eth_block = eth_block.clone();
        cib.set_value_ops_call_context_rwc_eor();

        debug_assert!(
            cib.chunk_ctx.idx == 0,
            "processing {} > 1 chunk",
            cib.chunk_ctx.idx
        ); // dry run mode only one chunk

        Ok(cib)
    }

    /// Handle a block by handling each transaction to generate all the
    /// associated operations. Dry run the block to determind the target
    /// [`FixedCParams`] from to total number of chunks.
    pub fn handle_block(
        self,
        eth_block: &EthBlock,
        geth_traces: &[eth_types::GethExecTrace],
    ) -> Result<CircuitInputBuilder<FixedCParams>, Error> {
        // Run the block without chunking and compute the blockwise params
        let mut target_params = self
            .dry_run(eth_block, geth_traces)
            .expect("Dry run failure")
            .compute_param(eth_block);

        // Calculate the chunkwise params from total number of chunks
        let total_chunks = self.circuits_params.total_chunks;
        target_params.total_chunks = total_chunks;
        // count rws buffer here to left some space for extra virtual steps
        target_params.max_rws = (target_params.max_rws + 1) / total_chunks + RW_BUFFER_SIZE;

        // Use a new builder with targeted params to handle the block
        // chunking context is set to dynamic so for the actual param is update per chunk
        let cib = CircuitInputBuilder::<FixedCParams> {
            sdb: self.sdb,
            code_db: self.code_db,
            block: self.block,
            chunks: self.chunks,
            block_ctx: self.block_ctx,
            chunk_ctx: ChunkContext::new(total_chunks),
            circuits_params: target_params,
            feature_config: self.feature_config,
        };
        cib.handle_block(eth_block, geth_traces)
    }
}

/// Return all the keccak inputs used during the processing of the current
/// block.
pub fn keccak_inputs(block: &Block, code_db: &CodeDB) -> Result<Vec<Vec<u8>>, Error> {
    let mut keccak_inputs: HashSet<Vec<u8>> = HashSet::new();
    // Tx Circuit
    let txs: Vec<geth_types::Transaction> = block.txs.iter().map(|tx| tx.deref().clone()).collect();
    for input in keccak_inputs_tx_circuit(&txs, block.chain_id.as_u64())? {
        keccak_inputs.insert(input);
    }
    // Bytecode Circuit
    for bytecode in code_db.clone().into_iter() {
        keccak_inputs.insert(bytecode.code());
    }
    // EVM Circuit
    for input in &block.sha3_inputs {
        keccak_inputs.insert(input.clone());
    }
    // MPT Circuit
    // TODO https://github.com/privacy-scaling-explorations/zkevm-circuits/issues/696
    Ok(keccak_inputs.into_iter().collect_vec())
}

/// Generate the keccak inputs required by the SignVerify Chip from the
/// signature data.
pub fn keccak_inputs_sign_verify(sigs: &[SignData]) -> Vec<Vec<u8>> {
    let mut inputs = Vec::new();
    for sig in sigs {
        let pk_le = pk_bytes_le(&sig.pk);
        let pk_be = pk_bytes_swap_endianness(&pk_le);
        inputs.push(pk_be.to_vec());
    }
    // Padding signature
    let pk_le = pk_bytes_le(&SignData::default().pk);
    let pk_be = pk_bytes_swap_endianness(&pk_le);
    inputs.push(pk_be.to_vec());
    inputs
}

/// Generate the keccak inputs required by the Tx Circuit from the transactions.
pub fn keccak_inputs_tx_circuit(
    txs: &[geth_types::Transaction],
    chain_id: u64,
) -> Result<Vec<Vec<u8>>, Error> {
    let mut inputs = Vec::new();
    let sign_datas: Vec<SignData> = txs
        .iter()
        .enumerate()
        .filter(|(i, tx)| {
            if tx.v == 0 && tx.r.is_zero() && tx.s.is_zero() {
                warn!("tx {} is not signed, skipping tx circuit keccak input", i);
                false
            } else {
                true
            }
        })
        .map(|(_, tx)| tx.sign_data(chain_id))
        .try_collect()?;
    // Keccak inputs from SignVerify Chip
    let sign_verify_inputs = keccak_inputs_sign_verify(&sign_datas);
    inputs.extend_from_slice(&sign_verify_inputs);
    // NOTE: We don't verify the Tx Hash in the circuit yet, so we don't have more
    // hash inputs.
    Ok(inputs)
}

/// Retrieve the init_code from memory for {CREATE, CREATE2}
pub fn get_create_init_code(call_ctx: &CallContext, step: &GethExecStep) -> Result<Vec<u8>, Error> {
    let offset = step.stack.nth_last(1)?.low_u64() as usize;
    let length = step.stack.nth_last(2)?.as_usize();

    let mem_len = call_ctx.memory.0.len();
    let mut result = vec![0u8; length];
    if length > 0 && offset < mem_len {
        let offset_end = offset
            .checked_add(length)
            .expect("overflow should be handled using OOG error")
            .min(mem_len);
        let copy_len = offset_end - offset;
        result[..copy_len].copy_from_slice(&call_ctx.memory.0[offset..offset_end]);
    }
    Ok(result)
}

/// Retrieve the memory offset and length of call.
pub fn get_call_memory_offset_length(step: &GethExecStep, nth: usize) -> Result<(u64, u64), Error> {
    let offset = step.stack.nth_last(nth)?;
    let length = step.stack.nth_last(nth + 1)?;
    if length.is_zero() {
        Ok((0, 0))
    } else {
        Ok((offset.low_u64(), length.low_u64()))
    }
}

type EthBlock = eth_types::Block<eth_types::Transaction>;

/// Struct that wraps a GethClient and contains methods to perform all the steps
/// necessary to generate the circuit inputs for a block by querying geth for
/// the necessary information and using the CircuitInputBuilder.
pub struct BuilderClient<P: JsonRpcClient> {
    cli: GethClient<P>,
    chain_id: Word,
    circuits_params: FixedCParams,
    feature_config: FeatureConfig,
}

/// Get State Accesses from TxExecTraces
pub fn get_state_accesses(
    eth_block: &EthBlock,
    geth_traces: &[eth_types::GethExecTrace],
) -> Result<AccessSet, Error> {
    let mut block_access_trace = vec![Access::new(
        None,
        RW::WRITE,
        AccessValue::Account {
            address: eth_block
                .author
                .ok_or(Error::EthTypeError(eth_types::Error::IncompleteBlock))?,
        },
    )];
    for (tx_index, tx) in eth_block.transactions.iter().enumerate() {
        let geth_trace = &geth_traces[tx_index];
        let tx_access_trace = gen_state_access_trace(eth_block, tx, geth_trace)?;
        block_access_trace.extend(tx_access_trace);
    }

    Ok(AccessSet::from(block_access_trace))
}

/// Build a partial StateDB from step 3
pub fn build_state_code_db(
    proofs: Vec<eth_types::EIP1186ProofResponse>,
    codes: HashMap<Address, Vec<u8>>,
) -> (StateDB, CodeDB) {
    let mut sdb = StateDB::new();
    for proof in proofs {
        let mut storage = HashMap::new();
        for storage_proof in proof.storage_proof {
            storage.insert(storage_proof.key, storage_proof.value);
        }
        sdb.set_account(
            &proof.address,
            state_db::Account {
                nonce: proof.nonce.as_u64(),
                balance: proof.balance,
                storage,
                code_hash: proof.code_hash,
            },
        )
    }

    let mut code_db = CodeDB::default();
    for (_address, code) in codes {
        code_db.insert(code.clone());
    }
    (sdb, code_db)
}

impl<P: JsonRpcClient> BuilderClient<P> {
    /// Create a new BuilderClient
    pub async fn new(client: GethClient<P>, circuits_params: FixedCParams) -> Result<Self, Error> {
        Self::new_with_features(client, circuits_params, FeatureConfig::default()).await
    }

    /// Create a new BuilderClient
    pub async fn new_with_features(
        client: GethClient<P>,
        circuits_params: FixedCParams,
        feature_config: FeatureConfig,
    ) -> Result<Self, Error> {
        let chain_id = client.get_chain_id().await?;

        Ok(Self {
            cli: client,
            chain_id: chain_id.into(),
            circuits_params,
            feature_config,
        })
    }

    /// Step 1. Query geth for Block, Txs, TxExecTraces, history block hashes
    /// and previous state root.
    pub async fn get_block(
        &self,
        block_num: u64,
    ) -> Result<(EthBlock, Vec<eth_types::GethExecTrace>, Vec<Word>, Word), Error> {
        let eth_block = self.cli.get_block_by_number(block_num.into()).await?;
        let geth_traces = self.cli.trace_block_by_number(block_num.into()).await?;

        // fetch up to 256 blocks
        let mut n_blocks = std::cmp::min(256, block_num as usize);
        let mut next_hash = eth_block.parent_hash;
        let mut prev_state_root: Option<Word> = None;
        let mut history_hashes = vec![Word::default(); n_blocks];
        while n_blocks > 0 {
            n_blocks -= 1;

            // TODO: consider replacing it with `eth_getHeaderByHash`, it's faster
            let header = self.cli.get_block_by_hash(next_hash).await?;

            // set the previous state root
            if prev_state_root.is_none() {
                prev_state_root = Some(header.state_root.to_word());
            }

            // latest block hash is the last item
            let block_hash = header
                .hash
                .ok_or(Error::EthTypeError(eth_types::Error::IncompleteBlock))?
                .to_word();
            history_hashes[n_blocks] = block_hash;

            // continue
            next_hash = header.parent_hash;
        }

        Ok((
            eth_block,
            geth_traces,
            history_hashes,
            prev_state_root.unwrap_or_default(),
        ))
    }

    /// Step 2. Get State Accesses from TxExecTraces
    pub fn get_state_accesses(
        eth_block: &EthBlock,
        geth_traces: &[eth_types::GethExecTrace],
    ) -> Result<AccessSet, Error> {
        get_state_accesses(eth_block, geth_traces)
    }

    /// Step 3. Query geth for all accounts, storage keys, and codes from
    /// Accesses
    pub async fn get_state(
        &self,
        block_num: u64,
        access_set: AccessSet,
    ) -> Result<
        (
            Vec<eth_types::EIP1186ProofResponse>,
            HashMap<Address, Vec<u8>>,
        ),
        Error,
    > {
        let mut proofs = Vec::new();
        for (address, key_set) in access_set.state {
            let mut keys: Vec<Word> = key_set.iter().cloned().collect();
            keys.sort();
            let proof = self
                .cli
                .get_proof(address, keys, (block_num - 1).into())
                .await
                .unwrap();
            proofs.push(proof);
        }
        let mut codes: HashMap<Address, Vec<u8>> = HashMap::new();
        for address in access_set.code {
            let code = self
                .cli
                .get_code(address, (block_num - 1).into())
                .await
                .unwrap();
            codes.insert(address, code);
        }
        Ok((proofs, codes))
    }

    /// Step 4. Build a partial StateDB from step 3
    pub fn build_state_code_db(
        proofs: Vec<eth_types::EIP1186ProofResponse>,
        codes: HashMap<Address, Vec<u8>>,
    ) -> (StateDB, CodeDB) {
        build_state_code_db(proofs, codes)
    }

    /// Step 5. For each step in TxExecTraces, gen the associated ops and state
    /// circuit inputs
    pub fn gen_inputs_from_state(
        &self,
        sdb: StateDB,
        code_db: CodeDB,
        eth_block: &EthBlock,
        geth_traces: &[eth_types::GethExecTrace],
        history_hashes: Vec<Word>,
        prev_state_root: Word,
    ) -> Result<CircuitInputBuilder<FixedCParams>, Error> {
        let block = Block::new(self.chain_id, history_hashes, prev_state_root, eth_block)?;
        let builder = CircuitInputBuilder::new(
            sdb,
            code_db,
            block,
            self.circuits_params,
            self.feature_config,
        );
        let builder = builder.handle_block(eth_block, geth_traces)?;
        Ok(builder)
    }

    /// Perform all the steps to generate the circuit inputs
    pub async fn gen_inputs(
        &self,
        block_num: u64,
    ) -> Result<
        (
            CircuitInputBuilder<FixedCParams>,
            eth_types::Block<eth_types::Transaction>,
        ),
        Error,
    > {
        let (eth_block, geth_traces, history_hashes, prev_state_root) =
            self.get_block(block_num).await?;
        let access_set = Self::get_state_accesses(&eth_block, &geth_traces)?;
        let (proofs, codes) = self.get_state(block_num, access_set).await?;
        let (state_db, code_db) = Self::build_state_code_db(proofs, codes);
        let builder = self.gen_inputs_from_state(
            state_db,
            code_db,
            &eth_block,
            &geth_traces,
            history_hashes,
            prev_state_root,
        )?;
        Ok((builder, eth_block))
    }
}
