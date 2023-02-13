use std::collections::HashMap;

use crate::evm_circuit::{detect_fixed_table_tags, EvmCircuit};
use bus_mapping::{
    circuit_input_builder::{self, CircuitsParams, CopyEvent, ExpEvent},
    Error,
};
use eth_types::{Address, Field, Word};

use super::{step::step_convert, tx::tx_convert, Bytecode, ExecStep, RwMap, Transaction};

// TODO: Remove fields that are duplicated in`eth_block`
/// Block is the struct used by all circuits, which contains all the needed
/// data for witness generation.
#[derive(Debug, Clone, Default)]
pub struct Block<F> {
    /// The randomness for random linear combination
    pub randomness: F,
    /// Transactions in the block
    pub txs: Vec<Transaction>,
    /// EndBlock step that is repeated after the last transaction and before
    /// reaching the last EVM row.
    pub end_block_not_last: ExecStep,
    /// Last EndBlock step that appears in the last EVM row.
    pub end_block_last: ExecStep,
    /// Read write events in the RwTable
    pub rws: RwMap,
    /// Bytecode used in the block
    pub bytecodes: HashMap<Word, Bytecode>,
    /// The block context
    pub context: BlockContext,
    /// Copy events for the copy circuit's table.
    pub copy_events: Vec<CopyEvent>,
    /// Exponentiation traces for the exponentiation circuit's table.
    pub exp_events: Vec<ExpEvent>,
    // TODO: Rename to `max_evm_rows`, maybe move to CircuitsParams
    /// Pad evm circuit to make selectors fixed, so vk/pk can be universal.
    /// When 0, the EVM circuit contains as many rows for all steps + 1 row
    /// for EndBlock.
    pub evm_circuit_pad_to: usize,
    /// Pad exponentiation circuit to make selectors fixed.
    pub exp_circuit_pad_to: usize,
    /// Circuit Setup Parameters
    pub circuits_params: CircuitsParams,
    /// Inputs to the SHA3 opcode
    pub sha3_inputs: Vec<Vec<u8>>,
    /// State root of the previous block
    pub prev_state_root: Word, // TODO: Make this H256
    /// Keccak inputs
    pub keccak_inputs: Vec<Vec<u8>>,
    /// Original Block from geth
    pub eth_block: eth_types::Block<eth_types::Transaction>,
}

impl<F: Field> Block<F> {
    /// For each tx, for each step, print the rwc at the beginning of the step,
    /// and all the rw operations of the step.
    pub(crate) fn debug_print_txs_steps_rw_ops(&self) {
        for (tx_idx, tx) in self.txs.iter().enumerate() {
            println!("tx {}", tx_idx);
            for step in &tx.steps {
                println!(" step {:?} rwc: {}", step.execution_state, step.rw_counter);
                for rw_ref in &step.rw_indices {
                    println!("  - {:?}", self.rws[*rw_ref]);
                }
            }
        }
    }
}

#[cfg(feature = "test")]
use crate::exp_circuit::OFFSET_INCREMENT;
#[cfg(feature = "test")]
use crate::util::log2_ceil;

#[cfg(feature = "test")]
impl<F: Field> Block<F> {
    /// Obtains the expected Circuit degree needed in order to be able to test
    /// the EvmCircuit with this block without needing to configure the
    /// `ConstraintSystem`.
    pub fn get_test_degree(&self) -> u32 {
        let num_rows_required_for_execution_steps: usize =
            EvmCircuit::<F>::get_num_rows_required(self);
        let num_rows_required_for_rw_table: usize = self.circuits_params.max_rws;
        let num_rows_required_for_fixed_table: usize = detect_fixed_table_tags(self)
            .iter()
            .map(|tag| tag.build::<F>().count())
            .sum();
        let num_rows_required_for_bytecode_table: usize = self
            .bytecodes
            .values()
            .map(|bytecode| bytecode.bytes.len() + 1)
            .sum();
        let num_rows_required_for_copy_table: usize =
            self.copy_events.iter().map(|c| c.bytes.len() * 2).sum();
        let num_rows_required_for_keccak_table: usize = self.keccak_inputs.len();
        let num_rows_required_for_tx_table: usize =
            self.txs.iter().map(|tx| 9 + tx.call_data.len()).sum();
        let num_rows_required_for_exp_table: usize = self
            .exp_events
            .iter()
            .map(|e| e.steps.len() * OFFSET_INCREMENT)
            .sum();

        const NUM_BLINDING_ROWS: usize = 64;

        let rows_needed: usize = itertools::max([
            num_rows_required_for_execution_steps,
            num_rows_required_for_rw_table,
            num_rows_required_for_fixed_table,
            num_rows_required_for_bytecode_table,
            num_rows_required_for_copy_table,
            num_rows_required_for_keccak_table,
            num_rows_required_for_tx_table,
            num_rows_required_for_exp_table,
        ])
        .unwrap();

        let k = log2_ceil(NUM_BLINDING_ROWS + rows_needed);
        log::debug!(
            "num_rows_requred_for rw_table={}, fixed_table={}, bytecode_table={}, \
            copy_table={}, keccak_table={}, tx_table={}, exp_table={}",
            num_rows_required_for_rw_table,
            num_rows_required_for_fixed_table,
            num_rows_required_for_bytecode_table,
            num_rows_required_for_copy_table,
            num_rows_required_for_keccak_table,
            num_rows_required_for_tx_table,
            num_rows_required_for_exp_table
        );
        log::debug!("evm circuit uses k = {}, rows = {}", k, rows_needed);
        k
    }
}

/// Block context for execution
#[derive(Debug, Default, Clone)]
pub struct BlockContext {
    /// The address of the miner for the block
    pub coinbase: Address,
    /// The gas limit of the block
    pub gas_limit: u64,
    /// The number of the block
    pub number: Word,
    /// The timestamp of the block
    pub timestamp: Word,
    /// The difficulty of the blcok
    pub difficulty: Word,
    /// The base fee, the minimum amount of gas fee for a transaction
    pub base_fee: Word,
    /// The hash of previous blocks
    pub history_hashes: Vec<Word>,
    /// The chain id
    pub chain_id: Word,
}

impl From<&circuit_input_builder::Block> for BlockContext {
    fn from(block: &circuit_input_builder::Block) -> Self {
        Self {
            coinbase: block.coinbase,
            gas_limit: block.gas_limit,
            number: block.number,
            timestamp: block.timestamp,
            difficulty: block.difficulty,
            base_fee: block.base_fee,
            history_hashes: block.history_hashes.clone(),
            chain_id: block.chain_id,
        }
    }
}

/// Convert a block struct in bus-mapping to a witness block used in circuits
pub fn block_convert<F: Field>(
    block: &circuit_input_builder::Block,
    code_db: &bus_mapping::state_db::CodeDB,
) -> Result<Block<F>, Error> {
    Ok(Block {
        // randomness: F::from(0x100), // Special value to reveal elements after RLC
        randomness: F::from(0xcafeu64),
        context: block.into(),
        rws: RwMap::from(&block.container),
        txs: block
            .txs()
            .iter()
            .enumerate()
            .map(|(idx, tx)| tx_convert(tx, idx + 1))
            .collect(),
        end_block_not_last: step_convert(&block.block_steps.end_block_not_last),
        end_block_last: step_convert(&block.block_steps.end_block_last),
        bytecodes: code_db
            .0
            .values()
            .map(|v| {
                let bytecode = Bytecode::new(v.clone());
                (bytecode.hash, bytecode)
            })
            .collect(),
        copy_events: block.copy_events.clone(),
        exp_events: block.exp_events.clone(),
        sha3_inputs: block.sha3_inputs.clone(),
        circuits_params: block.circuits_params,
        evm_circuit_pad_to: <usize>::default(),
        exp_circuit_pad_to: <usize>::default(),
        prev_state_root: block.prev_state_root,
        keccak_inputs: circuit_input_builder::keccak_inputs(block, code_db)?,
        eth_block: block.eth_block.clone(),
    })
}
