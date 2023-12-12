//! Constants and parameters for the EVM circuit
use super::table::Table;
use crate::evm_circuit::{step::ExecutionState, EvmCircuit};
use halo2_proofs::{
    halo2curves::bn256::Fr,
    plonk::{Circuit, ConstraintSystem},
};
use std::collections::HashMap;

// Step dimension
pub(crate) const STEP_WIDTH: usize = 131;
/// Step height
pub const MAX_STEP_HEIGHT: usize = 19;
/// The height of the state of a step, used by gates that connect two
/// consecutive steps. We target 1, which is also convenient for padding with
/// EndBlock steps.
pub(crate) const STEP_STATE_HEIGHT: usize = 1;

/// Number of Advice Phase2 columns in the EVM circuit
pub const N_PHASE2_COLUMNS: usize = 1;

/// Number of Advice Phase1 columns in the EVM circuit
pub const N_PHASE1_COLUMNS: usize =
    STEP_WIDTH - EVM_LOOKUP_COLS - N_PHASE2_COLUMNS - N_COPY_COLUMNS - N_U8_LOOKUPS - N_U16_LOOKUPS;

/// Number of copy columns
pub const N_COPY_COLUMNS: usize = 2;

/// Number of columns reserved for u8 lookup
pub const N_U8_LOOKUPS: usize = 24;

// TODO shift #column/2 from u8 to u16
/// Number of columns reserved for u16 lookup
pub const N_U16_LOOKUPS: usize = 0;

/// Amount of lookup columns in the EVM circuit dedicated to lookups.
pub(crate) const EVM_LOOKUP_COLS: usize = FIXED_TABLE_LOOKUPS
    + TX_TABLE_LOOKUPS
    + RW_TABLE_LOOKUPS
    + BYTECODE_TABLE_LOOKUPS
    + BLOCK_TABLE_LOOKUPS
    + COPY_TABLE_LOOKUPS
    + KECCAK_TABLE_LOOKUPS
    + EXP_TABLE_LOOKUPS
    + CHUNK_CTX_TABLE_LOOKUPS;

/// Lookups done per row.
pub const LOOKUP_CONFIG: &[(Table, usize)] = &[
    (Table::Fixed, FIXED_TABLE_LOOKUPS),
    (Table::Tx, TX_TABLE_LOOKUPS),
    (Table::Rw, RW_TABLE_LOOKUPS),
    (Table::Bytecode, BYTECODE_TABLE_LOOKUPS),
    (Table::Block, BLOCK_TABLE_LOOKUPS),
    (Table::Copy, COPY_TABLE_LOOKUPS),
    (Table::Keccak, KECCAK_TABLE_LOOKUPS),
    (Table::Exp, EXP_TABLE_LOOKUPS),
    (Table::chunk_ctx, CHUNK_CTX_TABLE_LOOKUPS),
];

/// Fixed Table lookups done in EVMCircuit
pub const FIXED_TABLE_LOOKUPS: usize = 8;

/// Tx Table lookups done in EVMCircuit
pub const TX_TABLE_LOOKUPS: usize = 4;

/// Rw Table lookups done in EVMCircuit
pub const RW_TABLE_LOOKUPS: usize = 13;

/// Bytecode Table lookups done in EVMCircuit
pub const BYTECODE_TABLE_LOOKUPS: usize = 4;

/// Block Table lookups done in EVMCircuit
pub const BLOCK_TABLE_LOOKUPS: usize = 1;

/// Copy Table lookups done in EVMCircuit
pub const COPY_TABLE_LOOKUPS: usize = 1;

/// Keccak Table lookups done in EVMCircuit
pub const KECCAK_TABLE_LOOKUPS: usize = 1;

/// Exp Table lookups done in EVMCircuit
pub const EXP_TABLE_LOOKUPS: usize = 1;

/// chunk_ctx Table lookups done in EVMCircuit
pub const CHUNK_CTX_TABLE_LOOKUPS: usize = 1;

/// Maximum number of bytes that an integer can fit in field without wrapping
/// around.
pub(crate) const MAX_N_BYTES_INTEGER: usize = 31;

// Number of bytes an EVM word has.
pub(crate) const N_BYTES_WORD: usize = 32;

// Number of bytes an half EVM word has.
pub(crate) const N_BYTES_HALF_WORD: usize = N_BYTES_WORD / 2;

// Number of bytes an u64 has.
pub(crate) const N_BYTES_U64: usize = 8;

pub(crate) const N_BYTES_ACCOUNT_ADDRESS: usize = 20;

// Number of bytes that will be used of the memory address and size.
// If any of the other more significant bytes are used it will always result in
// an out-of-gas error.
pub(crate) const N_BYTES_MEMORY_ADDRESS: usize = 5;
pub(crate) const N_BYTES_MEMORY_WORD_SIZE: usize = 4;

pub(crate) const STACK_CAPACITY: usize = 1024;

// Number of bytes that will be used of prorgam counter. Although the maximum
// size of execution bytecode could be at most 128kB due to the size limit of a
// transaction, which could be covered by 3 bytes, we still support program
// counter to u64 as go-ethereum in case transaction size is allowed larger in
// the future.
pub(crate) const N_BYTES_PROGRAM_COUNTER: usize = N_BYTES_U64;

// Number of bytes that will be used for a tx's gas field.
pub(crate) const N_BYTES_GAS: usize = N_BYTES_U64;

// Number of bytes that will be used for call data's size.
pub(crate) const N_BYTES_CALLDATASIZE: usize = N_BYTES_U64;

// Number of bytes that will be used for block values
pub(crate) const N_BYTES_COINBASE: usize = N_BYTES_ACCOUNT_ADDRESS;
pub(crate) const N_BYTES_GAS_LIMIT: usize = N_BYTES_U64;
pub(crate) const N_BYTES_NUMBER: usize = N_BYTES_U64;
pub(crate) const N_BYTES_TIMESTAMP: usize = N_BYTES_U64;
pub(crate) const N_BYTES_DIFFICULTY: usize = N_BYTES_WORD;
pub(crate) const N_BYTES_BASE_FEE: usize = N_BYTES_WORD;
pub(crate) const N_BYTES_CHAIN_ID: usize = N_BYTES_U64;
pub(crate) const N_BYTES_PREV_HASH: usize = 256 * N_BYTES_WORD;

pub(crate) const N_BYTES_BLOCK: usize = N_BYTES_COINBASE
    + N_BYTES_GAS_LIMIT
    + N_BYTES_NUMBER
    + N_BYTES_TIMESTAMP
    + N_BYTES_DIFFICULTY
    + N_BYTES_BASE_FEE
    + N_BYTES_CHAIN_ID
    + N_BYTES_PREV_HASH;

pub(crate) const N_BYTES_EXTRA_VALUE: usize = N_BYTES_WORD // block hash
    + N_BYTES_WORD // state root
    + N_BYTES_WORD; // prev state root

// Number of bytes that will be used for tx values
pub(crate) const N_BYTES_TX_NONCE: usize = N_BYTES_U64;
pub(crate) const N_BYTES_TX_GAS_LIMIT: usize = N_BYTES_U64; // gas limit type is U256, different with gas U64
pub(crate) const N_BYTES_TX_GASPRICE: usize = N_BYTES_WORD;
pub(crate) const N_BYTES_TX_FROM: usize = N_BYTES_ACCOUNT_ADDRESS;
pub(crate) const N_BYTES_TX_TO: usize = N_BYTES_ACCOUNT_ADDRESS;
pub(crate) const N_BYTES_TX_IS_CREATE: usize = N_BYTES_U64;
pub(crate) const N_BYTES_TX_VALUE: usize = N_BYTES_WORD;
pub(crate) const N_BYTES_TX_CALLDATA_LEN: usize = N_BYTES_CALLDATASIZE;
pub(crate) const N_BYTES_TX_CALLDATA_GASCOST: usize = N_BYTES_U64;
pub(crate) const N_BYTES_TX_TXSIGNHASH: usize = N_BYTES_WORD;
pub(crate) const N_BYTES_TX: usize = N_BYTES_TX_NONCE
    + N_BYTES_TX_GAS_LIMIT
    + N_BYTES_TX_GASPRICE
    + N_BYTES_TX_FROM
    + N_BYTES_TX_TO
    + N_BYTES_TX_IS_CREATE
    + N_BYTES_TX_VALUE
    + N_BYTES_TX_CALLDATA_LEN
    + N_BYTES_TX_CALLDATA_GASCOST
    + N_BYTES_TX_TXSIGNHASH;

lazy_static::lazy_static! {
    // Step slot height in evm circuit
    pub(crate) static ref EXECUTION_STATE_HEIGHT_MAP : HashMap<ExecutionState, usize> = get_step_height_map();
}
fn get_step_height_map() -> HashMap<ExecutionState, usize> {
    let mut meta = ConstraintSystem::<Fr>::default();
    let circuit = EvmCircuit::configure(&mut meta);

    circuit.0.execution.height_map
}
