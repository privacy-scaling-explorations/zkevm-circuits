//! Types needed for block

use eth_types::Word;
use ethers_core::types::{Block, Transaction};

/// Transaction in a witness block
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct ZkEvmBlock {
    /// Transactions in the block
    // pub txs: Vec<ZkEvmTransaction>,
    // /// Copy events for the copy circuit's table.
    // pub copy_events: Vec<CopyEvent>,
    // /// Exponentiation traces for the exponentiation circuit's table.
    // pub exp_events: Vec<ExpEvent>,
    // /// Circuit Setup Parameters
    // pub circuits_params: CircuitsParams,
    /// Inputs to the SHA3 opcode
    pub sha3_inputs: Vec<Vec<u8>>,
    /// State root of the previous block
    pub prev_state_root: Word, // TODO: Make this H256
    /// Original Block from geth
    pub eth_block: Block<Transaction>,
}
