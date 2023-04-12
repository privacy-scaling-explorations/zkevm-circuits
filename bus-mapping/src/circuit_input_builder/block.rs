//! Block-related utility module

use super::{
    execution::ExecState, transaction::Transaction, CircuitsParams, CopyEvent, ExecStep, ExpEvent,
};
use crate::{
    operation::{OperationContainer, RWCounter},
    Error,
};
use eth_types::{evm_unimplemented, Address, Hash, Word};
use std::collections::HashMap;

/// Context of a [`Block`] which can mutate in a [`Transaction`].
#[derive(Debug)]
pub struct BlockContext {
    /// Used to track the global counter in every operation in the block.
    /// Contains the next available value.
    pub(crate) rwc: RWCounter,
    /// Map call_id to (tx_index, call_index) (where tx_index is the index used
    /// in Block.txs and call_index is the index used in Transaction.
    /// calls).
    pub(crate) call_map: HashMap<usize, (usize, usize)>,
    /// Total gas used by previous transactions in this block.
    pub(crate) cumulative_gas_used: u64,
}

impl Default for BlockContext {
    fn default() -> Self {
        Self::new()
    }
}

impl BlockContext {
    /// Create a new Self
    pub fn new() -> Self {
        Self {
            rwc: RWCounter::new(),
            call_map: HashMap::new(),
            cumulative_gas_used: 0,
        }
    }
}

/// Block-wise execution steps that don't belong to any Transaction.
#[derive(Debug)]
pub struct BlockSteps {
    /// EndBlock step that is repeated after the last transaction and before
    /// reaching the last EVM row.
    pub end_block_not_last: ExecStep,
    /// Last EndBlock step that appears in the last EVM row.
    pub end_block_last: ExecStep,
}

// TODO: Remove fields that are duplicated in`eth_block`
/// Circuit Input related to a block.
#[derive(Debug)]
pub struct Block {
    // pub block: ZkEvmBlock,
    /// Transactions in the block
    pub txs: Vec<Transaction>,
    /// Inputs to the SHA3 opcode
    pub sha3_inputs: Vec<Vec<u8>>,
    /// State root of the previous block
    pub prev_state_root: Word, // TODO: Make this H256
    /// Original Block from geth
    pub eth_block: ethers_core::types::Block<ethers_core::types::Transaction>,

    /// chain id
    pub chain_id: Word,
    /// history hashes contains most recent 256 block hashes in history, where
    /// the latest one is at history_hashes[history_hashes.len() - 1].
    pub history_hashes: Vec<Word>,
    /// coinbase
    pub coinbase: Address,
    /// time
    pub gas_limit: u64,
    /// number
    pub number: Word,
    /// difficulty
    pub timestamp: Word,
    /// gas limit
    pub difficulty: Word,
    /// base fee
    pub base_fee: Word,
    /// Container of operations done in this block.
    pub container: OperationContainer,
    /// Block-wise steps
    pub block_steps: BlockSteps,
    // pub exp_events: Vec<ExpEvent>,
    code: HashMap<Hash, Vec<u8>>,

    // TODO-KIMI: decouple these types and move to eth-types/
    /// Copy events for the copy circuit's table.
    pub copy_events: Vec<CopyEvent>,
    /// Exponentiation traces for the exponentiation circuit's table.  
    pub exp_events: Vec<ExpEvent>,
    /// Circuit Setup Parameters
    pub circuits_params: CircuitsParams,
}

impl Block {
    /// Create a new block.
    pub fn new(
        chain_id: Word,
        history_hashes: Vec<Word>,
        prev_state_root: Word,
        eth_block: &eth_types::Block<eth_types::Transaction>,
        circuits_params: CircuitsParams,
    ) -> Result<Self, Error> {
        if eth_block.base_fee_per_gas.is_none() {
            // FIXME: resolve this once we have proper EIP-1559 support
            evm_unimplemented!(
                "This does not look like a EIP-1559 block - base_fee_per_gas defaults to zero"
            );
        }

        Ok(Self {
            txs: Vec::new(),
            sha3_inputs: Vec::new(),
            prev_state_root,
            eth_block: eth_block.clone(),
            chain_id,
            history_hashes,
            coinbase: eth_block
                .author
                .ok_or(Error::EthTypeError(eth_types::Error::IncompleteBlock))?,
            gas_limit: eth_block.gas_limit.low_u64(),
            number: eth_block
                .number
                .ok_or(Error::EthTypeError(eth_types::Error::IncompleteBlock))?
                .low_u64()
                .into(),
            timestamp: eth_block.timestamp,
            difficulty: eth_block.difficulty,
            base_fee: eth_block.base_fee_per_gas.unwrap_or_default(),
            container: OperationContainer::new(),
            block_steps: BlockSteps {
                end_block_not_last: ExecStep {
                    exec_state: ExecState::EndBlock,
                    ..ExecStep::default()
                },
                end_block_last: ExecStep {
                    exec_state: ExecState::EndBlock,
                    ..ExecStep::default()
                },
            },
            copy_events: Vec::new(),
            exp_events: Vec::new(),
            code: HashMap::new(),

            circuits_params,
        })
    }

    /// Return the list of transactions of this block.
    pub fn txs(&self) -> &[Transaction] {
        &self.txs
    }

    #[cfg(test)]
    pub fn txs_mut(&mut self) -> &mut Vec<Transaction> {
        &mut self.txs
    }
}

impl Block {
    /// Push a copy event to the block.
    pub fn add_copy_event(&mut self, event: CopyEvent) {
        self.copy_events.push(event);
    }
    /// Push an exponentiation event to the block.
    pub fn add_exp_event(&mut self, event: ExpEvent) {
        self.exp_events.push(event);
    }
}
