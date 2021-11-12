//! Mock types and functions to generate mock data useful for tests
use crate::address;
use crate::bytecode::Bytecode;
use crate::eth_types::{self, Address, Bytes, Hash, Index, Word, H64, U64};
use crate::evm::Gas;
use crate::external_tracer;
use crate::BlockConstants;
use crate::Error;

/// Generate a new mock block with preloaded data, useful for tests.
pub fn new_block() -> eth_types::Block<()> {
    eth_types::Block {
        hash: Some(Hash::from([0u8; 32])),
        parent_hash: Hash::from([0u8; 32]),
        uncles_hash: Hash::from([0u8; 32]),
        author: Address::from([0u8; 20]),
        state_root: Hash::from([0u8; 32]),
        transactions_root: Hash::from([0u8; 32]),
        receipts_root: Hash::from([0u8; 32]),
        number: Some(U64([123456u64])),
        gas_used: Word::from(15_000_000u64),
        gas_limit: Word::from(15_000_000u64),
        base_fee_per_gas: Some(Word::from(97u64)),
        extra_data: Bytes(Vec::new()),
        logs_bloom: None,
        timestamp: Word::from(1633398551u64),
        difficulty: Word::from(0x200000u64),
        total_difficulty: None,
        seal_fields: Vec::new(),
        uncles: Vec::new(),
        transactions: Vec::new(),
        size: None,
        mix_hash: None,
        nonce: Some(H64([0u8; 8])),
    }
}

/// Generate a new mock transaction with preloaded data, useful for tests.
pub fn new_tx<TX>(block: &eth_types::Block<TX>) -> eth_types::Transaction {
    eth_types::Transaction {
        hash: Hash::from([0u8; 32]),
        nonce: Word::from([0u8; 32]),
        block_hash: block.hash,
        block_number: block.number,
        transaction_index: Some(Index::from(0u64)),
        from: Some(address!("0x00000000000000000000000000000000c014ba5e")),
        to: Some(Address::zero()),
        value: Word::from([0u8; 32]),
        gas_price: Word::from([0u8; 32]),
        gas: Word::from(1_000_000u64),
        input: Bytes(Vec::new()),
        v: Some(U64([0u64])),
        r: Some(Word::from([0u8; 32])),
        s: Some(Word::from([0u8; 32])),
        raw: Some(Bytes(Vec::new())),
        transaction_type: Some(U64([0u64])),
        access_list: None,
    }
}

/// BlockData is a type that contains all the information from a block required to build the
/// circuit inputs.
pub struct BlockData {
    /// Block from geth
    pub eth_block: eth_types::Block<()>,
    /// Transaction from geth
    pub eth_tx: eth_types::Transaction,
    /// Block Constants
    pub block_ctants: BlockConstants,
    /// Execution Trace from geth
    pub geth_trace: eth_types::GethExecTrace,
}

impl BlockData {
    /// Create a new block with a single tx that executes the code passed by argument.  The trace
    /// will be generated automatically with the external_tracer from the code.
    pub fn new_single_tx_trace_code(code: &Bytecode) -> Result<Self, Error> {
        let eth_block = new_block();
        let eth_tx = new_tx(&eth_block);
        let block_ctants = BlockConstants::from_eth_block(
            &eth_block,
            &eth_types::Word::one(),
            &address!("0x00000000000000000000000000000000c014ba5e"),
        );
        let tracer_tx = external_tracer::Transaction::from_eth_tx(&eth_tx);
        let tracer_account = new_tracer_account(code);
        let geth_trace = eth_types::GethExecTrace {
            gas: Gas(eth_tx.gas.as_u64()),
            failed: false,
            struct_logs: external_tracer::trace(
                &block_ctants,
                &tracer_tx,
                &[tracer_account],
            )?
            .to_vec(),
        };
        Ok(Self {
            eth_block,
            eth_tx,
            block_ctants,
            geth_trace,
        })
    }

    /// Create a new block with a single tx that executes the code passed by argument.  The trace
    /// will be generated automatically with the external_tracer from the code.  The trace steps
    /// will start at the "start" position as tagged in the code.
    pub fn new_single_tx_trace_code_at_start(
        code: &Bytecode,
    ) -> Result<Self, Error> {
        let mut mock = Self::new_single_tx_trace_code(code)?;
        mock.geth_trace.struct_logs =
            mock.geth_trace.struct_logs[code.get_pos("start")..].to_vec();
        Ok(mock)
    }

    /// Create a new block with a single tx that leads to the geth_steps passed by argument.
    pub fn new_single_tx_geth_steps(
        geth_steps: Vec<eth_types::GethExecStep>,
    ) -> Self {
        let eth_block = new_block();
        let eth_tx = new_tx(&eth_block);
        let block_ctants = BlockConstants::from_eth_block(
            &eth_block,
            &eth_types::Word::one(),
            &crate::address!("0x00000000000000000000000000000000c014ba5e"),
        );
        let geth_trace = eth_types::GethExecTrace {
            gas: Gas(eth_tx.gas.as_u64()),
            failed: false,
            struct_logs: geth_steps,
        };
        Self {
            eth_block,
            eth_tx,
            block_ctants,
            geth_trace,
        }
    }
}

/// Generate a new mock tracer Transaction with preloaded data, useful for tests.
pub fn new_tracer_tx() -> external_tracer::Transaction {
    external_tracer::Transaction {
        origin: address!("0x00000000000000000000000000000000c014ba5e"),
        gas_limit: Word::from(1_000_000u64),
        target: Address::zero(),
    }
}

/// Generate a new mock tracer Account with preloaded data, useful for tests.
pub fn new_tracer_account(code: &Bytecode) -> external_tracer::Account {
    external_tracer::Account {
        address: new_tracer_tx().target,
        balance: Word::from(555u64),
        code: hex::encode(code.to_bytes()),
    }
}
