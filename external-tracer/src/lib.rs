//! This module generates traces by connecting to an external tracer

use eth_types::evm_types::Gas;
use eth_types::geth_types::{
    Account, BlockConstants, GethData, Transaction, MOCK_CHAIN_ID,
    MOCK_COINBASE,
};
use eth_types::{
    self, fix_geth_trace_memory_size, Address, Block, Bytes, ChainConstants,
    Error, GethExecStep, GethExecTrace, Hash, Word, U64,
};
use geth_utils;
use serde::Serialize;

/// Create a new block with a single tx that executes the code found in the
/// account with address 0x0 (which can call code in the other accounts),
/// with the given gas limit.
/// The trace will be generated automatically with the external_tracer
/// from the accounts code.
pub fn create_tx_by_accounts(
    accounts: &[Account],
    gas: Gas,
) -> Result<GethData, Error> {
    let eth_block = new_block();
    let mut eth_tx = new_tx(&eth_block);
    eth_tx.gas = Word::from(gas.0);
    let c_constant = new_chain_constants();
    let b_constant = BlockConstants::from_eth_block(
        &eth_block,
        &Word::from(c_constant.chain_id),
    );
    let tracer_tx = Transaction::from_eth_tx(&eth_tx);
    let geth_trace = GethExecTrace {
        gas: Gas(eth_tx.gas.as_u64()),
        failed: false,
        struct_logs: trace(&b_constant, &tracer_tx, accounts)?.to_vec(),
    };

    Ok(GethData {
        eth_block,
        eth_tx,
        c_constant,
        b_constant,
        geth_trace,
    })
}

/// Create a new block with a single tx that leads to the geth_steps passed
/// by argument.
pub fn create_tx_by_steps(geth_steps: Vec<GethExecStep>) -> GethData {
    let eth_block = new_block();
    let eth_tx = new_tx(&eth_block);
    let c_constant = new_chain_constants();
    let b_constant = BlockConstants::from_eth_block(
        &eth_block,
        &Word::from(c_constant.chain_id),
    );
    let geth_trace = eth_types::GethExecTrace {
        gas: Gas(eth_tx.gas.as_u64()),
        failed: false,
        struct_logs: geth_steps,
    };

    GethData {
        eth_block,
        eth_tx,
        c_constant,
        b_constant,
        geth_trace,
    }
}

/// Generate a new mock block with preloaded data, useful for tests.
fn new_block() -> Block<()> {
    eth_types::Block {
        hash: Some(Hash::zero()),
        parent_hash: Hash::zero(),
        uncles_hash: Hash::zero(),
        author: Address::zero(),
        state_root: Hash::zero(),
        transactions_root: Hash::zero(),
        receipts_root: Hash::zero(),
        number: Some(U64([123456u64])),
        gas_used: Word::from(15_000_000u64),
        gas_limit: Word::from(15_000_000u64),
        base_fee_per_gas: Some(Word::from(97u64)),
        extra_data: Bytes::default(),
        logs_bloom: None,
        timestamp: Word::from(1633398551u64),
        difficulty: Word::from(0x200000u64),
        total_difficulty: None,
        seal_fields: Vec::new(),
        uncles: Vec::new(),
        transactions: Vec::new(),
        size: None,
        mix_hash: None,
        nonce: Some(U64::zero()),
    }
}

/// Generate a new mock chain constants, useful for tests.
fn new_chain_constants() -> eth_types::ChainConstants {
    ChainConstants {
        chain_id: MOCK_CHAIN_ID,
    }
}

/// Generate a new mock transaction with preloaded data, useful for tests.
fn new_tx<TX>(block: &Block<TX>) -> eth_types::Transaction {
    eth_types::Transaction {
        hash: Hash::zero(),
        nonce: Word::zero(),
        block_hash: block.hash,
        block_number: block.number,
        transaction_index: Some(U64::zero()),
        from: *MOCK_COINBASE,
        to: Some(Address::zero()),
        value: Word::zero(),
        gas_price: Some(Word::zero()),
        gas: Word::from(1_000_000u64),
        input: Bytes::default(),
        v: U64::zero(),
        r: Word::zero(),
        s: Word::zero(),
        transaction_type: Some(U64::zero()),
        access_list: None,
        max_priority_fee_per_gas: Some(Word::zero()),
        max_fee_per_gas: Some(Word::zero()),
        chain_id: Some(Word::from(MOCK_CHAIN_ID)),
    }
}

#[derive(Debug, Clone, Serialize)]
struct GethConfig {
    block_constants: BlockConstants,
    transaction: Transaction,
    accounts: Vec<Account>,
}

/// Creates a trace for the specified config
fn trace(
    block_constants: &BlockConstants,
    tx: &Transaction,
    accounts: &[Account],
) -> Result<Vec<GethExecStep>, Error> {
    let geth_config = GethConfig {
        block_constants: block_constants.clone(),
        transaction: tx.clone(),
        accounts: accounts.to_vec(),
    };

    // Get the trace
    let trace_string =
        geth_utils::trace(&serde_json::to_string(&geth_config).unwrap())
            .map_err(|_| Error::TracingError)?;

    let mut trace: Vec<GethExecStep> =
        serde_json::from_str(&trace_string).map_err(Error::SerdeError)?;
    fix_geth_trace_memory_size(&mut trace);
    Ok(trace)
}
