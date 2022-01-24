//! Mock types and functions to generate mock data useful for tests

use crate::bytecode::Bytecode;
use crate::circuit_input_builder::CircuitInputBuilder;
use crate::state_db::{self, CodeDB, StateDB};
use crate::Error;
use eth_types::geth_types::{
    Account, BlockConstants, GethData, Transaction, MOCK_COINBASE,
};
use eth_types::{self, Address, Bytes, ChainConstants, Word};
use std::collections::HashMap;

#[cfg(test)]
use eth_types::{address, evm_types::Gas, geth_types::MOCK_GAS};

/// BlockData is a type that contains all the information from a block required
/// to build the circuit inputs.
#[derive(Debug)]
pub struct BlockData {
    /// StateDB
    pub sdb: StateDB,
    /// CodeDB
    pub code_db: CodeDB,
    /// Block from geth
    pub eth_block: eth_types::Block<()>,
    /// Transaction from geth
    pub eth_tx: eth_types::Transaction,
    /// Constants
    pub c_constant: ChainConstants,
    /// Constants
    pub b_constant: BlockConstants,
    /// Execution Trace from geth
    pub geth_trace: eth_types::GethExecTrace,
}

impl BlockData {
    /// Generate a new CircuitInputBuilder initialized with the context of the
    /// BlockData.
    pub fn new_circuit_input_builder(&self) -> CircuitInputBuilder {
        CircuitInputBuilder::new(
            self.sdb.clone(),
            self.code_db.clone(),
            &self.eth_block,
            self.c_constant.clone(),
            self.b_constant.clone(),
        )
    }

    /// Create a new block with a single tx that executes the code found in the
    /// account with address 0x0 (which can call code in the other accounts),
    /// with the given Geth data.
    pub fn new_single_tx_trace(
        accounts: &[Account],
        geth_data: GethData,
    ) -> Result<Self, Error> {
        let mut sdb = StateDB::new();
        let mut code_db = CodeDB::new();
        for account in accounts {
            let code_hash = code_db.insert(account.code.to_vec());
            sdb.set_account(
                &account.address,
                state_db::Account {
                    nonce: Word::zero(),
                    balance: account.balance,
                    storage: HashMap::new(),
                    code_hash,
                },
            );
        }
        Ok(Self {
            sdb,
            code_db,
            eth_block: geth_data.eth_block,
            eth_tx: geth_data.eth_tx,
            c_constant: geth_data.c_constant,
            b_constant: geth_data.b_constant,
            geth_trace: geth_data.geth_trace,
        })
    }

    /// Slice trace steps to start at the "start" position as tagged in code.
    pub fn slice_from_code_start(&mut self, code: &Bytecode) {
        self.geth_trace.struct_logs =
            self.geth_trace.struct_logs[code.get_pos("start")..].to_vec();
    }
}

#[cfg(test)]
impl BlockData {
    /// Create a new block with a single tx that executes the code found in the
    /// account with address 0x0 (which can call code in the other accounts).
    /// The trace will be generated automatically with the external_tracer
    /// from the accounts code.
    fn new_single_tx_trace_accounts(
        accounts: &[Account],
    ) -> Result<Self, Error> {
        let geth_data =
            external_tracer::create_tx_by_accounts(accounts, Gas(MOCK_GAS))?;
        Self::new_single_tx_trace(accounts, geth_data)
    }

    /// Create a new block with a single tx that executes the code passed by
    /// argument. The trace will be generated automatically with the
    /// external_tracer from the code.
    pub fn new_single_tx_trace_code(code: &Bytecode) -> Result<Self, Error> {
        let tracer_account = new_tracer_account(code);
        Self::new_single_tx_trace_accounts(&[tracer_account])
    }

    /// Create a new block with a single tx with the given gas limit that
    /// executes the code passed by argument. The trace will be generated
    /// automatically with the external_tracer from the code.
    pub fn new_single_tx_trace_code_gas(
        code: &Bytecode,
        gas: Gas,
    ) -> Result<Self, Error> {
        let accounts = [new_tracer_account(code)];
        let geth_data = external_tracer::create_tx_by_accounts(&accounts, gas)?;
        Self::new_single_tx_trace(&accounts, geth_data)
    }

    /// Create a new block with a single tx that executes the code_a passed by
    /// argument, with code_b deployed at address 0x123. The trace will be
    /// generated automatically with the external_tracer from the code.
    pub fn new_single_tx_trace_code_2(
        code_a: &Bytecode,
        code_b: &Bytecode,
    ) -> Result<Self, Error> {
        let tracer_account_a = new_tracer_account(code_a);
        let mut tracer_account_b = new_tracer_account(code_b);
        tracer_account_b.address =
            address!("0x0000000000000000000000000000000000000123");
        Self::new_single_tx_trace_accounts(&[
            tracer_account_a,
            tracer_account_b,
        ])
    }

    /// Create a new block with a single tx that executes the code passed by
    /// argument. The trace will be generated automatically with the
    /// external_tracer from the code. The trace steps will start at the
    /// "start" position as tagged in the code.
    pub fn new_single_tx_trace_code_at_start(
        code: &Bytecode,
    ) -> Result<Self, Error> {
        let mut mock = Self::new_single_tx_trace_code(code)?;
        mock.slice_from_code_start(code);
        Ok(mock)
    }

    /// Create a new block with a single tx that leads to the geth_steps passed
    /// by argument. The returned BlockData contains an empty StateDB and
    /// CodeDB.
    pub fn new_single_tx_geth_steps(
        geth_steps: Vec<eth_types::GethExecStep>,
    ) -> Self {
        let geth_data = external_tracer::create_tx_by_steps(geth_steps);
        let sdb = StateDB::new();
        let code_db = CodeDB::new();
        Self {
            sdb,
            code_db,
            eth_block: geth_data.eth_block,
            eth_tx: geth_data.eth_tx,
            c_constant: geth_data.c_constant,
            b_constant: geth_data.b_constant,
            geth_trace: geth_data.geth_trace,
        }
    }
}

/// Generate a new mock tracer Transaction with preloaded data, useful for
/// tests.
pub fn new_tracer_tx() -> Transaction {
    Transaction {
        origin: *MOCK_COINBASE,
        gas_limit: Word::from(1_000_000u64),
        target: Address::zero(),
    }
}

/// Generate a new mock tracer Account with preloaded data, useful for tests.
pub fn new_tracer_account(code: &Bytecode) -> Account {
    Account {
        address: new_tracer_tx().target,
        balance: Word::from(555u64),
        code: Bytes::from(code.to_vec()),
    }
}
