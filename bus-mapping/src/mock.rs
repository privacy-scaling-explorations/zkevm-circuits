//! Mock types and functions to generate mock data useful for tests

use crate::{
    circuit_input_builder::{
        get_state_accesses, Block, CircuitInputBuilder, CircuitsParams, DynamicCParams,
        FixedCParams,
    },
    state_db::{self, CodeDB, StateDB},
};
use eth_types::{geth_types::GethData, Word};

/// BlockData is a type that contains all the information from a block required
/// to build the circuit inputs.
#[derive(Debug)]
pub struct BlockData<C: CircuitsParams> {
    /// StateDB
    pub sdb: StateDB,
    /// CodeDB
    pub code_db: CodeDB,
    /// chain id
    pub chain_id: Word,
    /// history hashes contains most recent 256 block hashes in history, where
    /// the lastest one is at history_hashes[history_hashes.len() - 1].
    pub history_hashes: Vec<Word>,
    /// Block from geth
    pub eth_block: eth_types::Block<eth_types::Transaction>,
    /// Execution Trace from geth
    pub geth_traces: Vec<eth_types::GethExecTrace>,
    /// Circuits setup parameters
    pub circuits_params: C,
}

impl<C: CircuitsParams> BlockData<C> {
    /// Generate a new CircuitInputBuilder initialized with the context of the
    /// BlockData.
    pub fn new_circuit_input_builder(&self) -> CircuitInputBuilder<C> {
        CircuitInputBuilder::new(
            self.sdb.clone(),
            self.code_db.clone(),
            Block::new(
                self.chain_id,
                self.history_hashes.clone(),
                Word::default(),
                &self.eth_block,
            )
            .unwrap(),
            self.circuits_params,
        )
    }

    fn init_dbs(geth_data: &GethData) -> (StateDB, CodeDB) {
        let mut sdb = StateDB::new();
        let mut code_db = CodeDB::new();

        let access_set = get_state_accesses(&geth_data.eth_block, &geth_data.geth_traces)
            .expect("state accesses");
        // Initialize all accesses accounts to zero
        for addr in access_set.state.keys() {
            sdb.set_account(addr, state_db::Account::zero());
        }

        for account in geth_data.accounts {
            code_db.insert(account.code.to_vec());
            sdb.set_account(&account.address, state_db::Account::from(account.clone()));
        }
        (sdb, code_db)
    }
}
impl BlockData<FixedCParams> {
    /// Create a new block from the given Geth data.
    pub fn new_from_geth_data_with_params(
        geth_data: GethData,
        circuits_params: FixedCParams,
    ) -> Self {
        let (sdb, code_db) = Self::init_dbs(&geth_data);

        Self {
            sdb,
            code_db,
            chain_id: geth_data.chain_id,
            history_hashes: geth_data.history_hashes,
            eth_block: geth_data.eth_block,
            geth_traces: geth_data.geth_traces,
            circuits_params,
        }
    }
}

impl BlockData<DynamicCParams> {
    /// Create a new block from the given Geth data with default CircuitsParams.
    pub fn new_from_geth_data(geth_data: GethData) -> Self {
        let (sdb, code_db) = Self::init_dbs(&geth_data);

        Self {
            sdb,
            code_db,
            chain_id: geth_data.chain_id,
            history_hashes: geth_data.history_hashes,
            eth_block: geth_data.eth_block,
            geth_traces: geth_data.geth_traces,
            circuits_params: DynamicCParams {},
        }
    }
}
