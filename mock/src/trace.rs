//! Mock Trace definition and builder related methods.

use std::collections::HashMap;

use eth_types::{
    geth_types::{Account, BlockConstants},
    Address, Transaction, Word,
};

#[derive(Clone, Debug)]
pub struct MockTrace {
    /// chain id
    pub chain_id: Word,
    /// history hashes contains most recent 256 block hashes in history, where
    /// the lastest one is at history_hashes[history_hashes.len() - 1].
    pub history_hashes: Vec<Word>,
    /// block constants
    pub block_constants: BlockConstants,
    /// accounts
    pub accounts: HashMap<Address, Account>,
    /// transaction
    pub transaction: Transaction,
}

impl MockTrace {
    /// Set chain_id field for the MockTrace.
    pub fn chain_id(&mut self, chain_id: Word) -> &mut Self {
        self.chain_id = chain_id;
        self
    }

    /// Set history_hashes field for the MockTrace.
    pub fn history_hashes(&mut self, history_hashes: Vec<Word>) -> &mut Self {
        self.history_hashes = history_hashes;
        self
    }

    /// Set block_constants field for the MockTrace.
    pub fn block_constants(&mut self, block_constants: BlockConstants) -> &mut Self {
        self.block_constants = block_constants;
        self
    }

    /// Set accounts field for the MockTrace.
    pub fn accounts<I: Iterator<Item = Account>>(&mut self, accounts: I) -> &mut Self {
        accounts.for_each(|acc| {
            self.accounts
                .insert(acc.address, acc)
                .expect("Error including account into trace");
        });
        self
    }

    /// Set transaction field for the MockTrace.
    pub fn transaction(&mut self, transaction: Transaction) -> &mut Self {
        self.transaction = transaction;
        self
    }
}
