//! Mock types and functions to generate Test enviroments for ZKEVM tests

use crate::{MockAccount, MockBlock, MockTransaction};
use eth_types::{
    geth_types::{Account, BlockConstants, GethData},
    Block, Error, GethExecTrace, Transaction, Word,
};
use external_tracer::{trace, TraceConfig};
use itertools::Itertools;

/// TestContext is a type that contains all the information from a block
/// required to build the circuit inputs.
#[derive(Debug)]
pub struct TestContext<const NACC: usize> {
    /// chain id
    pub chain_id: Word,
    /// Account list
    pub accounts: [Account; NACC],
    /// history hashes contains most recent 256 block hashes in history, where
    /// the lastest one is at history_hashes[history_hashes.len() - 1].
    pub history_hashes: Vec<Word>,
    /// Block from geth
    pub eth_block: eth_types::Block<eth_types::Transaction>,
    /// Execution Trace from geth
    pub geth_traces: Vec<eth_types::GethExecTrace>,
}

impl<const NACC: usize> From<TestContext<NACC>> for GethData {
    fn from(ctx: TestContext<NACC>) -> GethData {
        GethData {
            chain_id: ctx.chain_id,
            history_hashes: ctx.history_hashes,
            eth_block: ctx.eth_block,
            geth_traces: ctx.geth_traces,
            accounts: ctx.accounts.into(),
        }
    }
}

impl<const NACC: usize> TestContext<NACC> {
    pub fn new<FAcc, FTx, Fb>(
        history_hashes: Option<Vec<Word>>,
        acc_fns: FAcc,
        func_tx: FTx,
        func_block: Fb,
    ) -> Result<Self, Error>
    where
        FTx: FnOnce(&mut MockTransaction, [MockAccount; NACC]) -> &mut MockTransaction,
        Fb: FnOnce(&mut MockBlock, MockTransaction) -> &mut MockBlock,
        FAcc: FnOnce([&mut MockAccount; NACC]) -> [&mut MockAccount; NACC],
    {
        let mut accounts: Vec<MockAccount> = vec![MockAccount::default(); NACC];
        let account_refs = accounts
            .iter_mut()
            .collect_vec()
            .try_into()
            .expect("Mismatched len err");
        acc_fns(account_refs);
        let accounts: [MockAccount; NACC] = accounts
            .iter_mut()
            .map(|acc| acc.build())
            .collect_vec()
            .try_into()
            .expect("Mismatched acc len");

        let mut tx = MockTransaction::default();
        func_tx(&mut tx, accounts.clone()).build();

        let mut block = MockBlock::default();
        func_block(&mut block, tx.clone()).build();
        block.transactions = vec![tx];

        let transactions: Vec<Transaction> = block
            .transactions
            .iter()
            .cloned()
            .map(Transaction::from)
            .collect();
        let block = Block::<Transaction>::from(block);
        let accounts: [Account; NACC] = accounts
            .iter()
            .cloned()
            .map(Account::from)
            .collect_vec()
            .try_into()
            .expect("Mismatched acc len");

        let geth_traces = gen_geth_traces(block.clone(), accounts.clone(), history_hashes.clone())?;

        Ok(Self {
            chain_id: transactions[0].chain_id.unwrap_or_default(),
            accounts,
            history_hashes: history_hashes.unwrap_or_default(),
            eth_block: block,
            geth_traces,
        })
    }
}

/// Generates execution traces for the transactions included in the provided
/// Block
fn gen_geth_traces<const NACC: usize>(
    block: Block<Transaction>,
    accounts: [Account; NACC],
    history_hashes: Option<Vec<Word>>,
) -> Result<Vec<GethExecTrace>, Error> {
    let trace_config = TraceConfig {
        chain_id: block.transactions[0].chain_id.unwrap_or_default(),
        history_hashes: history_hashes.unwrap_or_default(),
        block_constants: BlockConstants::try_from(&block)?,
        accounts: accounts
            .iter()
            .map(|account| (account.address, account.clone()))
            .collect(),
        transactions: block
            .transactions
            .iter()
            .map(eth_types::geth_types::Transaction::from_eth_tx)
            .collect(),
    };
    trace(&trace_config)
}
