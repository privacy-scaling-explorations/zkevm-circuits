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
pub struct TestContext<const NACC: usize, const NTX: usize> {
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
    pub geth_traces: [eth_types::GethExecTrace; NTX],
}

impl<const NACC: usize, const NTX: usize> From<TestContext<NACC, NTX>> for GethData {
    fn from(ctx: TestContext<NACC, NTX>) -> GethData {
        GethData {
            chain_id: ctx.chain_id,
            history_hashes: ctx.history_hashes,
            eth_block: ctx.eth_block,
            geth_traces: ctx.geth_traces.to_vec(),
            accounts: ctx.accounts.into(),
        }
    }
}

impl<const NACC: usize, const NTX: usize> TestContext<NACC, NTX> {
    pub fn new<FAcc, FTx, Fb>(
        history_hashes: Option<Vec<Word>>,
        acc_fns: FAcc,
        func_tx: FTx,
        func_block: Fb,
    ) -> Result<Self, Error>
    where
        FTx: FnOnce(Vec<&mut MockTransaction>, [MockAccount; NACC]),
        Fb: FnOnce(&mut MockBlock, Vec<MockTransaction>) -> &mut MockBlock,
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

        let mut transactions = vec![MockTransaction::default(); NTX];
        let tx_refs = transactions.iter_mut().collect();
        func_tx(tx_refs, accounts.clone());
        let transactions: Vec<MockTransaction> =
            transactions.iter_mut().map(|tx| tx.build()).collect();

        let mut block = MockBlock::default();
        block.transactions.extend_from_slice(&transactions);
        func_block(&mut block, transactions).build();

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
fn gen_geth_traces<const NACC: usize, const NTX: usize>(
    block: Block<Transaction>,
    accounts: [Account; NACC],
    history_hashes: Option<Vec<Word>>,
) -> Result<[GethExecTrace; NTX], Error> {
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
    let traces = trace(&trace_config)?;
    let result: [GethExecTrace; NTX] = traces.try_into().expect("Unexpected len mismatch");
    Ok(result)
}
