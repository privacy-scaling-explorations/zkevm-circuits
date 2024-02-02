//! Mock types and functions to generate Test environments for ZKEVM tests

use crate::{withdrawal::MockWithdrawal, MockAccount, MockBlock, MockTransaction};
use eth_types::{
    geth_types::{Account, BlockConstants, GethData, Withdrawal},
    Block, Error, GethExecTrace, Transaction, Word,
};
use external_tracer::{trace, TraceConfig};
use itertools::Itertools;

pub use external_tracer::LoggerConfig;

// TODO: merge it with TestContext.
// Here is the issue, https://github.com/privacy-scaling-explorations/zkevm-circuits/issues/1651

/// TestContext2 is an extended struct of TestContext. For more details and usage, see TestContext
/// file.
#[derive(Debug, Clone)]
pub struct TestContext2<const NACC: usize, const NTX: usize, const NWD: usize> {
    /// chain id
    pub chain_id: Word,
    /// Account list
    pub accounts: [Account; NACC],
    /// history hashes contains most recent 256 block hashes in history, where
    /// the latest one is at history_hashes[history_hashes.len() - 1].
    pub history_hashes: Vec<Word>,
    /// Block from geth
    pub eth_block: eth_types::Block<eth_types::Transaction>,
    /// Execution Trace from geth
    pub geth_traces: Vec<eth_types::GethExecTrace>,
}

impl<const NACC: usize, const NTX: usize, const NWD: usize> From<TestContext2<NACC, NTX, NWD>>
    for GethData
{
    fn from(ctx: TestContext2<NACC, NTX, NWD>) -> GethData {
        GethData {
            chain_id: ctx.chain_id,
            history_hashes: ctx.history_hashes,
            eth_block: ctx.eth_block,
            geth_traces: ctx.geth_traces.to_vec(),
            accounts: ctx.accounts.into(),
        }
    }
}

impl<const NACC: usize, const NTX: usize, const NWD: usize> TestContext2<NACC, NTX, NWD> {
    pub fn new_with_logger_config<FAcc, FTx, FWd, Fb>(
        history_hashes: Option<Vec<Word>>,
        acc_fns: FAcc,
        func_tx: FTx,
        func_wd: FWd,
        func_block: Fb,
        logger_config: LoggerConfig,
    ) -> Result<Self, Error>
    where
        FTx: FnOnce(Vec<&mut MockTransaction>, [MockAccount; NACC]),
        FWd: FnOnce(Vec<&mut MockWithdrawal>),
        Fb: FnOnce(&mut MockBlock, Vec<MockTransaction>) -> &mut MockBlock,
        FAcc: FnOnce([&mut MockAccount; NACC]),
    {
        let mut accounts: Vec<MockAccount> = vec![MockAccount::default(); NACC];
        // Build Accounts modifiers
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

        // Build Tx modifiers.
        func_tx(tx_refs, accounts.clone());

        let mut withdrawals = vec![MockWithdrawal::default(); NWD];
        let wd_refs = withdrawals.iter_mut().collect();

        // Build Withdrawal modifiers.
        func_wd(wd_refs);

        // Sets the transaction_idx and nonce after building the tx modifiers. Hence, if user has
        // overridden these values above using the tx modifiers, that will be ignored.
        let mut acc_tx_count = vec![0u64; NACC];
        transactions.iter_mut().enumerate().for_each(|(idx, tx)| {
            let idx = u64::try_from(idx).expect("Unexpected idx conversion error");
            tx.transaction_idx(idx);
            if let Some((pos, from_acc)) = accounts
                .iter()
                .find_position(|acc| acc.address == tx.from.address())
            {
                if tx.nonce.is_none() {
                    tx.nonce(from_acc.nonce + acc_tx_count[pos]);
                }
                if !tx.invalid {
                    acc_tx_count[pos] += 1;
                }
            }
        });

        let transactions: Vec<MockTransaction> =
            transactions.iter_mut().map(|tx| tx.build()).collect();

        // Build Block modifiers
        let mut block = MockBlock::default();
        block.transactions.extend_from_slice(&transactions);
        block.withdrawals.extend_from_slice(&withdrawals);
        func_block(&mut block, transactions.clone()).build();

        let chain_id = block.chain_id;
        let block = Block::<Transaction>::from(block);
        let accounts: [Account; NACC] = accounts
            .iter()
            .cloned()
            .map(Account::from)
            .collect_vec()
            .try_into()
            .expect("Mismatched acc len");

        let withdrawals: [Withdrawal; NWD] = withdrawals
            .iter()
            .cloned()
            .map(Withdrawal::from)
            .collect_vec()
            .try_into()
            .expect("Mismatched withdrawal len");

        let geth_traces = gen_geth_traces(
            chain_id,
            block.clone(),
            accounts.to_vec(),
            withdrawals.to_vec(),
            history_hashes.clone(),
            logger_config,
        )?;

        // Don't allow invalid transactions unless explicitly allowed to avoid unrelated tests from
        // passing simply because the test transaction was incorrectly set up.
        for (tx, geth_trace) in transactions.iter().zip(geth_traces.iter()) {
            if !tx.invalid && geth_trace.invalid {
                panic!(
                    "{:?}",
                    Error::TracingError(geth_trace.return_value.clone()).to_string()
                )
            }
            assert_eq!(
                tx.invalid, geth_trace.invalid,
                "tx has unexpected invalid status: {}",
                geth_trace.return_value
            );
        }

        Ok(Self {
            chain_id,
            accounts,
            history_hashes: history_hashes.unwrap_or_default(),
            eth_block: block,
            geth_traces,
        })
    }

    /// Create a new TestContext2 which starts with `NACC` default accounts and
    /// `NTX` default transactions.  Afterwards, we apply the `acc_fns`
    /// function to the accounts, the `func_tx` to the transactions and
    /// the `func_block` to the block, where each of these functions can
    /// mutate their target using the builder pattern. Finally an
    /// execution trace is generated of the resulting input block and state.
    pub fn new<FAcc, FTx, FWd, Fb>(
        history_hashes: Option<Vec<Word>>,
        acc_fns: FAcc,
        func_tx: FTx,
        func_wd: FWd,
        func_block: Fb,
    ) -> Result<Self, Error>
    where
        FTx: FnOnce(Vec<&mut MockTransaction>, [MockAccount; NACC]),
        FWd: FnOnce(Vec<&mut MockWithdrawal>),
        Fb: FnOnce(&mut MockBlock, Vec<MockTransaction>) -> &mut MockBlock,
        FAcc: FnOnce([&mut MockAccount; NACC]),
    {
        Self::new_with_logger_config(
            history_hashes,
            acc_fns,
            func_tx,
            func_wd,
            func_block,
            LoggerConfig::default(),
        )
    }
}

/// Generates execution traces for the transactions included in the provided
/// Block
pub fn gen_geth_traces(
    chain_id: Word,
    block: Block<Transaction>,
    accounts: Vec<Account>,
    withdrawals: Vec<Withdrawal>,
    history_hashes: Option<Vec<Word>>,
    logger_config: LoggerConfig,
) -> Result<Vec<GethExecTrace>, Error> {
    let trace_config = TraceConfig {
        chain_id,
        history_hashes: history_hashes.unwrap_or_default(),
        block_constants: BlockConstants::try_from(&block)?,
        accounts: accounts
            .iter()
            .map(|account| (account.address, account.clone()))
            .collect(),
        transactions: block
            .transactions
            .iter()
            .map(eth_types::geth_types::Transaction::from)
            .collect(),
        withdrawals,
        logger_config,
    };
    let traces = trace(&trace_config)?;
    Ok(traces)
}
