//! Mock types and functions to generate Test environments for ZKEVM tests

use crate::{eth, MockAccount, MockBlock, MockTransaction, TestContext2};
use eth_types::{
    geth_types::{Account, GethData},
    Bytecode, Error, Word,
};
use helpers::*;

pub use external_tracer::LoggerConfig;

/// TestContext is a type that contains all the information from a block
/// required to build the circuit inputs.
///
/// It is specifically used to generate Test cases with very precise information
/// details about any specific part of a block. That includes of course, its
/// transactions too and the accounts involved in all of them.
///
/// The intended way to interact with the structure is through the fn `new`
/// which is designed to return a [`GethData`] which then can be used to query
/// any specific part of the logs generated by the transactions executed within
/// this context.
///
/// ## Example
/// ```rust
/// use eth_types::evm_types::{stack::Stack, OpcodeId};
/// use eth_types::{address, bytecode, geth_types::GethData, word, Bytecode, ToWord, Word};
/// use lazy_static::lazy_static;
/// use mock::test_ctx::{helpers::*, TestContext};
/// // code_a calls code
/// // jump to 0x10 which is outside the code (and also not marked with
///         // JUMPDEST)
/// let code = bytecode! {
///     PUSH1(0x10)
///     JUMP
///     STOP
/// };
/// let code_a = bytecode! {
///     PUSH1(0x0) // retLength
///     PUSH1(0x0) // retOffset
///     PUSH1(0x0) // argsLength
///     PUSH1(0x0) // argsOffset
///     PUSH32(address!("0x000000000000000000000000000000000cafe001").to_word()) // addr
///     PUSH32(0x1_0000) // gas
///     STATICCALL
///     PUSH2(0xaa)
/// };
/// let index = 8; // JUMP
///
/// // Get the execution steps from the external tracer
/// let block: GethData = TestContext::<3, 2>::new(
///     None,
///     |accs| {
///         accs[0]
///             .address(address!("0x0000000000000000000000000000000000000000"))
///             .code(code_a);
///         accs[1].address(address!("0x000000000000000000000000000000000cafe001")).code(code);
///         accs[2]
///             .address(address!("0x000000000000000000000000000000000cafe002"))
///             .balance(Word::from(1u64 << 30));
///     },
///     |mut txs, accs| {
///         txs[0].to(accs[0].address).from(accs[2].address);
///         txs[1]
///             .to(accs[1].address)
///             .from(accs[2].address);
///     },
///     |block, _tx| block.number(0xcafeu64),
/// )
/// .unwrap()
/// .into();
///
/// // Now we can start generating the traces and items we need to inspect
/// // the behaviour of the generated env.
/// ```
#[derive(Debug, Clone)]
pub struct TestContext<const NACC: usize, const NTX: usize> {
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
    pub fn new_with_logger_config<FAcc, FTx, Fb>(
        history_hashes: Option<Vec<Word>>,
        acc_fns: FAcc,
        func_tx: FTx,
        func_block: Fb,
        logger_config: LoggerConfig,
    ) -> Result<Self, Error>
    where
        FTx: FnOnce(Vec<&mut MockTransaction>, [MockAccount; NACC]),
        Fb: FnOnce(&mut MockBlock, Vec<MockTransaction>) -> &mut MockBlock,
        FAcc: FnOnce([&mut MockAccount; NACC]),
    {
        let test_ctx2 = TestContext2::<NACC, NTX, 0>::new_with_logger_config(
            history_hashes,
            acc_fns,
            func_tx,
            |_| {},
            func_block,
            logger_config,
        )?;

        Ok(Self {
            chain_id: test_ctx2.chain_id,
            accounts: test_ctx2.accounts,
            history_hashes: test_ctx2.history_hashes.clone(),
            eth_block: test_ctx2.eth_block,
            geth_traces: test_ctx2.geth_traces,
        })
    }

    /// Create a new TestContext which starts with `NACC` default accounts and
    /// `NTX` default transactions.  Afterwards, we apply the `acc_fns`
    /// function to the accounts, the `func_tx` to the transactions and
    /// the `func_block` to the block, where each of these functions can
    /// mutate their target using the builder pattern. Finally an
    /// execution trace is generated of the resulting input block and state.
    pub fn new<FAcc, FTx, Fb>(
        history_hashes: Option<Vec<Word>>,
        acc_fns: FAcc,
        func_tx: FTx,
        func_block: Fb,
    ) -> Result<Self, Error>
    where
        FTx: FnOnce(Vec<&mut MockTransaction>, [MockAccount; NACC]),
        Fb: FnOnce(&mut MockBlock, Vec<MockTransaction>) -> &mut MockBlock,
        FAcc: FnOnce([&mut MockAccount; NACC]),
    {
        Self::new_with_logger_config(
            history_hashes,
            acc_fns,
            func_tx,
            func_block,
            LoggerConfig::default(),
        )
    }

    /// Returns a simple TestContext setup with a single tx executing the
    /// bytecode passed as parameters. The balances of the 2 accounts and
    /// addresses are the ones used in [`TestContext::
    /// account_0_code_account_1_no_code`]. Extra accounts, txs and/or block
    /// configs are set as [`Default`].
    pub fn simple_ctx_with_bytecode(bytecode: Bytecode) -> Result<TestContext<2, 1>, Error> {
        TestContext::new(
            None,
            account_0_code_account_1_no_code(bytecode),
            tx_from_1_to_0,
            |block, _txs| block,
        )
    }
}

/// Collection of helper functions which contribute to specific routines on the
/// builder pattern used to construct [`TestContext`]s.
pub mod helpers {
    use super::*;
    use crate::MOCK_ACCOUNTS;

    /// Generate a simple setup which adds balance to two default accounts from
    /// [`static@MOCK_ACCOUNTS`]:
    /// - 0x000000000000000000000000000000000cafe111
    /// - 0x000000000000000000000000000000000cafe222
    /// And injects the provided bytecode into the first one.
    pub fn account_0_code_account_1_no_code(code: Bytecode) -> impl FnOnce([&mut MockAccount; 2]) {
        |accs| {
            accs[0]
                .address(MOCK_ACCOUNTS[0])
                .balance(eth(10))
                .code(code);
            accs[1].address(MOCK_ACCOUNTS[1]).balance(eth(10));
        }
    }

    /// Generate a single transaction from the second account of the list to the
    /// first one.
    pub fn tx_from_1_to_0(mut txs: Vec<&mut MockTransaction>, accs: [MockAccount; 2]) {
        txs[0].from(accs[1].address).to(accs[0].address);
    }
}

#[cfg(test)]
mod tests {
    use eth_types::{address, U256, U64};

    use super::{eth, TestContext};

    #[test]
    fn test_nonce() {
        let block = TestContext::<2, 5>::new(
            None,
            |accs| {
                accs[0]
                    .address(address!("0x0000000000000000000000000000000000000000"))
                    .balance(eth(10));
                accs[1]
                    .address(address!("0x000000000000000000000000000000000cafe001"))
                    .balance(eth(10))
                    .nonce(100);
            },
            |mut txs, accs| {
                txs[0].from(accs[0].address);
                txs[1].from(accs[0].address);
                txs[2].from(accs[1].address);
                txs[3].from(accs[1].address);
                txs[4].from(accs[1].address);
            },
            |block, _tx| block.number(0xcafeu64),
        )
        .unwrap();

        // account 0 starts with nonce default 0
        assert_eq!(block.eth_block.transactions[0].nonce, U256::from(0));
        assert_eq!(block.eth_block.transactions[1].nonce, U256::from(1));

        // account 1 starts with nonce specified 100
        assert_eq!(block.eth_block.transactions[2].nonce, U256::from(100));
        assert_eq!(block.eth_block.transactions[3].nonce, U256::from(101));
        assert_eq!(block.eth_block.transactions[4].nonce, U256::from(102)); // 12345 is ignored

        // nonce in accounts is the nonce before the block processing
        assert_eq!(block.accounts[0].nonce, U64::from(0));
        assert_eq!(block.accounts[1].nonce, U64::from(100));
    }
}
