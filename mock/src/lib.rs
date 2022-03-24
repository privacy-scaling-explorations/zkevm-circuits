//! Mock types and functions to generate GethData used for tests

use eth_types::{
    address,
    bytecode::Bytecode,
    evm_types::Gas,
    geth_types::{Account, BlockConstants, GethData, Transaction},
    Address, Block, Bytes, Error, Hash, Word, U64,
};
use external_tracer::{trace, TraceConfig};
use lazy_static::lazy_static;
mod account;
mod block;
mod test_ctx;
mod trace;
mod transaction;

pub use account::MockAccount;
pub use block::MockBlock;
pub use test_ctx::TestContext;
pub use trace::MockTrace;
pub use transaction::MockTransaction;

lazy_static! {
    /// Mock coinbase value
    static ref MOCK_COINBASE: Address =
        address!("0x00000000000000000000000000000000c014ba5e");
    /// Mock gasprice value
    static ref MOCK_GASPRICE: Word = Word::from(1u8);
    /// Mock chain ID value
    static ref MOCK_CHAIN_ID: Word = Word::from(1338u64);
    /// Mock accounts loaded with ETH to use for test cases.
    pub static ref MOCK_ACCOUNTS: Vec<Address> = vec![
        address!("0x0000000000000000000000000000000000000111"),
        address!("0x0000000000000000000000000000000000000222"),
        address!("0x0000000000000000000000000000000000000333"),
        address!("0x0000000000000000000000000000000000000444"),
        address!("0x0000000000000000000000000000000000000555"),
    ];
}
