//! Types needed for Transaction

/// Transaction in a witness block
// pub mod ZkEvmTransaction {
use ethers_core::types::transaction::response;

use crate::geth_types::{ZkEvmCall, ZkEvmExecStep};

/// Transaction in a witness block
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct ZkEvmTransaction {
    /// Original tx definition from geth
    pub eth_tx: response::Transaction,

    /// Whether it's a create transaction
    pub is_create: bool,
    /// The call data length
    pub call_data_length: usize,
    /// The gas cost for transaction call data
    pub call_data_gas_cost: u64,
    /// The calls made in the transaction
    pub calls: Vec<ZkEvmCall::Call>,
    /// The steps executioned in the transaction
    pub steps: Vec<ZkEvmExecStep::ExecStep>,
}
// }
