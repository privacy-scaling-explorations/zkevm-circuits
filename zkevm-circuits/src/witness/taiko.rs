//! extra witness for taiko circuits

use eth_types::{Address, Hash, H256};

/// Taiko witness
#[derive(Debug, Default)]
pub struct Taiko {
    /// l1 signal service address
    pub l1_signal_service: Address,
    /// l2 signal service address
    pub l2_signal_service: Address,
    /// l2 contract address
    pub l2_contract: Address,
    /// meta hash
    pub meta_hash: Hash,
    /// block hash value
    pub block_hash: Hash,
    /// the parent block hash
    pub parent_hash: Hash,
    /// signal root
    pub signal_root: Hash,
    /// extra message
    pub graffiti: H256,
    /// Prover address
    pub prover: Address,
    /// gas used
    pub gas_used: u32,
    /// parent gas used
    pub parent_gas_used: u32,
    /// blockMaxGasLimit
    pub block_max_gas_limit: u64,
    /// maxTransactionsPerBlock
    pub max_transactions_per_block: u64,
    /// maxBytesPerTxList
    pub max_bytes_per_tx_list: u64,
}
