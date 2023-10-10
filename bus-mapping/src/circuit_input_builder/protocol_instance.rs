//! extra witness for taiko circuits

use std::iter;

use eth_types::{Address, Bytes, Hash, ToBigEndian, ToWord, Word, H256};
use keccak256::plain::Keccak;
use mock::{
    MOCK_ANCHOR_GAS_LIMIT, MOCK_ANCHOR_L1_HASH, MOCK_ANCHOR_L1_HIGHT, MOCK_ANCHOR_PARENT_GAS_USED,
    MOCK_ANCHOR_SIGNAL_ROOT, MOCK_TAIKO_L2_ADDRESS, MOCK_TAIKO_TREASURY_ADDRESS
};

pub use mock::ANCHOR_TX_METHOD_SIGNATURE;

/// Taiko witness
#[derive(Debug, Clone)]
pub struct ProtocolInstance {
    /// l1 signal service address
    pub l1_signal_service: Address,
    /// l2 signal service address
    pub l2_signal_service: Address,
    /// l2 contract address
    pub l2_contract: Address,
    /// meta hash from l1
    pub meta_data: MetaData,
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

    /// anchor gas limit
    pub anchor_gas_limit: u64,
}

impl Default for ProtocolInstance {
    fn default() -> Self {
        Self {
            anchor_gas_limit: MOCK_ANCHOR_GAS_LIMIT.as_u64(),
            meta_data: MetaData {
                l1_hash: *MOCK_ANCHOR_L1_HASH,
                l1_height: *MOCK_ANCHOR_L1_HIGHT,
                treasury: *MOCK_TAIKO_TREASURY_ADDRESS,
                ..Default::default()
            },
            signal_root: *MOCK_ANCHOR_SIGNAL_ROOT,
            parent_gas_used: *MOCK_ANCHOR_PARENT_GAS_USED,
            l1_signal_service: Address::default(),
            l2_signal_service: Address::default(),
            l2_contract: *MOCK_TAIKO_L2_ADDRESS,
            block_hash: Hash::default(),
            parent_hash: Hash::default(),
            graffiti: H256::default(),
            prover: Address::default(),
            gas_used: 0,
            block_max_gas_limit: 0,
            max_transactions_per_block: 0,
            max_bytes_per_tx_list: 0,
        }
    }
}

/// l1 meta hash
#[derive(Debug, Clone)]
pub struct MetaData {
    /// meta id
    pub id: u64,
    /// meta timestamp
    pub timestamp: u64,
    /// l1 block height
    pub l1_height: u64,
    /// l1 block hash
    pub l1_hash: Hash,
    /// l1 block mix hash
    pub l1_mix_hash: Hash,
    /// deposits processed
    pub deposits_processed: Hash,
    /// tx list hash
    pub tx_list_hash: Hash,
    /// tx list byte start
    pub tx_list_byte_start: u32, // u24
    /// tx list byte end
    pub tx_list_byte_end: u32, // u24
    /// gas limit
    pub gas_limit: u32,
    /// beneficiary
    pub beneficiary: Address,
    /// treasury
    pub treasury: Address,
}

impl Default for MetaData {
    fn default() -> Self {
        Self {
            id: 0,
            timestamp: 0,
            l1_height: 0,
            l1_hash: Hash::default(),
            l1_mix_hash: Hash::default(),
            deposits_processed: Hash::default(),
            tx_list_hash: Hash::default(),
            tx_list_byte_start: 0,
            tx_list_byte_end: 0,
            gas_limit: 0,
            beneficiary: Address::default(),
            treasury: *MOCK_TAIKO_TREASURY_ADDRESS,
        }
    }
}

/// left shift x by n bits
pub fn left_shift<T: ToWord>(x: T, n: u32) -> Word {
    assert!(n < 256);
    if n < 128 {
        return x.to_word() * Word::from(2u128.pow(n));
    }
    let mut bits = [0; 32];
    bits[..16].copy_from_slice(2u128.pow(n - 128).to_be_bytes().as_ref());
    bits[16..].copy_from_slice(0u128.to_be_bytes().as_ref());
    x.to_word() * Word::from(&bits[..])
}

impl MetaData {
    /// get the hash of meta hash
    pub fn hash(&self) -> Hash {
        let field0 = left_shift(self.id, 192)
            + left_shift(self.timestamp, 128)
            + left_shift(self.l1_height, 64);

        let field5 = left_shift(self.tx_list_byte_start as u64, 232)
            + left_shift(self.tx_list_byte_end as u64, 208)
            + left_shift(self.gas_limit as u64, 176)
            + left_shift(self.beneficiary, 16);

        let field6 = left_shift(self.treasury, 96);

        let input: Vec<u8> = iter::empty()
            .chain(field0.to_be_bytes())
            .chain(self.l1_hash.to_fixed_bytes())
            .chain(self.l1_mix_hash.to_fixed_bytes())
            .chain(self.deposits_processed.to_fixed_bytes())
            .chain(self.tx_list_hash.to_fixed_bytes())
            .chain(field5.to_be_bytes())
            .chain(field6.to_be_bytes())
            .collect();
        let mut keccak = Keccak::default();
        keccak.update(&input);
        let output = keccak.digest();
        Hash::from_slice(&output)
    }
}

impl ProtocolInstance {
    /// gen anchor call
    // anchor(l1_hash,signal_root,l1_height,parent_gas_used)
    pub fn anchor_call(&self) -> Bytes {
        let mut result = Vec::new();
        result.extend_from_slice(&ANCHOR_TX_METHOD_SIGNATURE.to_be_bytes());
        result.extend_from_slice(&self.meta_data.l1_hash.to_fixed_bytes());
        result.extend_from_slice(&self.signal_root.to_fixed_bytes());
        result.extend_from_slice(&self.meta_data.l1_height.to_word().to_be_bytes());
        result.extend_from_slice(&(self.parent_gas_used as u64).to_word().to_be_bytes());
        result.into()
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use super::*;
    #[test]
    fn test_left_shift() {
        let _field0 = left_shift(1u64, 192) + left_shift(1688574587u64, 128) + left_shift(9u64, 64);

        let _field5 = left_shift(0u32 as u64, 232)
            + left_shift(124u32 as u64, 208)
            + left_shift(21000u32 as u64, 176)
            + left_shift(
                Address::from_str("0000777700000000000000000000000000000001").unwrap(),
                16,
            );
        let _field6 = left_shift(
            Address::from_str("df09A0afD09a63fb04ab3573922437e1e637dE8b").unwrap(),
            96,
        );

        let _field9 = left_shift(
            Address::from_str("70997970C51812dc3A010C7d01b50e0d17dc79C8").unwrap(),
            96,
        ) + left_shift(0u64, 64)
            + left_shift(141003u64, 32);

        let _field10 =
            left_shift(6000000u64, 192) + left_shift(79u64, 128) + left_shift(120000u64, 64);
    }
}
