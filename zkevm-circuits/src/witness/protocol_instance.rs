//! extra witness for taiko circuits

use std::iter;

use crate::{table::PiFieldTag, util::rlc_be_bytes};
use eth_types::{Address, Bytes, Field, Hash, ToBigEndian, ToWord, Word, H256};
use halo2_proofs::circuit::Value;
use keccak256::plain::Keccak;

// hash(anchor)
const ANCHOR_TX_METHOD_SIGNATURE: u32 = 0xda69d3db;

/// Taiko witness
#[derive(Debug, Default, Clone)]
pub struct ProtocolInstance {
    /// l1 signal service address
    pub l1_signal_service: Address,
    /// l2 signal service address
    pub l2_signal_service: Address,
    /// l2 contract address
    pub l2_contract: Address,
    /// meta hash
    pub meta_hash: MetaHash,
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

/// l1 meta hash
#[derive(Debug, Default, Clone)]
pub struct MetaHash {
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

impl MetaHash {
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
        result.extend_from_slice(&self.meta_hash.l1_hash.to_fixed_bytes());
        result.extend_from_slice(&self.signal_root.to_fixed_bytes());
        result.extend_from_slice(&self.meta_hash.l1_height.to_word().to_be_bytes());
        result.extend_from_slice(&(self.parent_gas_used as u64).to_word().to_be_bytes());
        result.into()
    }

    /// Assignments for pi table
    pub fn table_assignments<F: Field>(&self, randomness: Value<F>) -> [[Value<F>; 2]; 6] {
        [
            [
                Value::known(F::from(PiFieldTag::Null as u64)),
                Value::known(F::ZERO),
            ],
            [
                Value::known(F::from(PiFieldTag::MethodSign as u64)),
                Value::known(F::from(ANCHOR_TX_METHOD_SIGNATURE as u64)),
            ],
            [
                Value::known(F::from(PiFieldTag::L1Hash as u64)),
                rlc_be_bytes(&self.meta_hash.l1_hash.to_fixed_bytes(), randomness),
            ],
            [
                Value::known(F::from(PiFieldTag::L1SignalRoot as u64)),
                rlc_be_bytes(&self.signal_root.to_fixed_bytes(), randomness),
            ],
            [
                Value::known(F::from(PiFieldTag::L1Height as u64)),
                rlc_be_bytes(
                    &self.meta_hash.l1_height.to_word().to_be_bytes(),
                    randomness,
                ),
            ],
            [
                Value::known(F::from(PiFieldTag::ParentGasUsed as u64)),
                rlc_be_bytes(
                    &(self.parent_gas_used as u64).to_word().to_be_bytes(),
                    randomness,
                ),
            ],
        ]
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
