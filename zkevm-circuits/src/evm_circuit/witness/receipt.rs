use digest::Digest;
use eth_types::{ToLittleEndian, Word};
use halo2_proofs::{arithmetic::FieldExt, plonk::Expression};
use sha3::Keccak256;

use crate::{evm_circuit::util::RandomLinearCombination, impl_expr};

use super::{
    common::{handle_prefix, handle_u256},
    rlp_witness::{RlpWitnessGen, RlpWitnessRow},
    Receipt,
};

/// Tags used to tags rows in the RLP circuit for a tx receipt.
#[derive(Clone, Copy, Debug)]
pub enum RlpReceiptTag {
    /// Denotes the prefix bytes indicating the "length of length" and/or
    /// "length" of the tx receipt's RLP-encoding.
    Prefix = 1,
    /// Denotes the byte for the receipt's status.
    Status,
    /// Denotes the bytes representing the cumulative gas used.
    CumulativeGasUsed,
    /// Denotes the bytes prefixing the bloom filter bytes.
    BloomPrefix,
    /// Denotes the 256-bytes representing bloom filter.
    Bloom,
    /// Denotes the bytes prefixing the list of logs.
    LogsPrefix,
    /// Denotes the bytes prefixing a single log.
    LogPrefix,
    /// Denotes the byte prefixing the log.address.
    LogAddressPrefix,
    /// Denotes the 20-bytes representing the log.address.
    LogAddress,
    /// Denotes the bytes prefixing log.topics.
    LogTopicsPrefix,
    /// Denotes the bytes prefixing a single log.topic.
    LogTopicPrefix,
    /// Denotes the bytes representing a single log.topic.
    LogTopic,
    /// Denotes the bytes prefixing log.data.
    LogDataPrefix,
    /// Denotes the bytes representing log.data.
    LogData,
}

impl_expr!(RlpReceiptTag);

/// Denotes the number of possible tag values for a tx receipt row.
pub const N_RECEIPT_TAGS: usize = 14;

impl<F: FieldExt> RlpWitnessGen<F> for Receipt {
    fn gen_witness(&self, randomness: F) -> Vec<RlpWitnessRow<F>> {
        let rlp_data = rlp::encode(self);
        let hash = Word::from_big_endian(Keccak256::digest(&rlp_data).as_slice());
        let hash = RandomLinearCombination::random_linear_combine(hash.to_le_bytes(), randomness);

        let mut rows = Vec::with_capacity(rlp_data.len());

        let idx = handle_prefix(
            rlp_data.as_ref(),
            hash,
            &mut rows,
            RlpReceiptTag::Prefix as u8,
            0,
        );
        let _idx = handle_u256(
            rlp_data.as_ref(),
            hash,
            &mut rows,
            RlpReceiptTag::Status as u8,
            self.status.into(),
            idx,
        );

        rows
    }
}
