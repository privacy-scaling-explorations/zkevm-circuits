use halo2_proofs::{arithmetic::FieldExt, plonk::Expression};

use crate::impl_expr;

use super::{
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
    fn gen_witness(&self, _randomness: F) -> Vec<RlpWitnessRow<F>> {
        unimplemented!()
    }
}
