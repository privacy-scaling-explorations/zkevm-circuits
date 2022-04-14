use halo2_proofs::{arithmetic::FieldExt, plonk::Expression};
use rlp::Encodable;

use crate::impl_expr;

use super::Transaction;

#[derive(Clone, Copy, Debug)]
/// Data types that are supported by the RLP circuit.
pub enum RlpDataType {
    /// Data type for an RLP-encoded legacy transaction.
    Transaction,
    /// Data type for an RLP-encoded transaction receipt.
    Receipt,
}

#[derive(Clone, Copy, Debug)]
/// Tags used to tag rows in the RLP circuit for a transaction.
pub enum RlpTxTag {
    /// Denotes the prefix bytes indicating the “length of length” and/or
    /// “length” of the tx’s RLP-encoding.
    Prefix,
    /// Denotes the byte(s) for the tx’s nonce.
    Nonce,
    /// Denotes the byte(s) for the tx’s gas price.
    GasPrice,
    /// Denotes the byte(s) for the tx’s gas.
    Gas,
    /// Denotes the prefix byte indicating the “length” of the tx’s to.
    ToPrefix,
    /// Denotes the bytes for the tx’s to.
    To,
    /// Denotes the byte(s) for the tx’s value.
    Value,
    /// Denotes the prefix byte(s) indicating the “length of length” and/or
    /// “length” of the tx’s data.
    DataPrefix,
    /// Denotes the bytes for the tx’s data.
    Data,
}

/// Denotes the number of possible tag values for a tx row.
pub const N_TX_TAGS: usize = 9;

#[derive(Clone, Copy, Debug)]
/// Tags used to tags rows in the RLP circuit for a tx receipt.
pub enum RlpReceiptTag {
    /// Denotes the prefix bytes indicating the "length of length" and/or
    /// "length" of the tx receipt's RLP-encoding.
    Prefix,
    /// Denotes the byte for the receipt's status.
    Status,
    // TODO: other receipt tags
}

/// Denotes the number of possible tag values for a tx receipt row.
pub const N_RECEIPT_TAGS: usize = 2;

impl_expr!(RlpDataType);
impl_expr!(RlpTxTag);
impl_expr!(RlpReceiptTag);

pub const N_COLUMNS_RLP: usize = 4;

pub struct RlpWitnessRow {
    pub index: usize,
    pub data_type: RlpDataType,
}

pub trait RlpWitnessGen<F>: Encodable {
    fn gen_witness(&self) -> Vec<[F; N_COLUMNS_RLP]>;
}

impl<F: FieldExt> RlpWitnessGen<F> for Transaction {
    fn gen_witness(&self) -> Vec<[F; N_COLUMNS_RLP]> {
        unimplemented!()
    }
}
