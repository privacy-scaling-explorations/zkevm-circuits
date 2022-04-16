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
    Prefix,
    /// Denotes the byte for the receipt's status.
    Status,
    // TODO: other receipt tags
}

impl_expr!(RlpReceiptTag);

/// Denotes the number of possible tag values for a tx receipt row.
pub const N_RECEIPT_TAGS: usize = 2;

impl<F: FieldExt> RlpWitnessGen<F> for Receipt {
    fn gen_witness(&self, _randomness: F) -> Vec<RlpWitnessRow<F>> {
        unimplemented!()
    }
}
