use eth_types::{ToLittleEndian, Word};
use halo2_proofs::{arithmetic::FieldExt, circuit::Value, plonk::Expression};
use rlp::Encodable;
use sha3::{digest::Digest, Keccak256};

use crate::{evm_circuit::util::RandomLinearCombination, impl_expr, util::Challenges};

/// Data types that are supported by the RLP circuit.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RlpDataType {
    /// Data type for an RLP-encoded unsigned transaction. The encoding consists
    /// of: [nonce, gas, gasprice, to, value, input, chainid, 0, 0].
    TxSign,
    /// Data type for an RLP-encoded signed transaction. The encoding consists
    /// of: [nonce, gas, gasprice, to, value, input, v, r, s].
    /// where the fields `v`, `r` and `s` represent the compressed form of an
    /// ECDSA signature.
    TxHash,
}

impl_expr!(RlpDataType);

/// Represents the witness in a single row of the RLP circuit.
#[derive(Clone, Debug)]
pub struct RlpWitnessRow<F> {
    /// Denotes the transaction or receipt ID.
    pub id: usize,
    /// Denotes the index of this row, starting from 0 and ending at n-1 where n
    /// is the byte length of the RLP-encoded data.
    pub index: usize,
    /// Denotes the data type, whether this circuit encodes a RlpDataType::Tx or
    /// a RlpDataType::Receipt.
    pub data_type: RlpDataType,
    /// Denotes the byte value in the RLP-encoded data.
    pub value: u8,
    /// Accumulator value to represent the full value of the tag.
    pub value_acc: F,
    /// Denotes the row’s tag, which can be a field from the data type encoded.
    pub tag: u8,
    /// Denotes the current tag's length in bytes.
    pub tag_length: usize,
    /// Denotes a decrementing index specific to the tag in in the current block
    /// of bytes.
    pub tag_index: usize,
    /// Denotes the aux tag's index.
    pub aux_tag_index: [usize; 2],
    /// Denotes the aux tag's length.
    pub aux_tag_length: [usize; 2],
    /// Denotes an accumulator for the length of data, in the case where len >
    /// 55 and the length is represented in its big-endian form.
    pub length_acc: u64,
    /// Denotes the hash of the RLP-encoded data.
    pub hash: Value<F>,
}

/// The RlpWitnessGen trait is implemented by data types who's RLP encoding can
/// be verified by the RLP-encoding circuit.
pub trait RlpWitnessGen<F: FieldExt>: Encodable + Default + std::marker::Sized {
    /// Generate witness to the RLP-encoding verifier circuit, as a vector of
    /// RlpWitnessRow.
    fn gen_witness(
        &self,
        randomness: F,
        challenges: &Challenges<Value<F>>,
    ) -> Vec<RlpWitnessRow<F>>;

    /// Returns a random linear combination (RLC) of the Keccak-256 hash of the
    /// RLP-encoded data.
    fn hash(&self, challenges: &Challenges<Value<F>>) -> Value<F> {
        let rlp_data = rlp::encode(self);
        let keccak_hash = Word::from_big_endian(Keccak256::digest(&rlp_data).as_slice());
        challenges.evm_word().map(|challenge| {
            RandomLinearCombination::random_linear_combine(keccak_hash.to_le_bytes(), challenge)
        })
    }
}
