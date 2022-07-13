//! Common utility traits and functions.
use eth_types::Field;

pub use gadgets::util::Expr;

pub(crate) fn random_linear_combine_word<F: Field>(bytes: [u8; 32], randomness: F) -> F {
    crate::evm_circuit::util::Word::random_linear_combine(bytes, randomness)
}
