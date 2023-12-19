use std::ops::Deref;
use ethers::utils::keccak256;

#[allow(unused_imports)]
use ethers::types::{H160, H256, U256};

#[cfg(not(feature = "prover"))]
mod deps {
    use halo2_proofs::halo2curves::ff::{Field as Halo2Field, PrimeField, FromUniformBytes};

    pub fn from_bytes_value<F: Field>(bytes: &[u8]) -> F {
        let mut value = F::ZERO;
        let mut multiplier = F::ONE;
        for byte in bytes.iter() {
            value += F::from(*byte as u64) * multiplier;
            multiplier *= F::from(256);
        }
        value
    }

    pub struct WordLimbs<T, const N: usize> {
        pub limbs: [T; N],
    }
    pub(crate) type Word2<T> = WordLimbs<T, 2>;
    pub struct Word<T>(Word2<T>);

    impl<F: Field> From<U256> for Word<F> {
        fn from(value: U256) -> Self {
            let bytes = value.to_le_bytes();
            Word::new([
                from_bytes_value(&bytes[..16]),
                from_bytes_value(&bytes[16..]),
            ])
        }
    }

    impl<F: Field> From<H256> for Word<F> {
        fn from(h: H256) -> Self {
            let le_bytes = {
                let mut b = h.to_fixed_bytes();
                b.reverse();
                b
            };
            Word::new([
                from_bytes_value(&le_bytes[..16]),
                from_bytes_value(&le_bytes[16..]),
            ])
        }
    }

    impl<F: Field> From<u8> for Word<F> {
        /// Construct the word from u8
        fn from(value: u8) -> Self {
            Word::new([F::from(value as u64), F::from(0)])
        }
    }

    impl<F: Field> From<H160> for Word<F> {
        /// Construct the word from h160
        fn from(value: H160) -> Self {
            let mut bytes = *value.as_fixed_bytes();
            bytes.reverse();
            Word::new([
                from_bytes::value(&bytes[..16]),
                from_bytes::value(&bytes[16..]),
            ])
        }
    }

    pub trait Field: Halo2Field + PrimeField<Repr = [u8; 32]> + FromUniformBytes<64> + Ord {}

}

#[cfg(feature = "prover")]
mod deps {
    pub use zkevm_circuits::util::word::{Word, WordLimbs};
    pub use eth_types::Field;
}

pub use deps::{Word, WordLimbs, Field};


