//! Utility traits, functions used in the crate.

use eth_types::Word;

pub(crate) const BIT_COUNT: usize = 3;
pub(crate) const BIT_SIZE: usize = 2usize.pow(BIT_COUNT as u32);

/// Packs bits into bytes
pub mod to_bytes {
    use eth_types::Field;
    use gadgets::util::Expr;
    use halo2_proofs::plonk::Expression;

    pub(crate) fn expr<F: Field>(bits: &[Expression<F>]) -> Vec<Expression<F>> {
        debug_assert!(bits.len() % 8 == 0, "bits not a multiple of 8");

        let mut bytes = Vec::new();
        for byte_bits in bits.chunks(8) {
            let mut value = 0.expr();
            let mut multiplier = F::one();
            for byte in byte_bits.iter() {
                value = value + byte.expr() * multiplier;
                multiplier *= F::from(2);
            }
            bytes.push(value);
        }
        bytes
    }

    pub(crate) fn value(bits: &[u8]) -> Vec<u8> {
        debug_assert!(bits.len() % 8 == 0, "bits not a multiple of 8");

        let mut bytes = Vec::new();
        for byte_bits in bits.chunks(8) {
            let mut value = 0u8;
            for (idx, bit) in byte_bits.iter().enumerate() {
                value += *bit << idx;
            }
            bytes.push(value);
        }
        bytes
    }
}

/// Encodes the data using rlc
pub mod compose_rlc {
    use eth_types::Field;
    use halo2_proofs::plonk::Expression;

    pub(crate) fn expr<F: Field>(expressions: &[Expression<F>], r: F) -> Expression<F> {
        let mut rlc = expressions[0].clone();
        let mut multiplier = r;
        for expression in expressions[1..].iter() {
            rlc = rlc + expression.clone() * multiplier;
            multiplier *= r;
        }
        rlc
    }
}

/// Scatters a value into a packed word constant
pub mod scatter {
    use super::BIT_SIZE;
    use eth_types::Field;
    use halo2_proofs::plonk::Expression;

    pub(crate) fn expr<F: Field>(value: usize, count: usize) -> Expression<F> {
        let mut packed = F::zero();
        let mut factor = F::one();
        for _ in 0..count {
            packed += F::from(value as u64) * factor;
            factor *= F::from(BIT_SIZE as u64);
        }
        Expression::Constant(packed)
    }
}

/// The words that absorb data
pub fn get_absorb_positions() -> Vec<(usize, usize)> {
    let mut absorb_positions = Vec::new();
    for j in 0..5 {
        for i in 0..5 {
            if i + j * 5 < 17 {
                absorb_positions.push((i, j));
            }
        }
    }
    absorb_positions
}

/// Converts bytes into bits
pub fn into_bits(bytes: &[u8]) -> Vec<u8> {
    let num_bits = bytes.len() * 8;
    let mut bits: Vec<u8> = vec![0; num_bits];

    let mut counter = 0;
    for byte in bytes {
        for idx in 0u64..8 {
            bits[counter] = (*byte >> idx) & 1;
            counter += 1;
        }
    }

    bits
}

/// Converts bits into bytes
pub fn from_bits(bits: &[u8]) -> Word {
    let mut value = Word::zero();
    for (idx, bit) in bits.iter().enumerate() {
        value += Word::from(*bit as u64) << idx;
    }
    value
}

/// Pack bits into a word
pub fn pack(bits: &[u8]) -> Word {
    let mut packed = Word::zero();
    let mut factor = Word::from(1u64);
    for bit in bits {
        packed += Word::from(*bit as u64) * factor;
        factor *= BIT_SIZE;
    }
    packed
}

/// Unpack a word into bits
pub fn unpack(packed: Word) -> [u8; 64] {
    let mut bits = [0; 64];
    for (idx, bit) in bits.iter_mut().enumerate() {
        *bit = ((packed >> (idx * BIT_COUNT)) & Word::from(BIT_SIZE - 1)).as_u32() as u8;
    }
    assert_eq!(pack(&bits), packed);
    bits
}

/// Pack bits stored in a u64 value into a word
pub fn pack_u64(value: u64) -> Word {
    pack(
        &((0..64)
            .map(|i| ((value >> i) & 1) as u8)
            .collect::<Vec<_>>()),
    )
}

/// Normalize bits
pub fn normalize(bits: &[u8]) -> [u8; 64] {
    let mut normalized = [0; 64];
    for (normalized, bit) in normalized.iter_mut().zip(bits.iter()) {
        *normalized = *bit & 1;
    }
    normalized
}

/// Rotates bits left
pub fn rotate_left(bits: &[u8], count: usize) -> [u8; 64] {
    let mut rotated = bits.to_vec();
    rotated.rotate_left(count);
    rotated.try_into().unwrap()
}
