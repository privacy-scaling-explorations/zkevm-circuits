//! Utility traits, functions used in the crate.

use eth_types::Word;

pub(crate) const NUM_BITS_PER_BYTE: usize = 8;
pub(crate) const NUM_BYTES_PER_WORD: usize = 8;
pub(crate) const NUM_BITS_PER_WORD: usize = NUM_BYTES_PER_WORD * NUM_BITS_PER_BYTE;
pub(crate) const KECCAK_WIDTH: usize = 5 * 5;
pub(crate) const KECCAK_WIDTH_IN_BITS: usize = KECCAK_WIDTH * NUM_BITS_PER_WORD;
pub(crate) const NUM_ROUNDS: usize = 24;
pub(crate) const NUM_WORDS_TO_ABSORB: usize = 17;
pub(crate) const NUM_WORDS_TO_SQUEEZE: usize = 4;
pub(crate) const ABSORB_WIDTH_PER_ROW: usize = NUM_BITS_PER_WORD;
pub(crate) const ABSORB_WIDTH_PER_ROW_BYTES: usize = ABSORB_WIDTH_PER_ROW / NUM_BITS_PER_BYTE;
pub(crate) const RATE: usize = NUM_WORDS_TO_ABSORB * NUM_BYTES_PER_WORD;
pub(crate) const RATE_IN_BITS: usize = RATE * NUM_BITS_PER_BYTE;
pub(crate) const THETA_C_WIDTH: usize = 5 * NUM_BITS_PER_WORD;
pub(crate) const RHOM: [[usize; 5]; 5] = [
    [0, 36, 3, 41, 18],
    [1, 44, 10, 45, 2],
    [62, 6, 43, 15, 61],
    [28, 55, 25, 21, 56],
    [27, 20, 39, 8, 14],
];
pub(crate) const ROUND_CST: [u64; NUM_ROUNDS + 1] = [
    0x0000000000000001,
    0x0000000000008082,
    0x800000000000808a,
    0x8000000080008000,
    0x000000000000808b,
    0x0000000080000001,
    0x8000000080008081,
    0x8000000000008009,
    0x000000000000008a,
    0x0000000000000088,
    0x0000000080008009,
    0x000000008000000a,
    0x000000008000808b,
    0x800000000000008b,
    0x8000000000008089,
    0x8000000000008003,
    0x8000000000008002,
    0x8000000000000080,
    0x000000000000800a,
    0x800000008000000a,
    0x8000000080008081,
    0x8000000000008080,
    0x0000000080000001,
    0x8000000080008008,
    0x0000000000000000, // absorb round
];
// Bit positions that have a non-zero value in `IOTA_ROUND_CST`.
pub(crate) const ROUND_CST_BIT_POS: [usize; 7] = [0, 1, 3, 7, 15, 31, 63];

pub(crate) const BIT_COUNT: usize = 3;
pub(crate) const BIT_SIZE: usize = 2usize.pow(BIT_COUNT as u32);

// `a ^ ((~b) & c)` is calculated by doing `lookup[3 - 2*a + b - c]`
pub(crate) const CHI_BASE_LOOKUP_TABLE: [u8; 5] = [0, 1, 1, 0, 0];
// `a ^ ((~b) & c) ^ d` is calculated by doing `lookup[5 - 2*a - b + c - 2*d]`
pub(crate) const CHI_EXT_LOOKUP_TABLE: [u8; 7] = [0, 0, 1, 1, 0, 0, 1];

/// PartInfo
#[derive(Clone, Debug)]
pub struct PartInfo {
    /// The bits of the part
    pub bits: Vec<usize>,
}

/// WordParts
#[derive(Clone, Debug)]
pub struct WordParts {
    /// The parts of the word
    pub parts: Vec<PartInfo>,
}

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

/// Rotates a word that was split into parts to the right
pub fn rotate<T>(parts: Vec<T>, count: usize, part_size: usize) -> Vec<T> {
    let mut rotated_parts = parts;
    rotated_parts.rotate_right(get_rotate_count(count, part_size));
    rotated_parts
}

/// Rotates a word that was split into parts to the left
pub fn rotate_rev<T>(parts: Vec<T>, count: usize, part_size: usize) -> Vec<T> {
    let mut rotated_parts = parts;
    rotated_parts.rotate_left(get_rotate_count(count, part_size));
    rotated_parts
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

/// Gets the target part sizes
pub fn target_part_sizes(part_size: usize) -> Vec<usize> {
    let num_full_chunks = 64 / part_size;
    let partial_chunk_size = 64 % part_size;
    let mut part_sizes = vec![part_size; num_full_chunks];
    if partial_chunk_size > 0 {
        part_sizes.push(partial_chunk_size);
    }
    part_sizes
}

/// Gets the rotation count in parts
pub fn get_rotate_count(count: usize, part_size: usize) -> usize {
    (count + part_size - 1) / part_size
}

/// Gets the word parts
pub fn get_word_parts(part_size: usize, rot: usize, normalize: bool) -> WordParts {
    let mut bits = (0usize..64).collect::<Vec<_>>();
    bits.rotate_right(rot);

    let mut parts = Vec::new();
    let mut rot_idx = 0;

    let mut idx = 0;
    let target_sizes = if normalize {
        // After the rotation we want the parts of all the words to be at the same
        // positions
        target_part_sizes(part_size)
    } else {
        // Here we only care about minimizing the number of parts
        let num_parts_a = rot / part_size;
        let partial_part_a = rot % part_size;

        let num_parts_b = (64 - rot) / part_size;
        let partial_part_b = (64 - rot) % part_size;

        let mut part_sizes = vec![part_size; num_parts_a];
        if partial_part_a > 0 {
            part_sizes.push(partial_part_a);
        }

        part_sizes.extend(vec![part_size; num_parts_b]);
        if partial_part_b > 0 {
            part_sizes.push(partial_part_b);
        }

        part_sizes
    };
    // Split into parts bit by bit
    for part_size in target_sizes {
        let mut num_consumed = 0;
        while num_consumed < part_size {
            let mut part_bits: Vec<usize> = Vec::new();
            while num_consumed < part_size {
                if !part_bits.is_empty() && bits[idx] == 0 {
                    break;
                }
                if bits[idx] == 0 {
                    rot_idx = parts.len();
                }
                part_bits.push(bits[idx]);
                idx += 1;
                num_consumed += 1;
            }
            parts.push(PartInfo { bits: part_bits });
        }
    }

    assert_eq!(get_rotate_count(rot, part_size), rot_idx);

    parts.rotate_left(rot_idx);
    assert_eq!(parts[0].bits[0], 0);

    WordParts { parts }
}
