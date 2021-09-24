use num_bigint::BigUint;
use num_traits::{One, Zero};

pub fn convert_13_base_limb(x: u64) -> u64 {
    assert!(x < 13);
    x & 1
}

fn convert_9_base_limb(x: u64) -> u64 {
    assert!(x < 9);
    let bit_table: [u64; 9] = [0, 0, 1, 1, 0, 0, 1, 1, 0];
    bit_table[x as usize]
}

fn mod_u64(a: &BigUint, b: u64) -> u64 {
    (a % b).iter_u64_digits().take(1).next().unwrap_or(0)
}

fn rotate_and_convert(base13_input: &BigUint, rot: u32) -> BigUint {
    let nine = BigUint::from(9u64);
    let thirteen = BigUint::from(13u64);
    let mut base = nine.pow(rot);
    let mut special_chunk = Zero::zero();
    let mut raw = base13_input.clone();
    let mut acc: BigUint = Zero::zero();

    for i in 0..65 {
        let remainder: u64 = mod_u64(&raw, 13);
        if i == 0 || i == 64 {
            special_chunk += remainder;
        } else {
            acc += convert_13_base_limb(remainder) * base.clone();
        }
        raw /= thirteen.clone();
        base *= nine.clone();
        if i == 64 - rot {
            base = One::one();
        }
    }
    acc += convert_13_base_limb(special_chunk) * nine.pow(rot);
    acc
}

pub fn get_step_size(chunk_idx: usize, rot: usize) -> usize {
    let max_offset = 64 - rot;
    if (chunk_idx < max_offset) && (chunk_idx + 4 > max_offset) {
        return max_offset - chunk_idx;
    }
    if (chunk_idx < 64) && (chunk_idx > 60) {
        return 64 - chunk_idx;
    }
    return 4;
}
