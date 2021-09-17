fn convert_13_base_limb(x: u64) -> u64 {
    assert!(x < 13);
    x & 1
}

fn convert_9_base_limb(x: u64) -> u64 {
    assert!(x < 9);
    bit_table = [0, 0, 1, 1, 0, 0, 1, 1, 0];
    return bit_table[n];
}

fn rotate_and_convert(base13_input: u64, rot: u64) -> u64 {
    base = 9 * *rot;
    special_chunk = 0;
    raw = base13_input;
    acc = 0;

    for i in 0..65 {
        remainder = raw % 13;
        if i == 0 || i == 64 {
            special_chunk += remainder;
        } else {
            acc += convert_13_base_limb(remainder) * base;
        }
        raw /= 13;
        base *= 9;
        if i == 64 - rot {
            base = 1;
        }

        acc += convert_13_base_limb(special_chunk) * 9 * *rot;
    }

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
