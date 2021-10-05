use crate::{
    arith_helpers::{convert_b13_coef, B13, B9},
    common::LANE_SIZE,
    gates::gate_helpers::biguint_mod,
};

use num_bigint::BigUint;

pub const BASE_NUM_OF_CHUNKS: u32 = 4;

/// Determine how many chunks in a step.
/// Usually it's a step of 4 chunks, but the number of chunks could be less near
/// the rotation position and the end of the lane.
pub fn get_step_size(chunk_idx: u32, rotation: u32) -> u32 {
    // near the rotation offset position of the lane
    let offset = LANE_SIZE - rotation;
    if chunk_idx < offset && offset < chunk_idx + BASE_NUM_OF_CHUNKS {
        return offset - chunk_idx;
    }
    // near the end of the lane
    if chunk_idx < LANE_SIZE && LANE_SIZE < chunk_idx + BASE_NUM_OF_CHUNKS {
        return LANE_SIZE - chunk_idx;
    }
    BASE_NUM_OF_CHUNKS
}
/// This is the point where power of 9 starts from 1
pub fn is_at_rotation_offset(chunk_idx: u32, rotation: u32) -> bool {
    chunk_idx == LANE_SIZE - rotation
}

pub fn slice_lane(rotation: u32) -> Vec<(u32, u32)> {
    // we start chunk_idx from 1
    // because the 0th chunk is for the low value from the theta step
    let mut chunk_idx = 1;
    let mut output = vec![];
    while chunk_idx < LANE_SIZE {
        let step = get_step_size(chunk_idx, rotation);
        output.push((chunk_idx, step));
        chunk_idx += step;
    }
    output
}

pub fn block_counting_function(n: usize) -> u32 {
    [0, 0, 1, 13, 170][n]
}

pub fn get_block_count_and_output_coef(input_coef: BigUint) -> (u32, u64) {
    let mut x = input_coef;
    let mut output_coef = 0;
    let mut non_zero_chunk_count = 0;
    for i in 0..4 {
        let base13_chunk = biguint_mod(&x, B13);
        let base9_chunk = convert_b13_coef(base13_chunk);
        if base9_chunk != 0 {
            non_zero_chunk_count += 1;
        }
        output_coef += base9_chunk * B9.pow(i as u32);
        x /= B13;
    }
    let block_count = block_counting_function(non_zero_chunk_count);

    (block_count, output_coef)
}
