use crate::{
    arith_helpers::{convert_b13_coef, B13, B9},
    common::LANE_SIZE,
    gates::gate_helpers::biguint_mod,
};

use std::convert::TryInto;

use num_bigint::BigUint;

pub const BASE_NUM_OF_CHUNKS: u32 = 4;

/// Determine how many chunks in a step
///
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

/// Slice the lane into chunk indices and steps
///
/// We ask what's the current chunk index and the step we need to go to the next
/// chunk index. We start chunk_idx from 1 because the 0th chunk is from the low
/// value from the theta step.
pub fn slice_lane(rotation: u32) -> Vec<(u32, u32)> {
    let mut chunk_idx = 1;
    let mut output = vec![];
    while chunk_idx < LANE_SIZE {
        let step = get_step_size(chunk_idx, rotation);
        output.push((chunk_idx, step));
        chunk_idx += step;
    }
    output
}

/// We have 12 step 1, 12 step 2, and 13 step 3
///
/// See tests for more detail
pub const STEP_COUNTS: [u32; 3] = [12, 12, 13];

/// A mapping from `step` to a block count value
///
/// See tests for the derivation of the values
pub const OVERFLOW_TRANSFORM: [u32; 5] = [0, 0, 1, 13, 170];

/// The sum of the step 2 block counts across all 25 lanes should not greater
/// than this value
///
/// See tests for the derivation of the values
pub const STEP2_RANGE: u64 = 12;

/// The sum of the step 3 block counts across all 25 lanes should not greater
/// than this value
///
/// See tests for the derivation of the values
pub const STEP3_RANGE: u64 = 169;

/// Get the block count from an input chunks
///
/// The input is chunks of a base 13 number in descending order of signiticance.
/// For example, if the input is `[1, 12, 3, 7]`, it represents a coefficient
/// `1*13^3 + 12*13^2 + 3*13 + 7`. The example only happens when `step = 4`. If
/// we have a `step = 3`, the first chunk must be 0. It could be the case that
/// we have `step = 4`, but all of the chunks are 0. That would result our block
/// count value to be 0.
///
/// In the circuit, if we have a `step = 3`, but a non-zero first chunk is
/// adviced. It would cause the non_zero_chunk_count to be 4, resulting the
/// block count to be 170.
///
/// This would fail the final block count check.
pub fn get_block_count(b13_chunks: [u64; BASE_NUM_OF_CHUNKS as usize]) -> u32 {
    // could be 0, 1, 2, 3, 4
    let non_zero_chunk_count = BASE_NUM_OF_CHUNKS as usize
        - b13_chunks.iter().take_while(|x| **x == 0).count();
    // could be 0, 0, 1, 13, 170
    OVERFLOW_TRANSFORM[non_zero_chunk_count]
}

pub fn get_block_count_and_output_coef(input_coef: BigUint) -> (u32, u64) {
    // b13_chunks is in descending order of more significant chunk
    let b13_chunks: [u64; BASE_NUM_OF_CHUNKS as usize] = {
        let mut x = input_coef;
        let mut b13_chunks: Vec<u64> = vec![];
        for _ in 0..BASE_NUM_OF_CHUNKS {
            b13_chunks.push(biguint_mod(&x, B13));
            x /= B13;
        }
        b13_chunks.reverse();
        b13_chunks.try_into().unwrap()
    };
    let output_coef: u64 = b13_chunks.iter().fold(0, |acc, b13_chunk| {
        let b9_chunk = convert_b13_coef(*b13_chunk);
        acc * B9 + b9_chunk
    });
    let block_count = get_block_count(b13_chunks);
    (block_count, output_coef)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::ROTATION_CONSTANTS;
    #[test]
    fn test_overflow_counting() {
        // counting how many step 1, step 2, and step 3 in the lane slices.
        let mut counts = vec![0; BASE_NUM_OF_CHUNKS as usize - 1];
        for rotation in ROTATION_CONSTANTS.iter().flat_map(|r| r.iter()) {
            let chunks = slice_lane(*rotation);
            for (_, step) in chunks.iter() {
                if *step < BASE_NUM_OF_CHUNKS {
                    counts[*step as usize - 1] += 1;
                }
            }
        }
        // We know exactly at setup time there would be 12 step 1, 12 step 2 and
        // 13 step 3.
        assert_eq!(counts, STEP_COUNTS);

        // We define a mapping overflow g(x), it maps step to a block count
        // value We first define g(0) = 0, g(1) = 0
        // Mapping from step 0 is meaningless, because we don't have step 0
        // Mapping step 1 to 0 as the base case.
        // Then we define `g(i+1) = g(i) * previous_step_count + 1`
        // Because `g(i) * previous_step_count` is the max possible block count
        // sum from previous step An overflow in previous step would get
        // the `g(i+1)` value from the lookup table and fail the final block
        // count sum check
        let mut overflow = vec![0, 0];
        for c in counts.iter() {
            let elem = overflow.last().cloned().unwrap();
            overflow.push(c * elem + 1);
        }
        assert_eq!(overflow, OVERFLOW_TRANSFORM);

        let step2 = 2;
        assert_eq!(
            STEP2_RANGE,
            (STEP_COUNTS[step2 - 1] * OVERFLOW_TRANSFORM[step2]).into()
        );

        let step3 = 3;
        assert_eq!(
            STEP3_RANGE,
            (STEP_COUNTS[step3 - 1] * OVERFLOW_TRANSFORM[step3]).into()
        );
    }
}
