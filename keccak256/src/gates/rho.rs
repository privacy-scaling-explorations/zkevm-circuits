use crate::common::*;
use crate::gates::running_sum::RotateConversionConfig;

use halo2::plonk::{Advice, Column, ConstraintSystem, Selector};
use itertools::Itertools;
use pasta_curves::arithmetic::FieldExt;
use std::marker::PhantomData;

/// Determine how many chunks in a step.
/// Usually it's a step of 4 chunks, but the number of chunks could be less near the rotation position and the end of the lane.
/// Those are the special chunks we need to take care of.
fn get_step_size(chunk_idx: u32, rotation: u32) -> u32 {
    const BASE_NUM_OF_CHUNKS: u32 = 4;
    const LANE_SIZE: u32 = 64;
    // near the rotation position of the lane
    if chunk_idx < rotation && rotation < chunk_idx + BASE_NUM_OF_CHUNKS {
        return rotation - chunk_idx;
    }
    // near the end of the lane
    if chunk_idx < LANE_SIZE && LANE_SIZE < chunk_idx + BASE_NUM_OF_CHUNKS {
        return LANE_SIZE - chunk_idx;
    }
    BASE_NUM_OF_CHUNKS
}

pub struct RhoConfig<F> {
    q_enable: Selector,
    state: [Column<Advice>; 25],
    _marker: PhantomData<F>,
}

impl<F: FieldExt> RhoConfig<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        state: [Column<Advice>; 25],
    ) {
        for (x, y) in (0..5).cartesian_product(0..5) {
            let base_13_cols = [
                meta.advice_column(),
                meta.advice_column(),
                meta.advice_column(),
            ];
            let base_9_cols = [
                meta.advice_column(),
                meta.advice_column(),
                meta.advice_column(),
            ];
            let block_count_cols = [
                meta.advice_column(),
                meta.advice_column(),
                meta.advice_column(),
            ];

            let q_is_final = meta.selector();
            let q_running_sum = meta.selector();

            let mut chunk_idx = 1;
            while chunk_idx < 64 {
                let step = get_step_size(chunk_idx, ROTATION_CONSTANTS[x][y]);
                let config = RotateConversionConfig::configure(
                    q_running_sum,
                    q_is_final,
                    meta,
                    base_13_cols,
                    base_9_cols,
                    block_count_cols,
                    step,
                );
                chunk_idx += step;
            }
        }

        // TODO: block_count check
    }
}
