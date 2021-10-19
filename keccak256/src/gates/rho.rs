use crate::arith_helpers::convert_b13_lane_to_b9;
use crate::common::ROTATION_CONSTANTS;
use crate::gates::running_sum::{
    BlockCountFinalConfig, LaneRotateConversionConfig,
};
use num_bigint::BigUint;

use halo2::{
    circuit::{Cell, Region},
    plonk::{Advice, Column, ConstraintSystem, Error, Selector},
};
use itertools::Itertools;
use pasta_curves::arithmetic::FieldExt;
use std::convert::TryInto;

pub struct RhoConfig<F> {
    q_enable: Selector,
    state: [Column<Advice>; 25],
    state_rotate_convert_configs: [LaneRotateConversionConfig<F>; 25],
    final_block_count_config: BlockCountFinalConfig<F>,
}

impl<F: FieldExt> RhoConfig<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: Selector,
        state: [Column<Advice>; 25],
    ) -> Self {
        let block_count_cols = [
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
        ];
        let state_rotate_convert_configs = (0..5)
            .cartesian_product(0..5)
            .map(|(x, y)| {
                LaneRotateConversionConfig::configure(
                    q_enable,
                    meta,
                    // NB: reused across all LaneRotateConversionConfigs
                    block_count_cols,
                    (x, y),
                )
            })
            .collect::<Vec<_>>().try_into().unwrap();
        let q_block_count_final = meta.selector();
        let final_block_count_config = BlockCountFinalConfig::configure(
            meta,
            q_block_count_final,
            block_count_cols,
        );
        Self {
            q_enable,
            state,
            state_rotate_convert_configs,
            final_block_count_config,
        }
    }
    pub fn assign_region(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        state: [F; 25],
        next_state: [&Cell; 25],
    ) -> Result<[F; 25], Error> {
        self.q_enable.enable(region, offset)?;

        for (x, y) in (0..5).cartesian_product(0..5) {
            let idx = 5 * x + y;
            let lane_base_13 = state[idx];
            let cell = region.assign_advice(
                || format!("assign lane {:?}", (x, y)),
                self.state[idx],
                offset,
                || Ok(lane_base_13),
            )?;
            let lane_config = &self.state_rotate_convert_configs[idx];
            let lane_base_13_big_uint =
                BigUint::from_bytes_le(&lane_base_13.to_bytes());
            let lane_base_9_big_uint = convert_b13_lane_to_b9(
                lane_base_13_big_uint,
                ROTATION_CONSTANTS[x][y],
            );
            let lane_base_9 = Option::from(F::from_bytes(
                lane_base_9_big_uint.to_bytes_le()[..=32]
                    .try_into()
                    .unwrap(),
            ))
            .ok_or(Error::SynthesisError)?;
            let next_offset = lane_config.assign_region(
                region,
                offset,
                &cell,
                lane_base_13,
                next_state[idx],
                lane_base_9,
            );
        }
        Ok(state)
    }
}
