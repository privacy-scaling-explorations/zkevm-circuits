use crate::common::*;
use crate::gates::running_sum::{
    BlockCountFinalConfig, LaneRotateConversionConfig,
};

use halo2::{
    circuit::Region,
    plonk::{Advice, Column, ConstraintSystem, Error, Selector},
};
use itertools::Itertools;
use pasta_curves::arithmetic::FieldExt;

pub struct RhoConfig<F> {
    q_enable: Selector,
    state: [Column<Advice>; 25],
    state_rotate_convert_configs: Vec<LaneRotateConversionConfig<F>>,
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
                    block_count_cols,
                    ROTATION_CONSTANTS[x][y],
                )
            })
            .collect();
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
    ) -> Result<[F; 25], Error> {
        self.q_enable.enable(region, offset)?;

        for (idx, lane) in state.iter().enumerate() {
            region.assign_advice(
                || format!("assign state {}", idx),
                self.state[idx],
                offset,
                || Ok(*lane),
            )?;
        }
        Ok(state)
    }
}
