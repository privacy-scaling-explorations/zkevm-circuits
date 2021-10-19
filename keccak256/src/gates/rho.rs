use crate::gates::gate_helpers::Lane;
use crate::gates::running_sum::{
    BlockCountFinalConfig, LaneRotateConversionConfig,
};

use halo2::{
    circuit::{Cell, Layouter, Region},
    plonk::{Advice, Column, ConstraintSystem, Error},
};
use itertools::Itertools;
use pasta_curves::arithmetic::FieldExt;
use std::convert::TryInto;

pub struct RhoConfig<F> {
    state: [Column<Advice>; 25],
    state_rotate_convert_configs: [LaneRotateConversionConfig<F>; 25],
    final_block_count_config: BlockCountFinalConfig<F>,
}

impl<F: FieldExt> RhoConfig<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        state: [Column<Advice>; 25],
    ) -> Self {
        let state_rotate_convert_configs = (0..5)
            .cartesian_product(0..5)
            .map(|(x, y)| LaneRotateConversionConfig::configure(meta, (x, y)))
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();
        let final_block_count_config = BlockCountFinalConfig::configure(meta);
        Self {
            state,
            state_rotate_convert_configs,
            final_block_count_config,
        }
    }
    pub fn assign_region(
        &self,
        layouter: &mut impl Layouter<F>,
        region: &mut Region<'_, F>,
        offset: usize,
        previous_state: [Lane<F>; 25],
    ) -> Result<[Lane<F>; 25], Error> {
        let mut next_state: Vec<Lane<F>> = vec![];
        let mut block_count_cells: Vec<(Cell, Cell)> = vec![];
        for (idx, lane) in previous_state.iter().enumerate() {
            let lane_config = self.state_rotate_convert_configs[idx];

            // copy constain enforced inside assign_region
            let (lane_next_row, cols) = lane_config.assign_region(
                &mut layouter.namespace(|| format!("lane {}", idx)),
                lane,
            )?;
            region.constrain_equal(lane.cell, lane_next_row.cell);
            let cell = region.assign_advice(
                || "lane next row",
                self.state[idx],
                offset + 1,
                || Ok(lane_next_row.value),
            )?;
            next_state.push(Lane {
                cell,
                value: lane_next_row.value,
            });
            block_count_cells.push(cols);
        }
        self.final_block_count_config.assign_region(
            &mut layouter.namespace(|| "Final block count check"),
            block_count_cells.try_into().unwrap(),
        );

        Ok(next_state.try_into().unwrap())
    }
}
