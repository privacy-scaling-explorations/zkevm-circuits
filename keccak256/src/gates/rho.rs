use crate::arith_helpers::convert_b13_lane_to_b9;
use crate::common::ROTATION_CONSTANTS;
use crate::gates::gate_helpers::Lane;

use halo2::{
    circuit::Region,
    plonk::{Advice, Column, Error},
};
use itertools::Itertools;
use num_bigint::BigUint;
use pasta_curves::arithmetic::FieldExt;
use std::convert::TryInto;
use std::marker::PhantomData;

pub struct RhoConfig<F> {
    state: [Column<Advice>; 25],
    _marker: PhantomData<F>,
}

impl<F: FieldExt> RhoConfig<F> {
    pub fn configure(state: [Column<Advice>; 25]) -> Self {
        Self {
            state,
            _marker: PhantomData,
        }
    }
    pub fn assign_region(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        previous_state: [Lane<F>; 25],
    ) -> Result<[Lane<F>; 25], Error> {
        let mut next_state: Vec<Lane<F>> = vec![];

        for (x, y) in (0..5).cartesian_product(0..5) {
            let idx = 5 * x + y;
            let lane_base_13 = &previous_state[idx];
            let lane_base_13_big_uint =
                BigUint::from_bytes_le(&lane_base_13.value.to_bytes());
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
            let cell = region.assign_advice(
                || "lane next row",
                self.state[idx],
                offset,
                || Ok(lane_base_9),
            )?;
            next_state.push(Lane {
                cell,
                value: lane_base_9,
            });
        }
        Ok(next_state.try_into().unwrap())
    }
}
