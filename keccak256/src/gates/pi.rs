use crate::gates::gate_helpers::Lane;

use halo2::{
    circuit::Region,
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Selector},
    poly::Rotation,
};
use itertools::Itertools;
use pairing::arithmetic::FieldExt;
use std::convert::TryInto;
use std::marker::PhantomData;

pub struct PiConfig<F> {
    q_enable: Selector,
    state: [Column<Advice>; 25],
    _marker: PhantomData<F>,
}

impl<F: FieldExt> PiConfig<F> {
    pub fn configure(
        q_enable: Selector,
        meta: &mut ConstraintSystem<F>,
        state: [Column<Advice>; 25],
    ) -> PiConfig<F> {
        meta.create_gate("pi", |meta| {
            let q_enable = meta.query_selector(q_enable);
            (0..5)
                .cartesian_product(0..5)
                .map(|(x, y)| {
                    let lane = meta.query_advice(
                        state[5 * ((x + 3 * y) % 5) + x],
                        Rotation::cur(),
                    );
                    let new_lane =
                        meta.query_advice(state[5 * x + y], Rotation::next());

                    q_enable.clone() * (new_lane - lane)
                })
                .collect::<Vec<Expression<F>>>()
        });

        PiConfig {
            q_enable,
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
        self.q_enable.enable(region, offset)?;
        let mut next_state: Vec<Lane<F>> = vec![];

        for (x, y) in (0..5).cartesian_product(0..5) {
            let idx_prev = 5 * ((x + 3 * y) % 5) + x;
            let idx_next = 5 * x + y;
            let lane = &previous_state[idx_prev];
            let cell = region.assign_advice(
                || "lane next row",
                self.state[idx_next],
                offset,
                || Ok(lane.value),
            )?;
            next_state.push(Lane {
                cell,
                value: lane.value,
            });
        }
        Ok(next_state.try_into().unwrap())
    }
}
