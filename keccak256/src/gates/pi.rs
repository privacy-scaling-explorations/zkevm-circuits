use halo2::{
    circuit::{Cell, Layouter},
    plonk::{Advice, Column, ConstraintSystem, Error},
};
use itertools::Itertools;
use pairing::arithmetic::FieldExt;
use std::convert::TryInto;
use std::marker::PhantomData;

#[derive(Clone, Debug)]
pub struct PiConfig<F> {
    state: [Column<Advice>; 25],
    _marker: PhantomData<F>,
}

impl<F: FieldExt> PiConfig<F> {
    pub fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let state: [Column<Advice>; 25] = (0..25)
            .map(|_| {
                let col = meta.advice_column();
                meta.enable_equality(col.into());
                col
            })
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();
        Self {
            state,
            _marker: PhantomData,
        }
    }

    pub fn assign_region(
        &self,
        layouter: &mut impl Layouter<F>,
        state: [(Cell, F); 25],
    ) -> Result<[(Cell, F); 25], Error> {
        let state = layouter.assign_region(
            || "Pi",
            |mut region| {
                let mut next_state: Vec<(Cell, F)> = vec![];
                let offset = 0;

                for (x, y) in (0..5).cartesian_product(0..5) {
                    let idx = 5 * ((x + 3 * y) % 5) + x;
                    let idx_next = 5 * x + y;
                    let (cell, value) = state[idx];
                    let cell_next = region.assign_advice(
                        || "lane next row",
                        self.state[idx_next],
                        offset,
                        || Ok(value),
                    )?;
                    region.constrain_equal(cell_next, cell)?;
                    next_state.push((cell_next, value));
                }
                Ok(next_state.try_into().unwrap())
            },
        )?;
        Ok(state)
    }
}
