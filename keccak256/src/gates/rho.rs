use crate::gates::{
    gate_helpers::BlockCount2,
    rho_checks::{
        BlockCountFinalConfig, LaneRotateConversionConfig, RhoAdvices,
    },
};

use halo2::{
    circuit::{Cell, Layouter, Region},
    plonk::{Advice, Column, ConstraintSystem, Error, TableColumn},
};
use itertools::Itertools;
use pairing::arithmetic::FieldExt;
use std::convert::TryInto;

#[derive(Debug, Clone)]
pub struct RhoConfig<F> {
    state: [Column<Advice>; 25],
    state_rotate_convert_configs: [LaneRotateConversionConfig<F>; 25],
    final_block_count_config: BlockCountFinalConfig<F>,
}

impl<F: FieldExt> RhoConfig<F> {
    pub const OFFSET: usize = 2;
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        state: [Column<Advice>; 25],
        adv: &RhoAdvices,
        axiliary: [Column<Advice>; 2],
        base13_to_9: [TableColumn; 3],
        special: [TableColumn; 2],
    ) -> Self {
        for lane in state.iter() {
            meta.enable_equality((*lane).into());
        }
        let state_rotate_convert_configs = (0..5)
            .cartesian_product(0..5)
            .map(|(x, y)| {
                LaneRotateConversionConfig::configure(
                    meta,
                    (x, y),
                    adv.clone(),
                    axiliary,
                    base13_to_9,
                    special,
                )
            })
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();
        let final_block_count_config =
            BlockCountFinalConfig::configure(meta, axiliary);
        Self {
            state,
            state_rotate_convert_configs,
            final_block_count_config,
        }
    }
    pub fn assign_rotation_checks(
        &self,
        layouter: &mut impl Layouter<F>,
        state: [(Cell, F); 25],
    ) -> Result<[(Cell, F); 25], Error> {
        type R<F> = ((Cell, F), BlockCount2<F>);
        let lane_and_bcs: Result<Vec<R<F>>, Error> = state
            .iter()
            .enumerate()
            .map(|(idx, &lane)| -> Result<R<F>, Error> {
                let (lane_next_row, bc) =
                    self.state_rotate_convert_configs[idx].assign_region(
                        &mut layouter.namespace(|| format!("arc lane {}", idx)),
                        lane,
                    )?;
                Ok((lane_next_row, bc))
            })
            .into_iter()
            .collect();
        let lane_and_bcs = lane_and_bcs?;
        let lane_and_bcs: [R<F>; 25] = lane_and_bcs.try_into().unwrap();

        let block_counts = lane_and_bcs.map(|(_, bc)| bc);
        let next_state = lane_and_bcs.map(|(lane_next_row, _)| lane_next_row);

        self.final_block_count_config.assign_region(
            &mut layouter.namespace(|| "Final block count check"),
            block_counts,
        )?;
        Ok(next_state)
    }

    pub fn assign_region(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        next_state: [(Cell, F); 25],
    ) -> Result<(), Error> {
        for (idx, next_lane) in next_state.iter().enumerate() {
            let cell = region.assign_advice(
                || "lane next row",
                self.state[idx],
                offset + 1,
                || Ok(next_lane.1),
            )?;
            region.constrain_equal(cell, next_lane.0)?;
        }
        Ok(())
    }

    pub fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        self.state_rotate_convert_configs[0].load(layouter)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arith_helpers::*;
    use crate::common::*;
    use crate::gates::gate_helpers::*;
    use crate::keccak_arith::*;
    use halo2::circuit::Layouter;
    use halo2::plonk::{Advice, Column, ConstraintSystem, Error};
    use halo2::{circuit::SimpleFloorPlanner, dev::MockProver, plonk::Circuit};
    use itertools::Itertools;
    use pairing::arithmetic::FieldExt;
    use pairing::bn256::Fr as Fp;
    use std::convert::TryInto;
    #[test]
    fn test_rho_gate() {
        #[derive(Default)]
        struct MyCircuit<F> {
            in_state: [F; 25],
            out_state: [F; 25],
        }
        impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
            type Config = RhoConfig<F>;
            type FloorPlanner = SimpleFloorPlanner;

            fn without_witnesses(&self) -> Self {
                Self::default()
            }

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                let state: [Column<Advice>; 25] = (0..25)
                    .map(|_| meta.advice_column())
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap();
                let cols: [Column<Advice>; 7] = state[0..7].try_into().unwrap();
                let adv = RhoAdvices::from(cols);
                let axiliary = [state[8], state[9]];

                let base13_to_9 = [
                    meta.lookup_table_column(),
                    meta.lookup_table_column(),
                    meta.lookup_table_column(),
                ];
                let special =
                    [meta.lookup_table_column(), meta.lookup_table_column()];
                RhoConfig::configure(
                    meta,
                    state,
                    &adv,
                    axiliary,
                    base13_to_9,
                    special,
                )
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<F>,
            ) -> Result<(), Error> {
                config.load(&mut layouter)?;
                let state = layouter.assign_region(
                    || "assign input state",
                    |mut region| {
                        let offset = 0;
                        let state: [(Cell, F); 25] = self
                            .in_state
                            .iter()
                            .enumerate()
                            .map(|(idx, &value)| {
                                let cell = region
                                    .assign_advice(
                                        || format!("lane {}", idx),
                                        config.state[idx],
                                        offset,
                                        || Ok(value),
                                    )
                                    .unwrap();
                                (cell, value)
                            })
                            .collect::<Vec<_>>()
                            .try_into()
                            .unwrap();
                        Ok(state)
                    },
                )?;
                let next_state =
                    config.assign_rotation_checks(&mut layouter, state)?;
                assert_eq!(next_state.map(|lane| lane.1), self.out_state);
                layouter.assign_region(
                    || "assign output state",
                    |mut region| {
                        let offset = 1;
                        config.assign_region(
                            &mut region,
                            offset,
                            next_state,
                        )?;
                        Ok(())
                    },
                )?;
                Ok(())
            }
        }

        let input1: State = [
            [102, 111, 111, 98, 97],
            [114, 0, 5, 0, 0],
            [0, 0, 0, 0, 0],
            [0, 0, 0, 5, 0],
            [0, 0, 0, 0, 0],
        ];
        let mut in_biguint = StateBigInt::default();
        let mut in_state: [Fp; 25] = [Fp::zero(); 25];

        for (x, y) in (0..5).cartesian_product(0..5) {
            in_biguint[(x, y)] = convert_b2_to_b13(input1[x][y]);
        }
        let s0_arith = KeccakFArith::theta(&in_biguint);
        for (x, y) in (0..5).cartesian_product(0..5) {
            in_state[5 * x + y] = biguint_to_f(&s0_arith[(x, y)]);
        }
        let s1_arith = KeccakFArith::rho(&s0_arith);
        let mut out_state: [Fp; 25] = [Fp::zero(); 25];
        for (x, y) in (0..5).cartesian_product(0..5) {
            out_state[5 * x + y] = biguint_to_f(&s1_arith[(x, y)]);
        }
        let circuit = MyCircuit::<Fp> {
            in_state,
            out_state,
        };
        #[cfg(feature = "dev-graph")]
        {
            use plotters::prelude::*;
            let k = 15;
            let root =
                BitMapBackend::new("rho-test-circuit.png", (16384, 65536))
                    .into_drawing_area();
            root.fill(&WHITE).unwrap();
            let root = root.titled("Rho", ("sans-serif", 60)).unwrap();
            halo2::dev::CircuitLayout::default()
                .render(k, &circuit, &root)
                .unwrap();
        }
        // Test without public inputs
        let prover = MockProver::<Fp>::run(15, &circuit, vec![]).unwrap();

        assert_eq!(prover.verify(), Ok(()));
    }
}
