use crate::permutation::{
    generic::GenericConfig,
    rho_checks::LaneRotateConversionConfig,
    tables::{Base13toBase9TableConfig, StackableTable},
};

use eth_types::Field;
use halo2_proofs::{
    circuit::{AssignedCell, Layouter},
    plonk::{Advice, Column, ConstraintSystem, Error, Fixed},
};

#[derive(Debug, Clone)]
pub struct RhoConfig<F> {
    lane_config: LaneRotateConversionConfig<F>,
    base13_to_9_table: Base13toBase9TableConfig<F>,
    stackable: StackableTable<F>,
    generic: GenericConfig<F>,
}

impl<F: Field> RhoConfig<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        state: [Column<Advice>; 25],
        fixed: Column<Fixed>,
        generic: GenericConfig<F>,
        stackable: StackableTable<F>,
    ) -> Self {
        state.iter().for_each(|col| meta.enable_equality(*col));
        let base13_to_9_table = Base13toBase9TableConfig::configure(meta);

        let lane_config = LaneRotateConversionConfig::configure(
            meta,
            &base13_to_9_table,
            state[0..3].try_into().unwrap(),
            fixed,
            generic.clone(),
            stackable.clone(),
        );
        Self {
            lane_config,
            base13_to_9_table,
            stackable,
            generic,
        }
    }
    pub fn assign_rotation_checks(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &[AssignedCell<F, F>; 25],
    ) -> Result<[AssignedCell<F, F>; 25], Error> {
        type R<F> = (
            AssignedCell<F, F>,
            Vec<AssignedCell<F, F>>,
            Vec<AssignedCell<F, F>>,
        );
        let lane_and_ods: Result<Vec<R<F>>, Error> = state
            .iter()
            .enumerate()
            .map(|(idx, lane)| -> Result<R<F>, Error> {
                let (out_lane, step2_od, step3_od) =
                    self.lane_config
                        .assign_region(layouter, lane.clone(), idx)?;
                Ok((out_lane, step2_od, step3_od))
            })
            .into_iter()
            .collect();
        let lane_and_ods = lane_and_ods?;
        let lane_and_ods: [R<F>; 25] = lane_and_ods.try_into().unwrap();
        let next_state = lane_and_ods.clone().map(|(out_lane, _, _)| out_lane);

        let step2_od_join = lane_and_ods
            .iter()
            .flat_map(|(_, step2_od, _)| step2_od.clone())
            .collect::<Vec<_>>();
        let step3_od_join = lane_and_ods
            .iter()
            .flat_map(|(_, _, step3_od)| step3_od.clone())
            .collect::<Vec<_>>();
        let step2_sum = self.generic.running_sum(layouter, step2_od_join, None)?;
        let step3_sum = self.generic.running_sum(layouter, step3_od_join, None)?;
        self.stackable.lookup_range_12(layouter, &[step2_sum])?;
        self.stackable.lookup_range_169(layouter, &[step3_sum])?;
        Ok(next_state)
    }

    pub fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        self.base13_to_9_table.load(layouter)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arith_helpers::*;
    use crate::common::*;
    use crate::gate_helpers::biguint_to_f;
    use crate::keccak_arith::*;
    use halo2_proofs::{
        circuit::{Layouter, SimpleFloorPlanner},
        dev::MockProver,
        pairing::bn256::Fr as Fp,
        plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Selector, TableColumn},
        poly::Rotation,
    };
    use itertools::Itertools;

    #[test]
    fn test_rho_gate() {
        #[derive(Default)]
        struct MyCircuit<F> {
            in_state: [F; 25],
            out_state: [F; 25],
        }

        #[derive(Clone)]
        struct MyConfig<F> {
            q_enable: Selector,
            rho_config: RhoConfig<F>,
            stackable: StackableTable<F>,
            state: [Column<Advice>; 25],
        }
        impl<F: Field> Circuit<F> for MyCircuit<F> {
            type Config = MyConfig<F>;
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

                let fixed = meta.fixed_column();
                let table_cols: [TableColumn; 3] = (0..3)
                    .map(|_| meta.lookup_table_column())
                    .collect_vec()
                    .try_into()
                    .unwrap();
                let stackable =
                    StackableTable::configure(meta, state[0..3].try_into().unwrap(), table_cols);
                let generic =
                    GenericConfig::configure(meta, state[0..3].try_into().unwrap(), fixed);

                let rho_config =
                    RhoConfig::configure(meta, state, fixed, generic, stackable.clone());

                let q_enable = meta.selector();
                meta.create_gate("Check states", |meta| {
                    let q_enable = meta.query_selector(q_enable);
                    state
                        .iter()
                        .map(|col| {
                            let final_state = meta.query_advice(*col, Rotation::cur());
                            let expected_final_state = meta.query_advice(*col, Rotation::next());
                            q_enable.clone() * (final_state - expected_final_state)
                        })
                        .collect::<Vec<_>>()
                });

                MyConfig {
                    q_enable,
                    rho_config,
                    stackable,
                    state,
                }
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<F>,
            ) -> Result<(), Error> {
                config.rho_config.load(&mut layouter)?;
                config.stackable.load(&mut layouter)?;
                let state = layouter.assign_region(
                    || "assign input state",
                    |mut region| {
                        let offset = 0;
                        let state: [AssignedCell<F, F>; 25] = self
                            .in_state
                            .iter()
                            .enumerate()
                            .map(|(idx, &value)| {
                                region
                                    .assign_advice(
                                        || format!("lane {}", idx),
                                        config.state[idx],
                                        offset,
                                        || Ok(value),
                                    )
                                    .unwrap()
                            })
                            .collect::<Vec<_>>()
                            .try_into()
                            .unwrap();
                        Ok(state)
                    },
                )?;
                let out_state = config
                    .rho_config
                    .assign_rotation_checks(&mut layouter, &state)?;
                layouter.assign_region(
                    || "check final states",
                    |mut region| {
                        config.q_enable.enable(&mut region, 0)?;
                        out_state.iter().enumerate().for_each(|(idx, cell)| {
                            cell.copy_advice(
                                || "out_state obtained",
                                &mut region,
                                config.state[idx],
                                0,
                            )
                            .unwrap();
                        });

                        self.out_state.iter().enumerate().for_each(|(idx, &value)| {
                            region
                                .assign_advice(
                                    || format!("lane {}", idx),
                                    config.state[idx],
                                    1,
                                    || Ok(value),
                                )
                                .unwrap();
                        });

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
        let k = 15;
        #[cfg(feature = "dev-graph")]
        {
            use plotters::prelude::*;
            let root =
                BitMapBackend::new("rho-test-circuit.png", (1024, 16384)).into_drawing_area();
            root.fill(&WHITE).unwrap();
            let root = root.titled("Rho", ("sans-serif", 60)).unwrap();
            halo2_proofs::dev::CircuitLayout::default()
                .render(k, &circuit, &root)
                .unwrap();
        }
        // Test without public inputs
        let prover = MockProver::<Fp>::run(k, &circuit, vec![]).unwrap();

        assert_eq!(prover.verify(), Ok(()));
    }
}
