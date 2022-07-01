use eth_types::Field;
use halo2_proofs::{
    circuit::{AssignedCell, Layouter},
    plonk::{Advice, Column, Error},
};
use itertools::Itertools;
use std::convert::TryInto;
use std::vec;

use super::tables::{FromBinaryTableConfig, NUM_OF_BINARY_CHUNKS_PER_SLICE, NUM_OF_BINARY_SLICES};

use crate::{
    arith_helpers::{convert_b2_to_b13, convert_b2_to_b9, A1, A2, A3, A4, B13, B2, B9},
    common::{NEXT_INPUTS_LANES, PERMUTATION, ROTATION_CONSTANTS, ROUND_CONSTANTS},
    gate_helpers::{biguint_to_f, f_to_biguint},
    permutation::{
        generic::GenericConfig,
        rho_helpers::{slice_lane, RhoLane},
        tables::{
            Base13toBase9TableConfig, FromBase9TableConfig, StackableTable,
            NUM_OF_B9_CHUNKS_PER_SLICE, NUM_OF_B9_SLICES,
        },
    },
};

use num_bigint::BigUint;

pub fn assign_theta<F: Field>(
    generic: &GenericConfig<F>,
    layouter: &mut impl Layouter<F>,
    state: &[AssignedCell<F, F>; 25],
) -> Result<[AssignedCell<F, F>; 25], Error> {
    let theta_col_sums = (0..5)
        .map(|x| {
            generic.running_sum(
                layouter,
                (0..5).map(|y| state[5 * x + y].clone()).collect(),
                None,
            )
        })
        .collect::<Result<Vec<_>, Error>>()?;

    let out_state = (0..5)
        .cartesian_product(0..5)
        .map(|(x, y)| {
            let cells = vec![
                state[5 * x + y].clone(),
                theta_col_sums[(x + 4) % 5].clone(),
                theta_col_sums[(x + 1) % 5].clone(),
            ];
            let vs = vec![F::one(), F::one(), F::from(B13 as u64)];
            generic.linear_combine_consts(layouter, cells, vs, None)
        })
        .collect::<Result<Vec<_>, Error>>()?;

    Ok(out_state.try_into().unwrap())
}

pub fn assign_rho<F: Field>(
    layouter: &mut impl Layouter<F>,
    base13to9_config: &Base13toBase9TableConfig<F>,
    generic: &GenericConfig<F>,
    stackable: &StackableTable<F>,
    state: &[AssignedCell<F, F>; 25],
) -> Result<[AssignedCell<F, F>; 25], Error> {
    let mut next_state = vec![];
    let mut step2_od_join = vec![];
    let mut step3_od_join = vec![];
    for (lane_idx, lane) in state.iter().enumerate() {
        let rotation = {
            let x = lane_idx / 5;
            let y = lane_idx % 5;
            ROTATION_CONSTANTS[x][y]
        };
        let (conversions, special) =
            RhoLane::new(f_to_biguint(*lane.value().unwrap_or(&F::zero())), rotation)
                .get_full_witness();
        let slices = slice_lane(rotation);

        let (input_coefs, mut output_coefs, step2_od, step3_od) =
            base13to9_config.assign_region(layouter, &slices, &conversions)?;

        let input_pobs = conversions
            .iter()
            .map(|c| biguint_to_f::<F>(&c.input.power_of_base))
            .collect_vec();

        let mut output_pobs = conversions
            .iter()
            .map(|c| biguint_to_f::<F>(&c.output.power_of_base))
            .collect_vec();
        // Final output power of base
        output_pobs.push(biguint_to_f::<F>(&special.output_pob));

        let input_from_chunks =
            generic.linear_combine_consts(layouter, input_coefs, input_pobs, None)?;
        let last_chunk = generic.sub_advice(layouter, &lane, &input_from_chunks)?;

        let final_output_coef = stackable.lookup_special_chunks(layouter, &last_chunk)?;
        output_coefs.push(final_output_coef);

        let output_lane =
            generic.linear_combine_consts(layouter, output_coefs, output_pobs, None)?;
        next_state.push(output_lane);
        step2_od_join.extend(step2_od);
        step3_od_join.extend(step3_od);
    }
    let step2_sum = generic.running_sum(layouter, step2_od_join, None)?;
    let step3_sum = generic.running_sum(layouter, step3_od_join, None)?;
    stackable.lookup_range_12(layouter, &[step2_sum])?;
    stackable.lookup_range_169(layouter, &[step3_sum])?;
    Ok(next_state.try_into().unwrap())
}

/// The Keccak Pi step
///
/// It has no gates. We just have to permute the previous state into the correct
/// order. The copy constrain in the next gate can then enforce the Pi step
/// permutation.
pub fn pi_gate_permutation<F: Field>(state: &[AssignedCell<F, F>; 25]) -> [AssignedCell<F, F>; 25] {
    (0..5)
        .cartesian_product(0..5)
        .map(|(x, y)| state[5 * ((x + 3 * y) % 5) + x].clone())
        .collect::<Vec<_>>()
        .try_into()
        .unwrap()
}

pub fn assign_xi<F: Field>(
    generic: &GenericConfig<F>,
    layouter: &mut impl Layouter<F>,
    state: &[AssignedCell<F, F>; 25],
) -> Result<[AssignedCell<F, F>; 25], Error> {
    let out_state = (0..5)
        .cartesian_product(0..5)
        .map(|(x, y)| {
            let cells = vec![
                state[5 * x + y].clone(),
                state[5 * ((x + 1) % 5) + y].clone(),
                state[5 * ((x + 2) % 5) + y].clone(),
            ];
            let vs = vec![F::from(A1), F::from(A2), F::from(A3)];
            generic.linear_combine_consts(layouter, cells, vs, None)
        })
        .collect::<Result<Vec<_>, Error>>()?;
    Ok(out_state.try_into().unwrap())
}

#[derive(Clone, Debug)]
pub struct IotaConstants<F> {
    pub round_constant_b13: F,
    pub a4_times_round_constants_b9: [F; PERMUTATION],
}

impl<F: Field> Default for IotaConstants<F> {
    fn default() -> Self {
        let round_constant_b13 =
            biguint_to_f::<F>(&convert_b2_to_b13(ROUND_CONSTANTS[PERMUTATION - 1]));

        let a4_times_round_constants_b9: [F; 24] = ROUND_CONSTANTS
            .iter()
            .map(|&x| {
                let constant = A4 * convert_b2_to_b9(x);
                biguint_to_f::<F>(&constant)
            })
            .collect_vec()
            .try_into()
            .unwrap();

        Self {
            round_constant_b13,
            a4_times_round_constants_b9,
        }
    }
}

pub fn assign_next_input<F: Field>(
    layouter: &mut impl Layouter<F>,
    next_input_col: &Column<Advice>,
    next_input: &Option<[F; NEXT_INPUTS_LANES]>,
) -> Result<[AssignedCell<F, F>; NEXT_INPUTS_LANES], Error> {
    let next_input_b9 = layouter.assign_region(
        || "next input words",
        |mut region| {
            let next_input = next_input.map_or(
                [None; NEXT_INPUTS_LANES],
                |v| -> [Option<F>; NEXT_INPUTS_LANES] {
                    v.map(|vv| Some(vv))
                        .iter()
                        .cloned()
                        .collect_vec()
                        .try_into()
                        .unwrap()
                },
            );
            next_input
                .iter()
                .enumerate()
                .map(|(offset, input)| {
                    region.assign_advice(
                        || "next input words",
                        *next_input_col,
                        offset,
                        || Ok(input.unwrap_or_default()),
                    )
                })
                .collect::<Result<Vec<_>, Error>>()
        },
    )?;
    Ok(next_input_b9.try_into().unwrap())
}

pub fn convert_to_b9_mul_a4<F: Field>(
    layouter: &mut impl Layouter<F>,
    from_b2_table: &FromBinaryTableConfig<F>,
    generic: &GenericConfig<F>,
    next_input: &[AssignedCell<F, F>; NEXT_INPUTS_LANES],
) -> Result<[AssignedCell<F, F>; NEXT_INPUTS_LANES], Error> {
    let next_input = next_input
        .iter()
        .map(|input| {
            let (base2s, base9s, _) = from_b2_table.assign_region(layouter, input)?;
            let vs = (0..NUM_OF_BINARY_SLICES)
                .map(|i| {
                    biguint_to_f(
                        &BigUint::from(B2).pow((NUM_OF_BINARY_CHUNKS_PER_SLICE * i) as u32),
                    )
                })
                .rev()
                .collect_vec();
            generic.linear_combine_consts(layouter, base2s, vs, Some(input.clone()))?;
            let vs = (0..NUM_OF_BINARY_SLICES)
                .map(|i| {
                    biguint_to_f::<F>(
                        &BigUint::from(B9).pow((NUM_OF_BINARY_CHUNKS_PER_SLICE * i) as u32),
                    ) * F::from(A4)
                })
                .rev()
                .collect_vec();
            let output = generic.linear_combine_consts(layouter, base9s.clone(), vs, None)?;
            Ok(output)
        })
        .collect::<Result<Vec<AssignedCell<F, F>>, Error>>()?;
    let next_input: [AssignedCell<F, F>; NEXT_INPUTS_LANES] = next_input.try_into().unwrap();
    Ok(next_input)
}

pub fn convert_from_b9_to_b13<F: Field>(
    layouter: &mut impl Layouter<F>,
    from_b9_table: &FromBase9TableConfig<F>,
    generic: &GenericConfig<F>,
    state: [AssignedCell<F, F>; 25],
    output_b2: bool,
) -> Result<([AssignedCell<F, F>; 25], Option<[AssignedCell<F, F>; 25]>), Error> {
    let (state_b13, state_b2): (Vec<AssignedCell<F, F>>, Vec<Option<AssignedCell<F, F>>>) = state
        .iter()
        .map(|lane| {
            let (base9s, base_13s, base_2s) = from_b9_table.assign_region(layouter, lane)?;
            let vs = (0..NUM_OF_B9_SLICES)
                .map(|i| {
                    biguint_to_f(&BigUint::from(B9).pow((NUM_OF_B9_CHUNKS_PER_SLICE * i) as u32))
                })
                .rev()
                .collect_vec();
            generic.linear_combine_consts(layouter, base9s, vs, Some(lane.clone()))?;
            let vs = (0..NUM_OF_B9_SLICES)
                .map(|i| {
                    biguint_to_f(&BigUint::from(B13).pow((NUM_OF_B9_CHUNKS_PER_SLICE * i) as u32))
                })
                .rev()
                .collect_vec();
            let lane_b13 = generic.linear_combine_consts(layouter, base_13s, vs, None)?;
            let lane_b2 = if output_b2 {
                let vs = (0..NUM_OF_B9_SLICES)
                    .map(|i| {
                        biguint_to_f(
                            &BigUint::from(B2).pow((NUM_OF_B9_CHUNKS_PER_SLICE * i) as u32),
                        )
                    })
                    .rev()
                    .collect_vec();
                let lane_b2 = generic.linear_combine_consts(layouter, base_2s, vs, None)?;
                Some(lane_b2)
            } else {
                None
            };
            Ok((lane_b13, lane_b2))
        })
        .collect::<Result<Vec<_>, Error>>()?
        .iter()
        .cloned()
        .unzip();
    let state_b2: Option<[AssignedCell<F, F>; 25]> = state_b2
        .into_iter()
        .collect::<Option<Vec<_>>>()
        .map(|v| v.try_into().unwrap());

    Ok((state_b13.try_into().unwrap(), state_b2))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arith_helpers::StateBigInt;
    use crate::common::*;
    use crate::gate_helpers::biguint_to_f;
    use crate::keccak_arith::*;
    use halo2_proofs::{
        circuit::{Layouter, SimpleFloorPlanner},
        dev::MockProver,
        pairing::bn256::Fr as Fp,
        plonk::{Advice, Circuit, Column, ConstraintSystem, Error, TableColumn},
    };
    use itertools::Itertools;
    use std::convert::TryInto;
    use std::marker::PhantomData;

    #[test]
    fn test_theta_gates() {
        #[derive(Clone, Debug)]
        struct MyConfig<F> {
            lane: Column<Advice>,
            generic: GenericConfig<F>,
        }

        impl<F: Field> MyConfig<F> {
            pub fn configure(meta: &mut ConstraintSystem<F>) -> Self {
                let advices: [Column<Advice>; 3] = (0..3)
                    .map(|_| {
                        let column = meta.advice_column();
                        meta.enable_equality(column);
                        column
                    })
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap();
                let fixed = meta.fixed_column();

                let lane = advices[0];
                let generic = GenericConfig::configure(meta, advices, fixed);
                Self { lane, generic }
            }
        }
        #[derive(Default)]
        struct MyCircuit<F> {
            in_state: [F; 25],
            out_state: [F; 25],
            _marker: PhantomData<F>,
        }
        impl<F: Field> Circuit<F> for MyCircuit<F> {
            type Config = MyConfig<F>;
            type FloorPlanner = SimpleFloorPlanner;

            fn without_witnesses(&self) -> Self {
                Self::default()
            }

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                // this column is required by `constrain_constant`
                let constant = meta.fixed_column();
                meta.enable_constant(constant);
                Self::Config::configure(meta)
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<F>,
            ) -> Result<(), Error> {
                let in_state = layouter.assign_region(
                    || "Wittnes & assignation",
                    |mut region| {
                        // Witness `state`
                        let in_state: [AssignedCell<F, F>; 25] = {
                            let mut state: Vec<AssignedCell<F, F>> = Vec::with_capacity(25);
                            for (offset, val) in self.in_state.iter().enumerate() {
                                let cell = region.assign_advice(
                                    || "witness input state",
                                    config.lane,
                                    offset,
                                    || Ok(*val),
                                )?;
                                state.push(cell)
                            }
                            state.try_into().unwrap()
                        };
                        Ok(in_state)
                    },
                )?;

                let out_state = assign_theta(&config.generic, &mut layouter, &in_state)?;

                layouter.assign_region(
                    || "Check outstate",
                    |mut region| {
                        for (assigned, value) in out_state.iter().zip(self.out_state.iter()) {
                            region.constrain_constant(assigned.cell(), value)?;
                        }
                        Ok(())
                    },
                )?;
                Ok(())
            }
        }

        let input1: State = [
            [1, 0, 0, 0, 0],
            [0, 0, 0, 9223372036854775808, 0],
            [0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
        ];
        let mut in_biguint = StateBigInt::default();
        let mut in_state: [Fp; 25] = [Fp::zero(); 25];

        for (x, y) in (0..5).cartesian_product(0..5) {
            in_biguint[(x, y)] = convert_b2_to_b13(input1[x][y]);
            in_state[5 * x + y] = biguint_to_f(&in_biguint[(x, y)]);
        }
        let s1_arith = KeccakFArith::theta(&in_biguint);
        let mut out_state: [Fp; 25] = [Fp::zero(); 25];
        for (x, y) in (0..5).cartesian_product(0..5) {
            out_state[5 * x + y] = biguint_to_f(&s1_arith[(x, y)]);
        }

        let circuit = MyCircuit::<Fp> {
            in_state,
            out_state,
            _marker: PhantomData,
        };

        // Test without public inputs
        let prover = MockProver::<Fp>::run(9, &circuit, vec![]).unwrap();

        assert_eq!(prover.verify(), Ok(()));

        let mut out_state2 = out_state;
        out_state2[0] = Fp::from(5566u64);

        let circuit2 = MyCircuit::<Fp> {
            in_state,
            out_state: out_state2,
            _marker: PhantomData,
        };

        let prover = MockProver::<Fp>::run(9, &circuit2, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn test_rho_gate() {
        #[derive(Default)]
        struct MyCircuit<F> {
            in_state: [F; 25],
            out_state: [F; 25],
        }

        #[derive(Clone)]
        struct MyConfig<F> {
            advice: Column<Advice>,
            generic: GenericConfig<F>,
            stackable: StackableTable<F>,
            base13to9_config: Base13toBase9TableConfig<F>,
        }
        impl<F: Field> Circuit<F> for MyCircuit<F> {
            type Config = MyConfig<F>;
            type FloorPlanner = SimpleFloorPlanner;

            fn without_witnesses(&self) -> Self {
                Self::default()
            }

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                let advices: [Column<Advice>; 3] = (0..3)
                    .map(|_| meta.advice_column())
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap();

                let fixed = meta.fixed_column();
                let stackable_cols: [TableColumn; 3] = (0..3)
                    .map(|_| meta.lookup_table_column())
                    .collect_vec()
                    .try_into()
                    .unwrap();
                let base13to9_cols: [TableColumn; 3] = (0..3)
                    .map(|_| meta.lookup_table_column())
                    .collect_vec()
                    .try_into()
                    .unwrap();
                let stackable = StackableTable::configure(meta, advices, stackable_cols);
                let generic = GenericConfig::configure(meta, advices, fixed);
                let base13to9_config =
                    Base13toBase9TableConfig::configure(meta, advices, base13to9_cols);

                Self::Config {
                    advice: advices[0],
                    generic,
                    stackable,
                    base13to9_config,
                }
            }

            fn synthesize(
                &self,
                mut config: Self::Config,
                mut layouter: impl Layouter<F>,
            ) -> Result<(), Error> {
                config.base13to9_config.load(&mut layouter)?;
                config.stackable.load(&mut layouter)?;
                let state = layouter.assign_region(
                    || "assign input state",
                    |mut region| {
                        let state = self
                            .in_state
                            .iter()
                            .enumerate()
                            .map(|(offset, &value)| {
                                region.assign_advice(|| "lane", config.advice, offset, || Ok(value))
                            })
                            .collect::<Result<Vec<AssignedCell<F, F>>, Error>>()?;

                        Ok(state.try_into().unwrap())
                    },
                )?;
                let out_state = assign_rho(
                    &mut layouter,
                    &config.base13to9_config,
                    &config.generic,
                    &config.stackable,
                    &state,
                )?;
                layouter.assign_region(
                    || "check final states",
                    |mut region| {
                        for (assigned, value) in out_state.iter().zip(self.out_state.iter()) {
                            region.constrain_constant(assigned.cell(), value)?;
                        }
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

    #[test]
    fn test_xi_gate() {
        #[derive(Clone, Debug)]
        struct MyConfig<F> {
            lane: Column<Advice>,
            generic: GenericConfig<F>,
        }

        impl<F: Field> MyConfig<F> {
            pub fn configure(meta: &mut ConstraintSystem<F>) -> Self {
                let advices: [Column<Advice>; 3] = (0..3)
                    .map(|_| {
                        let column = meta.advice_column();
                        meta.enable_equality(column);
                        column
                    })
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap();
                let fixed = meta.fixed_column();

                let lane = advices[0];
                let generic = GenericConfig::configure(meta, advices, fixed);
                Self { lane, generic }
            }
        }
        #[derive(Default)]
        struct MyCircuit<F> {
            in_state: [F; 25],
            out_state: [F; 25],
            _marker: PhantomData<F>,
        }

        impl<F: Field> Circuit<F> for MyCircuit<F> {
            type Config = MyConfig<F>;
            type FloorPlanner = SimpleFloorPlanner;

            fn without_witnesses(&self) -> Self {
                Self::default()
            }

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                // this column is required by `constrain_constant`
                let constant = meta.fixed_column();
                meta.enable_constant(constant);
                Self::Config::configure(meta)
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<F>,
            ) -> Result<(), Error> {
                let in_state = layouter.assign_region(
                    || "Wittnes & assignation",
                    |mut region| {
                        // Witness `state`
                        let in_state: [AssignedCell<F, F>; 25] = {
                            let mut state: Vec<AssignedCell<F, F>> = Vec::with_capacity(25);
                            for (offset, val) in self.in_state.iter().enumerate() {
                                let cell = region.assign_advice(
                                    || "witness input state",
                                    config.lane,
                                    offset,
                                    || Ok(*val),
                                )?;
                                state.push(cell)
                            }
                            state.try_into().unwrap()
                        };
                        Ok(in_state)
                    },
                )?;

                let out_state = assign_xi(&config.generic, &mut layouter, &in_state)?;

                layouter.assign_region(
                    || "Check outstate",
                    |mut region| {
                        for (assigned, value) in out_state.iter().zip(self.out_state.iter()) {
                            region.constrain_constant(assigned.cell(), value)?;
                        }
                        Ok(())
                    },
                )?;
                Ok(())
            }
        }

        let input1: State = [
            [1, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
        ];
        let mut in_biguint = StateBigInt::default();
        let mut in_state: [Fp; 25] = [Fp::zero(); 25];

        for (x, y) in (0..5).cartesian_product(0..5) {
            in_biguint[(x, y)] = convert_b2_to_b9(input1[x][y]);
            in_state[5 * x + y] = biguint_to_f(&in_biguint[(x, y)]);
        }
        let s1_arith = KeccakFArith::xi(&in_biguint);
        let mut out_state: [Fp; 25] = [Fp::zero(); 25];
        for (x, y) in (0..5).cartesian_product(0..5) {
            out_state[5 * x + y] = biguint_to_f(&s1_arith[(x, y)]);
        }
        let circuit = MyCircuit::<Fp> {
            in_state,
            out_state,
            _marker: PhantomData,
        };

        // Test without public inputs
        let prover = MockProver::<Fp>::run(9, &circuit, vec![]).unwrap();

        assert_eq!(prover.verify(), Ok(()));
    }
}
