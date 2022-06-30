use crate::{
    arith_helpers::*,
    common::{NEXT_INPUTS_LANES, PERMUTATION},
    gate_helpers::biguint_to_f,
    permutation::{
        generic::GenericConfig,
        iota::IotaConstants,
        pi::pi_gate_permutation,
        rho::assign_rho,
        tables::{Base13toBase9TableConfig, FromBase9TableConfig, StackableTable},
    },
};
use eth_types::Field;
use halo2_proofs::{
    circuit::{AssignedCell, Layouter},
    plonk::{Advice, Column, ConstraintSystem, Error, TableColumn},
};
use itertools::Itertools;
use num_bigint::BigUint;

use super::{
    tables::{
        FromBinaryTableConfig, NUM_OF_B9_CHUNKS_PER_SLICE, NUM_OF_B9_SLICES,
        NUM_OF_BINARY_CHUNKS_PER_SLICE, NUM_OF_BINARY_SLICES,
    },
    theta::assign_theta,
    xi::assign_xi,
};

fn assign_next_input<F: Field>(
    layouter: &mut impl Layouter<F>,
    next_input_col: &Column<Advice>,
    next_input: &Option<[F; NEXT_INPUTS_LANES]>,
) -> Result<[AssignedCell<F, F>; NEXT_INPUTS_LANES], Error> {
    let next_input_b9 = layouter.assign_region(
        || "next input words",
        |mut region| {
            let mut next_input_b9: Vec<AssignedCell<F, F>> = vec![];
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
            for (offset, input) in next_input.iter().enumerate() {
                let cell = region.assign_advice(
                    || "next input words",
                    *next_input_col,
                    offset,
                    || Ok(input.unwrap_or_default()),
                )?;
                next_input_b9.push(cell);
            }
            Ok(next_input_b9)
        },
    )?;
    Ok(next_input_b9.try_into().unwrap())
}

fn convert_from_b9_to_b13<F: Field>(
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

#[derive(Clone, Debug)]
pub struct KeccakFConfig<F: Field> {
    generic: GenericConfig<F>,
    stackable: StackableTable<F>,
    base13to9_config: Base13toBase9TableConfig<F>,
    from_b9_table: FromBase9TableConfig<F>,
    from_b2_table: FromBinaryTableConfig<F>,
    advice: Column<Advice>,
}

impl<F: Field> KeccakFConfig<F> {
    // We assume state is received in base-9.
    pub fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let advices: [Column<Advice>; 3] = (0..3)
            .map(|_| {
                let column = meta.advice_column();
                meta.enable_equality(column);
                column
            })
            .collect_vec()
            .try_into()
            .unwrap();

        let fixed = meta.fixed_column();
        let generic = GenericConfig::configure(meta, advices, fixed);
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
        let from_base9_cols: [TableColumn; 3] = (0..3)
            .map(|_| meta.lookup_table_column())
            .collect_vec()
            .try_into()
            .unwrap();
        let from_base2_cols: [TableColumn; 3] = (0..3)
            .map(|_| meta.lookup_table_column())
            .collect_vec()
            .try_into()
            .unwrap();
        let stackable = StackableTable::configure(meta, advices, stackable_cols);
        let base13to9_config = Base13toBase9TableConfig::configure(meta, advices, base13to9_cols);
        let from_b9_table = FromBase9TableConfig::configure(meta, advices, from_base9_cols);
        let from_b2_table = FromBinaryTableConfig::configure(meta, advices, from_base2_cols);

        Self {
            generic,
            stackable,
            base13to9_config,
            from_b9_table,
            from_b2_table,
            advice: advices[0],
        }
    }

    pub fn load(&mut self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        self.stackable.load(layouter)?;
        self.base13to9_config.load(layouter)?;
        self.from_b9_table.load(layouter)?;
        self.from_b2_table.load(layouter)
    }

    // Result b13 state for next round, b2 state for end result
    pub fn assign_all(
        &self,
        layouter: &mut impl Layouter<F>,
        in_state: [AssignedCell<F, F>; 25],
        flag: bool,
        next_mixing: Option<[F; NEXT_INPUTS_LANES]>,
    ) -> Result<([AssignedCell<F, F>; 25], [AssignedCell<F, F>; 25]), Error> {
        let iota_constants = IotaConstants::default();
        let mut state = in_state;

        // First 23 rounds
        for round_idx in 0..PERMUTATION {
            // State in base-13
            state = assign_theta(&self.generic, layouter, &state)?;
            state = assign_rho(
                layouter,
                &self.base13to9_config,
                &self.generic,
                &self.stackable,
                &state,
            )?;
            // Outputs in base-9 which is what Pi requires
            state = pi_gate_permutation(&state);
            state = assign_xi(&self.generic, layouter, &state)?;

            // Last round before Mixing does not run IotaB9 nor BaseConversion
            if round_idx == PERMUTATION - 1 {
                break;
            }

            state[0] = self.generic.add_fixed(
                layouter,
                &state[0],
                &iota_constants.a4_times_round_constants_b9[round_idx],
            )?;

            // The resulting state is in Base-9 now. We now convert it to
            // base_13 which is what Theta requires again at the
            // start of the loop.
            state =
                convert_from_b9_to_b13(layouter, &self.from_b9_table, &self.generic, state, false)?
                    .0;
        }
        let (f_mix, f_no_mix) = self.stackable.assign_boolean_flag(layouter, Some(flag))?;
        state[0] = self.generic.conditional_add_const(
            layouter,
            &state[0],
            &f_no_mix,
            &iota_constants.a4_times_round_constants_b9[PERMUTATION - 1],
        )?;
        let next_input = assign_next_input(layouter, &self.advice, &next_mixing)?;

        // Convert to base 9 and multiply by A4
        let next_input = {
            let next_input = next_input
                .iter()
                .map(|input| {
                    let (base2s, base9s, _) = self.from_b2_table.assign_region(layouter, input)?;
                    let vs = (0..NUM_OF_BINARY_SLICES)
                        .map(|i| {
                            biguint_to_f(
                                &BigUint::from(B2).pow((NUM_OF_BINARY_CHUNKS_PER_SLICE * i) as u32),
                            )
                        })
                        .rev()
                        .collect_vec();
                    self.generic.linear_combine_consts(
                        layouter,
                        base2s,
                        vs,
                        Some(input.clone()),
                    )?;
                    let vs = (0..NUM_OF_BINARY_SLICES)
                        .map(|i| {
                            biguint_to_f::<F>(
                                &BigUint::from(B9).pow((NUM_OF_BINARY_CHUNKS_PER_SLICE * i) as u32),
                            ) * F::from(A4)
                        })
                        .rev()
                        .collect_vec();
                    let output =
                        self.generic
                            .linear_combine_consts(layouter, base9s.clone(), vs, None)?;
                    Ok(output)
                })
                .collect::<Result<Vec<AssignedCell<F, F>>, Error>>()?;
            let next_input: [AssignedCell<F, F>; NEXT_INPUTS_LANES] =
                next_input.try_into().unwrap();
            next_input
        };

        for (i, input) in next_input.iter().enumerate() {
            state[i] = self
                .generic
                .conditional_add_advice(layouter, &state[i], &f_mix, &input)?;
        }
        let (mut state_b13, state_b2) =
            convert_from_b9_to_b13(layouter, &self.from_b9_table, &self.generic, state, true)?;
        let state_b2 = state_b2.unwrap();
        state_b13[0] = self.generic.conditional_add_const(
            layouter,
            &state_b13[0],
            &f_mix,
            &iota_constants.round_constant_b13,
        )?;
        Ok((state_b13.try_into().unwrap(), state_b2))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::{State, NEXT_INPUTS_LANES};
    use crate::gate_helpers::biguint_to_f;
    use crate::keccak_arith::KeccakFArith;
    use halo2_proofs::circuit::Layouter;
    use halo2_proofs::pairing::bn256::Fr as Fp;
    use halo2_proofs::plonk::{ConstraintSystem, Error};
    use halo2_proofs::{circuit::SimpleFloorPlanner, dev::MockProver, plonk::Circuit};

    #[test]
    fn test_keccak_round() {
        #[derive(Default)]
        struct MyCircuit<F> {
            in_state: [F; 25],
            out_state: [F; 25],
            next_mixing: Option<[F; NEXT_INPUTS_LANES]>,
            // flag
            is_mixing: bool,
        }

        impl<F: Field> Circuit<F> for MyCircuit<F> {
            type Config = KeccakFConfig<F>;
            type FloorPlanner = SimpleFloorPlanner;

            fn without_witnesses(&self) -> Self {
                Self::default()
            }

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                Self::Config::configure(meta)
            }

            fn synthesize(
                &self,
                mut config: Self::Config,
                mut layouter: impl Layouter<F>,
            ) -> Result<(), Error> {
                // Load the table
                config.load(&mut layouter)?;

                let state: [AssignedCell<F, F>; 25] = layouter.assign_region(
                    || "Keccak round Wittnes & flag assignation",
                    |mut region| {
                        let state = self
                            .in_state
                            .iter()
                            .enumerate()
                            .map(|(offset, val)| {
                                region.assign_advice(
                                    || "witness input state",
                                    config.advice,
                                    offset,
                                    || Ok(*val),
                                )
                            })
                            .collect::<Result<Vec<AssignedCell<F, F>>, Error>>()?;

                        Ok(state.try_into().unwrap())
                    },
                )?;

                let (state_b13, state_b2) =
                    config.assign_all(&mut layouter, state, self.is_mixing, self.next_mixing)?;
                if self.is_mixing {
                    layouter.assign_region(
                        || "check final states",
                        |mut region| {
                            for (assigned, value) in state_b13.iter().zip(self.out_state.iter()) {
                                region.constrain_constant(assigned.cell(), value)?;
                            }
                            Ok(())
                        },
                    )
                } else {
                    layouter.assign_region(
                        || "check final states",
                        |mut region| {
                            for (assigned, value) in state_b2.iter().zip(self.out_state.iter()) {
                                region.constrain_constant(assigned.cell(), value)?;
                            }
                            Ok(())
                        },
                    )
                }
            }
        }

        let in_state: State = [
            [1, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
        ];

        let next_input: State = [
            [2, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
        ];

        let mut in_state_biguint = StateBigInt::default();

        // Generate in_state as `[Fp;25]`
        let mut in_state_fp: [Fp; 25] = [Fp::zero(); 25];
        for (x, y) in (0..5).cartesian_product(0..5) {
            in_state_fp[5 * x + y] = biguint_to_f(&convert_b2_to_b13(in_state[x][y]));
            in_state_biguint[(x, y)] = convert_b2_to_b13(in_state[x][y]);
        }

        // Compute out_state_mix
        let mut out_state_mix = in_state_biguint.clone();
        KeccakFArith::permute_and_absorb(&mut out_state_mix, Some(&next_input));

        // Compute out_state_non_mix
        let mut out_state_non_mix = in_state_biguint.clone();
        KeccakFArith::permute_and_absorb(&mut out_state_non_mix, None);

        for (x, y) in (0..5).cartesian_product(0..5) {
            out_state_non_mix[(x, y)] =
                convert_b9_lane_to_b2_biguint(out_state_non_mix[(x, y)].clone())
        }

        // Generate out_state as `[Fp;25]`
        let out_state_mix: [Fp; 25] = state_bigint_to_field(out_state_mix);
        let out_state_non_mix: [Fp; 25] = state_bigint_to_field(out_state_non_mix);

        // Generate next_input (tho one that is not None) in the form `[F;17]`
        // Generate next_input as `[Fp;NEXT_INPUTS_LANES]`
        let next_input_fp: [Fp; NEXT_INPUTS_LANES] =
            state_bigint_to_field(StateBigInt::from(next_input));

        // When we pass no `mixing_inputs`, we perform the full keccak round
        // ending with Mixing executing IotaB9
        {
            // With the correct input and output witnesses, the proof should
            // pass.
            let circuit = MyCircuit::<Fp> {
                in_state: in_state_fp,
                out_state: out_state_non_mix,
                next_mixing: None,
                is_mixing: false,
            };

            let prover = MockProver::<Fp>::run(17, &circuit, vec![]).unwrap();

            assert_eq!(prover.verify(), Ok(()), "is_mixing: false");

            // With wrong input and/or output witnesses, the proof should fail
            // to be verified.
            let circuit = MyCircuit::<Fp> {
                in_state: out_state_non_mix,
                out_state: out_state_non_mix,
                next_mixing: None,
                is_mixing: true,
            };
            let k = 17;
            let prover = MockProver::<Fp>::run(k, &circuit, vec![]).unwrap();

            #[cfg(feature = "dev-graph")]
            {
                use plotters::prelude::*;
                let root = BitMapBackend::new("keccak-f.png", (1024, 16384)).into_drawing_area();
                root.fill(&WHITE).unwrap();
                let root = root.titled("Keccak-F", ("sans-serif", 60)).unwrap();
                halo2_proofs::dev::CircuitLayout::default()
                    .show_labels(false)
                    .render(k, &circuit, &root)
                    .unwrap();
            }

            assert!(prover.verify().is_err());
        }

        // When we pass `mixing_inputs`, we perform the full keccak round ending
        // with Mixing executing Absorb + base_conversion + IotaB13
        {
            let circuit = MyCircuit::<Fp> {
                in_state: in_state_fp,
                out_state: out_state_mix,
                next_mixing: Some(next_input_fp),
                is_mixing: true,
            };

            let prover = MockProver::<Fp>::run(17, &circuit, vec![]).unwrap();

            assert_eq!(prover.verify(), Ok(()), "is_mixing: true");

            // With wrong input and/or output witnesses, the proof should fail
            // to be verified.
            let circuit = MyCircuit::<Fp> {
                in_state: out_state_non_mix,
                out_state: out_state_non_mix,
                next_mixing: Some(next_input_fp),
                is_mixing: true,
            };

            let prover = MockProver::<Fp>::run(17, &circuit, vec![]).unwrap();

            assert!(prover.verify().is_err());
        }
    }
}
