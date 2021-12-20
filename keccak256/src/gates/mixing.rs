use super::{
    absorb::{AbsorbConfig, ABSORB_NEXT_INPUTS},
    iota_b13::IotaB13Config,
    iota_b9::IotaB9Config,
};
use crate::arith_helpers::*;
use crate::common::*;
use halo2::{
    circuit::{Cell, Layouter},
    plonk::{Advice, Column, ConstraintSystem, Error},
};
use pairing::arithmetic::FieldExt;
use std::convert::TryInto;

#[derive(Clone, Debug)]
pub struct MixingConfig<F> {
    iota_b9_config: IotaB9Config<F>,
    iota_b13_config: IotaB13Config<F>,
    absorb_config: AbsorbConfig<F>,
    state: [Column<Advice>; 25],
    flag: Column<Advice>,
}

impl<F: FieldExt> MixingConfig<F> {
    pub fn configure(meta: &mut ConstraintSystem<F>) -> MixingConfig<F> {
        // Allocate space for the flag column from which we will copy to all of
        // the sub-configs.
        let flag = meta.advice_column();
        meta.enable_equality(flag.into());

        // Allocate state columns and enable copy constraints for them.
        let state: [Column<Advice>; 25] = (0..25)
            .map(|_| {
                let column = meta.advice_column();
                meta.enable_equality(column.into());
                column
            })
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        // Allocate space for the round constants in base-9 which is an
        // instance column
        let round_ctant_b9 = meta.advice_column();
        let round_constants_b9 = meta.instance_column();

        // Allocate space for the round constants in base-13 which is an
        // instance column
        let round_ctant_b13 = meta.advice_column();
        let round_constants_b13 = meta.instance_column();

        // We mix -> Flag = true
        let iota_b9_config = IotaB9Config::configure(
            meta,
            state,
            round_ctant_b9,
            round_constants_b9,
        );
        // We don't mix -> Flag = false
        let absorb_config = AbsorbConfig::configure(meta, state);
        let iota_b13_config = IotaB13Config::configure(
            meta,
            state,
            round_ctant_b13,
            round_constants_b13,
        );

        MixingConfig {
            iota_b9_config,
            iota_b13_config,
            absorb_config,
            state,
            flag,
        }
    }

    pub fn assign_state(
        &self,
        layouter: &mut impl Layouter<F>,
        in_state: [(Cell, F); 25],
        out_state: [F; 25],
        flag: bool,
        next_mixing: Option<[F; ABSORB_NEXT_INPUTS]>,
        absolute_row_b9: usize,
        absolute_row_b13: usize,
    ) -> Result<[(Cell, F); 25], Error> {
        // Witness the mixing flag.
        let val: F = (flag as u64).into();
        let flag_cell = layouter.assign_region(
            || "Mixing witnessing",
            |mut region| {
                let offset: usize = 0;
                // Witness `is_mixing` flag.
                let cell = region.assign_advice(
                    || "witness is_mixing",
                    self.flag,
                    offset,
                    || Ok(val),
                )?;
                Ok((cell, val))
            },
        )?;

        // If we mix:
        let mix_res = self.iota_b9_config.last_round(
            layouter,
            in_state,
            out_state,
            absolute_row_b9,
            flag_cell,
        );

        // If we don't mix:
        // Absorb
        let (out_state_absorb_cells, flag_cell) =
            self.absorb_config.copy_state_flag_next_inputs(
                layouter,
                in_state,
                out_state,
                next_mixing.unwrap_or_default(),
                flag_cell,
            )?;

        // Base conversion assign

        // IotaB13
        let non_mix_res = self.iota_b13_config.copy_state_flag_and_assing_rc(
            layouter,
            out_state_absorb_cells,
            out_state,
            absolute_row_b13,
            flag_cell,
        );

        if flag {
            mix_res
        } else {
            non_mix_res
        }
    }

    /// Given an `in_state` as [`State`] and `next_inputs` as [`Option<State>`],
    /// compute the result of the mixing step depending on the mixing flag
    /// returning the `in_state`, `out_state` and `next_inputs` (if any) on a
    /// way on which can be directly witnessed in the circuit.
    pub(crate) fn compute_circ_states(
        in_state: State,
        next_inputs: Option<State>,
    ) -> ([F; 25], [F; 25], Option<[F; ABSORB_NEXT_INPUTS]>) {
        if let Some(next_inputs) = next_inputs {
            // We mix, therefore we apply Absorb + IotaB13
            let (in_state, out, next_inputs) =
                AbsorbConfig::compute_circ_states(in_state.into(), next_inputs);
            let (_, out_state) = IotaB13Config::compute_circ_states(
                state_to_state_bigint::<F, 25>(out).into(),
            );
            (in_state, out_state, Some(next_inputs))
        } else {
            // We don't mix, therefore we run IotaB9
            let (in_state, out_state) =
                IotaB9Config::compute_circ_states(in_state.into());
            (in_state, out_state, None)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::{State, PERMUTATION, ROUND_CONSTANTS};
    use halo2::circuit::Layouter;
    use halo2::plonk::{ConstraintSystem, Error};
    use halo2::{circuit::SimpleFloorPlanner, dev::MockProver, plonk::Circuit};
    use pairing::bn256::Fr as Fp;
    use pretty_assertions::assert_eq;
    use std::convert::TryInto;

    #[ignore]
    #[test]
    fn test_mixing_gate() {
        #[derive(Default)]
        struct MyCircuit<F> {
            in_state: [F; 25],
            out_state: [F; 25],
            next_mixing: Option<[F; ABSORB_NEXT_INPUTS]>,
            // This usize is indeed pointing the exact row of the
            // ROUND_CTANTS_B9 we want to use.
            round_ctant_b9: usize,
            // This usize is indeed pointing the exact row of the
            // ROUND_CTANTS_B13 we want to use.
            round_ctant_b13: usize,
            // flag
            is_mixing: bool,
        }

        impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
            type Config = MixingConfig<F>;
            type FloorPlanner = SimpleFloorPlanner;

            fn without_witnesses(&self) -> Self {
                Self::default()
            }

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                MixingConfig::configure(meta)
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<F>,
            ) -> Result<(), Error> {
                let offset: usize = 0;

                let in_state = layouter.assign_region(
                    || "Wittnes & assignation",
                    |mut region| {
                        // Witness `state`
                        let in_state: [(Cell, F); 25] = {
                            let mut state: Vec<(Cell, F)> =
                                Vec::with_capacity(25);
                            for (idx, val) in self.in_state.iter().enumerate() {
                                let cell = region.assign_advice(
                                    || "witness input state",
                                    config.state[idx],
                                    offset,
                                    || Ok(*val),
                                )?;
                                state.push((cell, *val))
                            }
                            state.try_into().unwrap()
                        };
                        Ok(in_state)
                    },
                )?;

                config.assign_state(
                    &mut layouter,
                    in_state,
                    self.out_state,
                    self.is_mixing,
                    self.next_mixing,
                    self.round_ctant_b9,
                    self.round_ctant_b13,
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

        let next_input: State = [
            [2, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
        ];

        let (in_state, out_mixing_state, next_mixing) =
            MixingConfig::compute_circ_states(input1, Some(next_input));

        let (_, out_non_mixing_state, _) =
            MixingConfig::compute_circ_states(input1, None);

        let constants_b13: Vec<Fp> = ROUND_CONSTANTS
            .iter()
            .map(|num| big_uint_to_field(&convert_b2_to_b13(*num)))
            .collect();

        let constants_b9: Vec<Fp> = ROUND_CONSTANTS
            .iter()
            .map(|num| big_uint_to_field(&convert_b2_to_b9(*num)))
            .collect();

        // With flag set to false, we mix. And so we should obtain Absorb +
        // IotaB13 result
        {
            // FIXME: This should be passing
            // With the correct input and output witnesses, the proof should
            // pass.
            let circuit = MyCircuit::<Fp> {
                in_state,
                out_state: out_mixing_state,
                next_mixing,
                is_mixing: false,
                round_ctant_b13: PERMUTATION - 1,
                round_ctant_b9: PERMUTATION - 1,
            };

            let prover = MockProver::<Fp>::run(
                9,
                &circuit,
                vec![constants_b9.clone(), constants_b13.clone()],
            )
            .unwrap();

            assert_eq!(prover.verify(), Ok(()));

            // With wrong input and/or output witnesses, the proof should fail
            // to be verified.
            let circuit = MyCircuit::<Fp> {
                in_state,
                out_state: out_non_mixing_state,
                next_mixing,
                is_mixing: false,
                round_ctant_b13: PERMUTATION - 1,
                round_ctant_b9: PERMUTATION - 1,
            };

            let prover = MockProver::<Fp>::run(
                9,
                &circuit,
                vec![constants_b9.clone(), constants_b13.clone()],
            )
            .unwrap();

            assert!(prover.verify().is_err());
        }

        // With flag set to `true`, we don't mix. And so we should obtain IotaB9
        // application as result.
        {
            let circuit = MyCircuit::<Fp> {
                in_state,
                out_state: out_mixing_state,
                next_mixing,
                is_mixing: true,
                round_ctant_b13: PERMUTATION - 1,
                round_ctant_b9: PERMUTATION - 1,
            };

            let prover = MockProver::<Fp>::run(
                9,
                &circuit,
                vec![constants_b9.clone(), constants_b13.clone()],
            )
            .unwrap();

            assert_eq!(prover.verify(), Ok(()));

            // FIXME: This should be failing.
            // With wrong input and/or output witnesses, the proof should fail
            // to be verified.
            let circuit = MyCircuit::<Fp> {
                in_state,
                out_state: out_non_mixing_state,
                next_mixing,
                is_mixing: true,
                round_ctant_b13: PERMUTATION - 1,
                round_ctant_b9: PERMUTATION - 1,
            };

            let prover = MockProver::<Fp>::run(
                9,
                &circuit,
                vec![constants_b9, constants_b13],
            )
            .unwrap();

            assert!(prover.verify().is_err());
        }
    }
}
