use super::{
    absorb::apply_absorb, add::AddConfig, base_conversion::BaseConversionConfig, flag::FlagConfig,
    iota::IotaConfig,
};
use crate::common::*;
use eth_types::Field;
use halo2_proofs::{
    circuit::{AssignedCell, Layouter},
    plonk::{Advice, Column, Error},
};
use itertools::izip;
use std::convert::TryInto;

#[derive(Clone, Debug)]
pub(crate) struct MixingConfig<F> {
    iota_config: IotaConfig<F>,
    from9_config: BaseConversionConfig<F>,
    add: AddConfig<F>,
    flag: FlagConfig<F>,
    advice: Column<Advice>,
}

impl<F: Field> MixingConfig<F> {
    pub fn configure(
        from9_config: BaseConversionConfig<F>,
        iota_config: IotaConfig<F>,
        add: &AddConfig<F>,
        flag: FlagConfig<F>,
        advice: Column<Advice>,
    ) -> Self {
        Self {
            from9_config,
            iota_config,
            add: add.clone(),
            flag,
            advice,
        }
    }

    pub fn assign_state(
        &self,
        layouter: &mut impl Layouter<F>,
        in_state: &[AssignedCell<F, F>; 25],
        flag: Option<bool>,
        next_mixing: [Option<F>; NEXT_INPUTS_LANES],
    ) -> Result<[AssignedCell<F, F>; 25], Error> {
        let (f_pos, f_neg) = self.flag.assign_flag(layouter, flag)?;

        // If we don't mix:
        // IotaB9
        let state_non_mix = {
            let mut state = in_state.clone();
            state[0] =
                self.iota_config
                    .assign_b9_last_round(layouter, state[0].clone(), f_neg.clone())?;
            state
        };

        // If we mix:
        // Absorb
        let state_mix = apply_absorb(&self.add, layouter, self.advice, in_state, &next_mixing)?;

        // Base conversion assign
        let state_mix = self.from9_config.assign_state(layouter, &state_mix)?;

        // IotaB13
        let state_mix = {
            let mut state = state_mix;

            state[0] =
                self.iota_config
                    .assign_round_b13(layouter, state[0].clone(), f_pos.clone())?;
            state
        };
        let mut out_state: Vec<AssignedCell<F, F>> = vec![];
        for (mix, non_mix) in izip!(state_mix, state_non_mix) {
            let out_lane = self.add.linear_combine_advices(
                layouter,
                vec![mix, non_mix],
                vec![f_pos.clone(), f_neg.clone()],
                None,
            )?;
            out_state.push(out_lane)
        }
        Ok(out_state.try_into().unwrap())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arith_helpers::*;
    use crate::common::{State, ROUND_CONSTANTS};
    use crate::keccak_arith::KeccakFArith;
    use crate::permutation::{add::AddConfig, iota::IotaConfig};
    use halo2_proofs::circuit::Layouter;
    use halo2_proofs::pairing::bn256::Fr as Fp;
    use halo2_proofs::plonk::{ConstraintSystem, Error};
    use halo2_proofs::{circuit::SimpleFloorPlanner, dev::MockProver, plonk::Circuit};
    use itertools::Itertools;
    use pretty_assertions::assert_eq;
    use std::convert::TryInto;

    #[test]
    fn test_mixing_gate() {
        #[derive(Default, Debug)]
        struct MyCircuit<F> {
            in_state: [F; 25],
            out_state: [F; 25],
            next_mixing: Option<[F; NEXT_INPUTS_LANES]>,
            // flag
            is_mixing: bool,
        }

        #[derive(Clone)]
        struct MyConfig<F> {
            mixing_conf: MixingConfig<F>,
            table: FromBase9TableConfig<F>,
            advices: [Column<Advice>; 3],
        }

        impl<F: Field> Circuit<F> for MyCircuit<F> {
            type Config = MyConfig<F>;
            type FloorPlanner = SimpleFloorPlanner;

            fn without_witnesses(&self) -> Self {
                Self::default()
            }

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                let table = FromBase9TableConfig::configure(meta);
                let base_info = table.get_base_info(false);
                let advices: [Column<Advice>; 3] = (0..3)
                    .map(|_| {
                        let col = meta.advice_column();
                        meta.enable_equality(col);
                        col
                    })
                    .collect_vec()
                    .try_into()
                    .unwrap();
                let fixed = meta.fixed_column();
                let add = AddConfig::configure(meta, advices, fixed);
                let iota_config = IotaConfig::configure(add.clone());
                let flag = FlagConfig::configure(meta, advices[0]);
                let from9_config = BaseConversionConfig::configure(
                    meta,
                    base_info,
                    advices[0..2].try_into().unwrap(),
                    &add,
                );

                MyConfig {
                    mixing_conf: MixingConfig::configure(
                        from9_config,
                        iota_config,
                        &add,
                        flag,
                        advices[0],
                    ),
                    table,
                    advices,
                }
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<F>,
            ) -> Result<(), Error> {
                // Load the table
                config.table.load(&mut layouter)?;

                let in_state = layouter.assign_region(
                    || "Mixing Wittnes assignment",
                    |mut region| {
                        // Witness `in_state`
                        let in_state: [AssignedCell<F, F>; 25] = {
                            let mut state: Vec<AssignedCell<F, F>> = Vec::with_capacity(25);
                            for (offset, val) in self.in_state.iter().enumerate() {
                                let cell = region.assign_advice(
                                    || "witness input state",
                                    config.advices[0],
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

                let out_state = config.mixing_conf.assign_state(
                    &mut layouter,
                    &in_state,
                    Some(self.is_mixing),
                    self.next_mixing.map_or([None; NEXT_INPUTS_LANES], |x| {
                        x.iter().map(|&x| Some(x)).collect_vec().try_into().unwrap()
                    }),
                )?;
                layouter.assign_region(
                    || "State check",
                    |mut region| {
                        for (lane, value) in out_state.iter().zip(self.out_state.iter()) {
                            region.constrain_constant(lane.cell(), value)?;
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

        let input2: State = [
            [2, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
        ];

        // Convert the input to base9 as the gadget already expects it like this
        // since it's always the output of IotaB9.
        let mut in_state = StateBigInt::from(input1);
        for (x, y) in (0..5).cartesian_product(0..5) {
            in_state[(x, y)] = convert_b2_to_b9(input1[x][y])
        }

        // Convert the next_input_b9 to base9 as it needs to be added to the
        // state in base9 too.
        let next_input = StateBigInt::from(input2);

        // Compute out mixing state (when flag = 1)
        let out_mixing_state = state_bigint_to_field(KeccakFArith::mixing(
            &in_state,
            Some(&input2),
            *ROUND_CONSTANTS.last().unwrap(),
        ));

        // Compute out non-mixing state (when flag = 0)
        let out_non_mixing_state = state_bigint_to_field(KeccakFArith::mixing(
            &in_state,
            None,
            *ROUND_CONSTANTS.last().unwrap(),
        ));

        // Add inputs in the correct format.
        let in_state = state_bigint_to_field(StateBigInt::from(input1));
        let next_mixing = Some(state_bigint_to_field(next_input));

        // With flag set to false, we don't mix. And so we should obtain Absorb
        // + base_conv + IotaB13 result
        {
            // With the correct input and output witnesses, the proof should
            // pass.
            let circuit = MyCircuit::<Fp> {
                in_state,
                out_state: out_mixing_state,
                next_mixing,
                is_mixing: true,
            };

            let prover = MockProver::<Fp>::run(17, &circuit, vec![]).unwrap();

            assert_eq!(prover.verify(), Ok(()));

            // With wrong input and/or output witnesses, the proof should fail
            // to be verified.
            let circuit = MyCircuit::<Fp> {
                in_state,
                out_state: out_non_mixing_state,
                next_mixing,
                is_mixing: true,
            };

            let prover = MockProver::<Fp>::run(17, &circuit, vec![]).unwrap();

            assert!(prover.verify().is_err());
        }

        // With flag set to `false`, we don't mix. And so we should obtain
        // IotaB9 application as result.
        {
            let circuit = MyCircuit::<Fp> {
                in_state,
                out_state: out_non_mixing_state,
                next_mixing: None,
                is_mixing: false,
            };

            let prover = MockProver::<Fp>::run(17, &circuit, vec![]).unwrap();

            assert_eq!(prover.verify(), Ok(()));

            // With wrong input and/or output witnesses, the proof should fail
            // to be verified.
            let circuit = MyCircuit::<Fp> {
                in_state,
                out_state: in_state,
                next_mixing,
                is_mixing: false,
            };

            let prover = MockProver::<Fp>::run(17, &circuit, vec![]).unwrap();

            assert!(prover.verify().is_err());
        }
    }
}
