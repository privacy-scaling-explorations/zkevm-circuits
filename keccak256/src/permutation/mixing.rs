use super::tables::FromBase9TableConfig;
use super::{
    absorb::apply_absorb, add::AddConfig, base_conversion::BaseConversionConfig, iota::IotaConfig,
};
use crate::common::*;
use eth_types::Field;
use halo2_proofs::circuit::AssignedCell;
use halo2_proofs::plonk::{Expression, Selector};
use halo2_proofs::poly::Rotation;
use halo2_proofs::{
    circuit::Layouter,
    plonk::{Advice, Column, ConstraintSystem, Error},
};
use itertools::izip;
use std::convert::TryInto;

#[derive(Clone, Debug)]
pub struct MixingConfig<F> {
    iota_config: IotaConfig<F>,
    base_conv_config: BaseConversionConfig<F>,
    add: AddConfig<F>,
    state: [Column<Advice>; 25],
    flag: Column<Advice>,
    q_flag: Selector,
}

impl<F: Field> MixingConfig<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        table: &FromBase9TableConfig<F>,
        iota_config: IotaConfig<F>,
        add: &AddConfig<F>,
        state: [Column<Advice>; 25],
    ) -> Self {
        // Allocate space for the flag column from which we will copy to all of
        // the sub-configs.
        let flag = meta.advice_column();
        meta.enable_equality(flag);

        let q_flag = meta.selector();

        meta.create_gate("Ensure flag consistency", |meta| {
            let q_flag = meta.query_selector(q_flag);

            let negated_flag = meta.query_advice(flag, Rotation::next());
            let flag = meta.query_advice(flag, Rotation::cur());
            // We do a trick which consists on multiplying an internal selector
            // which is always active by the actual `negated_flag`
            // which will then enable or disable the gate.
            //
            // Force that `flag + negated_flag = 1`.
            // This ensures that flag = !negated_flag.
            let flag_consistency =
                (flag.clone() + negated_flag.clone()) - Expression::Constant(F::one());

            // Define bool constraint for flags.
            // Based on: `(1-flag) * flag = 0` only if `flag` is boolean.
            let bool_constraint = |flag: Expression<F>| -> Expression<F> {
                (Expression::Constant(F::one()) - flag.clone()) * flag
            };

            // Add a constraint that sums up the results of the two branches
            // constraining it to be equal to `out_state`.
            [
                q_flag.clone() * flag_consistency,
                q_flag.clone() * bool_constraint(flag),
                q_flag * bool_constraint(negated_flag),
            ]
        });

        let base_info = table.get_base_info(false);
        let base_conv_config =
            BaseConversionConfig::configure(meta, base_info, state[0..2].try_into().unwrap(), &add);

        Self {
            iota_config,
            base_conv_config,
            add: add.clone(),
            state,
            flag,
            q_flag,
        }
    }

    /// Enforce flag constraints
    pub fn enforce_flag_consistency(
        &self,
        layouter: &mut impl Layouter<F>,
        flag: Option<bool>,
    ) -> Result<(AssignedCell<F, F>, AssignedCell<F, F>), Error> {
        layouter.assign_region(
            || "Flag and Negated flag assignation",
            |mut region| {
                self.q_flag.enable(&mut region, 0)?;
                // Witness `is_mixing` flag
                let positive = region.assign_advice(
                    || "witness is_mixing",
                    self.flag,
                    0,
                    || {
                        flag.map(|flag| F::from(flag as u64))
                            .ok_or(Error::Synthesis)
                    },
                )?;

                // Witness negated `is_mixing` flag
                let negative = region.assign_advice(
                    || "witness negated is_mixing",
                    self.flag,
                    1,
                    || {
                        flag.map(|flag| F::from(!flag as u64))
                            .ok_or(Error::Synthesis)
                    },
                )?;

                Ok((positive, negative))
            },
        )
    }

    pub fn assign_state(
        &self,
        layouter: &mut impl Layouter<F>,
        in_state: &[AssignedCell<F, F>; 25],
        flag: Option<bool>,
        next_mixing: [Option<F>; NEXT_INPUTS_LANES],
    ) -> Result<[AssignedCell<F, F>; 25], Error> {
        // Enforce flag constraints and witness them.
        let (f_pos, f_neg) = self.enforce_flag_consistency(layouter, flag)?;

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
        let state_mix = apply_absorb(&self.add, layouter, self.state[0], in_state, &next_mixing)?;

        // Base conversion assign
        let state_mix = self.base_conv_config.assign_state(layouter, &state_mix)?;

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
        }

        impl<F: Field> Circuit<F> for MyCircuit<F> {
            type Config = MyConfig<F>;
            type FloorPlanner = SimpleFloorPlanner;

            fn without_witnesses(&self) -> Self {
                Self::default()
            }

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                let table = FromBase9TableConfig::configure(meta);

                let state: [Column<Advice>; 25] = (0..25)
                    .map(|_| {
                        let col = meta.advice_column();
                        meta.enable_equality(col);
                        col
                    })
                    .collect_vec()
                    .try_into()
                    .unwrap();
                let fixed = meta.fixed_column();
                let add = AddConfig::configure(meta, state[0..3].try_into().unwrap(), fixed);
                let iota_config = IotaConfig::configure(add.clone());

                MyConfig {
                    mixing_conf: MixingConfig::configure(meta, &table, iota_config, &add, state),
                    table,
                }
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<F>,
            ) -> Result<(), Error> {
                // Load the table
                config.table.load(&mut layouter)?;
                let offset: usize = 0;

                let in_state = layouter.assign_region(
                    || "Mixing Wittnes assignment",
                    |mut region| {
                        // Witness `in_state`
                        let in_state: [AssignedCell<F, F>; 25] = {
                            let mut state: Vec<AssignedCell<F, F>> = Vec::with_capacity(25);
                            for (idx, val) in self.in_state.iter().enumerate() {
                                let cell = region.assign_advice(
                                    || "witness input state",
                                    config.mixing_conf.state[idx],
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
