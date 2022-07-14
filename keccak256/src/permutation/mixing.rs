use super::super::arith_helpers::*;
use super::generic::GenericConfig;
use super::tables::{FromBase9TableConfig, StackableTable};
use super::{absorb::AbsorbConfig, base_conversion::BaseConversionConfig, iota::IotaConstants};
use crate::common::*;
use crate::keccak_arith::KeccakFArith;
use eth_types::Field;
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, Region},
    plonk::{Advice, Column, ConstraintSystem, Error, Selector},
    poly::Rotation,
};
use std::convert::TryInto;

#[derive(Clone, Debug)]
pub struct MixingConfig<F> {
    iota_constants: IotaConstants<F>,
    absorb_config: AbsorbConfig<F>,
    base_conv_config: BaseConversionConfig<F>,
    state: [Column<Advice>; 25],
    flag: Column<Advice>,
    q_out_copy: Selector,
    generic: GenericConfig<F>,
    stackable: StackableTable<F>,
}

impl<F: Field> MixingConfig<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        table: &FromBase9TableConfig<F>,
        state: [Column<Advice>; 25],
        generic: GenericConfig<F>,
        stackable: StackableTable<F>,
    ) -> MixingConfig<F> {
        let flag = meta.advice_column();
        meta.enable_equality(flag);
        // We mix -> Flag = true
        let absorb_config = AbsorbConfig::configure(meta, state);

        let base_info = table.get_base_info(false);
        let base_conv_lane = meta.advice_column();
        let base_conv_config = BaseConversionConfig::configure(
            meta,
            base_info,
            base_conv_lane,
            flag,
            state[0..5].try_into().unwrap(),
        );

        let q_out_copy = meta.selector();

        meta.create_gate("Mixing result copies and constraints", |meta| {
            let q_enable = meta.query_selector(q_out_copy);
            // Add out mixing states together multiplied by the mixing_flag.
            let negated_flag = meta.query_advice(flag, Rotation::next());
            let flag = meta.query_advice(flag, Rotation::cur());

            // Multiply by flag and negated_flag the out mixing results.
            let left_side = meta.query_advice(state[0], Rotation::cur()) * negated_flag;
            let right_side = meta.query_advice(state[0], Rotation::next()) * flag;
            let out_state = meta.query_advice(state[0], Rotation(2));

            // We add the results of the mixing gate if/else branches multiplied
            // by it's corresponding flags so that we always
            // copy from the same place on the copy_constraints while enforcing
            // the equality with the out_state of the permutation.
            [q_enable * ((left_side + right_side) - out_state)]
        });
        let iota_constants = IotaConstants::default();

        MixingConfig {
            iota_constants,
            absorb_config,
            base_conv_config,
            state,
            flag,
            q_out_copy,
            generic,
            stackable,
        }
    }

    /// Enforce flag constraints
    pub fn assign_out_mixing_states(
        &self,
        layouter: &mut impl Layouter<F>,
        flag_bool: bool,
        negated_flag: AssignedCell<F, F>,
        out_mixing_circ: &[AssignedCell<F, F>; 25],
        out_non_mixing_circ: &[AssignedCell<F, F>; 25],
        out_state: [F; 25],
    ) -> Result<[AssignedCell<F, F>; 25], Error> {
        layouter.assign_region(
            || "Out Mixing states assignation",
            |mut region| {
                // Enable selector
                self.q_out_copy.enable(&mut region, 0)?;

                // Copy constrain flags.
                let _flag_cell = region.assign_advice(
                    || "witness is_mixing",
                    self.flag,
                    0,
                    || Ok(F::from(flag_bool as u64)),
                )?;

                negated_flag.copy_advice(|| "witness is_mixing", &mut region, self.flag, 1)?;

                // Copy-constrain both out states.
                self.copy_state(&mut region, 0, self.state, out_non_mixing_circ)?;

                self.copy_state(&mut region, 1, self.state, out_mixing_circ)?;

                let out_state: [AssignedCell<F, F>; 25] = {
                    let mut out_vec: Vec<AssignedCell<F, F>> = vec![];
                    for (idx, lane) in out_state.iter().enumerate() {
                        let out_cell = region.assign_advice(
                            || format!("assign out_state [{}]", idx),
                            self.state[idx],
                            2,
                            || Ok(*lane),
                        )?;
                        out_vec.push(out_cell);
                    }
                    out_vec.try_into().unwrap()
                };

                Ok(out_state)
            },
        )
    }

    pub fn assign_state(
        &self,
        layouter: &mut impl Layouter<F>,
        in_state: &[AssignedCell<F, F>; 25],
        out_state: [F; 25],
        flag_bool: bool,
        next_mixing: Option<[F; NEXT_INPUTS_LANES]>,
    ) -> Result<[AssignedCell<F, F>; 25], Error> {
        // Enforce flag constraints and witness them.
        let (flag, negated_flag) = self
            .stackable
            .assign_boolean_flag(layouter, Some(flag_bool))?;

        // If we don't mix:
        // IotaB9
        let non_mix_res = {
            let mut state = in_state.clone();
            // If `no_mixing` is true: add `A4 * round_constant_b9`
            // Otherwise, do nothing and return the orignal lane value in the
            // next cell
            state[0] = self.generic.conditional_add_const(
                layouter,
                state[0].clone(),
                negated_flag.clone(),
                self.iota_constants.a4_times_round_constants_b9[PERMUTATION - 1],
            )?;
            state
        };

        // If we mix:
        // Absorb
        let (out_state_absorb_cells, _) = self.absorb_config.copy_state_flag_next_inputs(
            layouter,
            in_state,
            // Compute out_absorb state.
            state_bigint_to_field(KeccakFArith::absorb(
                &state_to_biguint(split_state_cells(in_state.clone())),
                &state_to_state_bigint::<F, NEXT_INPUTS_LANES>(next_mixing.unwrap_or_default()),
            )),
            next_mixing.unwrap_or_default(),
            flag.clone(),
        )?;

        // Base conversion assign
        let base_conv_cells =
            self.base_conv_config
                .assign_state(layouter, &out_state_absorb_cells, flag.clone())?;

        // IotaB13
        let mix_res = {
            let mut base_conv_cells = base_conv_cells;

            // If `mixing` is true: add round constant in base 13.
            // Otherwise, do nothing and return the orignal lane value in the
            // next cell
            base_conv_cells[0] = self.generic.conditional_add_const(
                layouter,
                base_conv_cells[0].clone(),
                flag,
                self.iota_constants.round_constant_b13,
            )?;
            base_conv_cells
        };

        self.assign_out_mixing_states(
            layouter,
            flag_bool,
            negated_flag,
            &mix_res,
            &non_mix_res,
            out_state,
        )
    }

    /// Copies the `[(Cell,F);25]` to the passed [Column<Advice>; 25].
    fn copy_state(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        columns: [Column<Advice>; 25],
        state: &[AssignedCell<F, F>; 25],
    ) -> Result<(), Error> {
        for (idx, state_cell) in state.iter().enumerate() {
            state_cell.copy_advice(
                || format!("Copy state {}", idx),
                region,
                columns[idx],
                offset,
            )?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::{State, ROUND_CONSTANTS};
    use halo2_proofs::{
        circuit::{Layouter, SimpleFloorPlanner},
        dev::MockProver,
        pairing::bn256::Fr as Fp,
        plonk::{Circuit, ConstraintSystem, Error, TableColumn},
    };
    use itertools::Itertools;
    use pretty_assertions::assert_eq;
    use std::convert::TryInto;

    #[test]
    fn test_mixing_gate() {
        #[derive(Default)]
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
            stackable: StackableTable<F>,
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
                let generic =
                    GenericConfig::configure(meta, state[0..3].try_into().unwrap(), fixed);
                let table_cols: [TableColumn; 3] = (0..3)
                    .map(|_| meta.lookup_table_column())
                    .collect_vec()
                    .try_into()
                    .unwrap();
                let stackable =
                    StackableTable::configure(meta, state[0..3].try_into().unwrap(), table_cols);
                let mixing_conf =
                    MixingConfig::configure(meta, &table, state, generic, stackable.clone());

                MyConfig {
                    mixing_conf,
                    table,
                    stackable,
                }
            }

            fn synthesize(
                &self,
                mut config: Self::Config,
                mut layouter: impl Layouter<F>,
            ) -> Result<(), Error> {
                // Load the table
                config.table.load(&mut layouter)?;
                config.stackable.load(&mut layouter)?;
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

                config.mixing_conf.assign_state(
                    &mut layouter,
                    &in_state,
                    self.out_state,
                    self.is_mixing,
                    self.next_mixing,
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
