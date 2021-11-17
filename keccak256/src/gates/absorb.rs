use crate::{arith_helpers::*, keccak_arith::*};
use halo2::{
    circuit::{layouter::RegionLayouter, Cell, Region},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Selector},
    poly::Rotation,
};
use pairing::arithmetic::FieldExt;
use std::marker::PhantomData;

/// The number of next_inputs that are used inside the `absorb` circuit.
pub(crate) const ABSORB_NEXT_INPUTS: usize = 17;

#[derive(Clone, Debug)]
pub struct AbsorbConfig<F> {
    state: [Column<Advice>; 25],
    _marker: PhantomData<F>,
}

impl<F: FieldExt> AbsorbConfig<F> {
    // We assume state is recieved in base-9.
    // Rows are assigned as:
    // 1) STATE (25 columns) (offset +2)
    // 2) NEXT_INPUTS (17 columns) + is_mixing flag (1 column) (offset +1)
    // (current rotation) 3) OUT_STATE (25 columns) (offset +2)
    // TODO: Review with YT!
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        state: [Column<Advice>; 25],
    ) -> AbsorbConfig<F> {
        // def absorb(state: List[List[int], next_input: List[List[int]):
        //     for x in range(5):
        //         for y in range(5):
        //             # state[x][y] has 2*a + b + 3*c already, now add 2*d to
        // make it 2*a + b + 3*c + 2*d             # coefficient in 0~8
        //             state[x][y] += 2 * next_input[x][y]
        //     return state
        meta.create_gate("absorb", |meta| {
            // Query is_mixing flag and multiply it at each round as the
            // selector!
            let is_mixing = meta
                .query_advice(state[ABSORB_NEXT_INPUTS + 1], Rotation::cur());
            (0..ABSORB_NEXT_INPUTS)
                .map(|idx| {
                    let val = meta.query_advice(state[idx], Rotation::prev())
                        + (Expression::Constant(F::from(2))
                            * meta.query_advice(state[idx], Rotation::cur()));

                    let next_lane =
                        meta.query_advice(state[idx], Rotation::next());

                    is_mixing * (val - next_lane)
                })
                .collect::<Vec<_>>()
        });

        AbsorbConfig {
            state,
            _marker: PhantomData,
        }
    }

    // TODO: Review with YT!
    pub fn assign_state_and_next_inp_from_cell(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        state: [(Cell, F); 25],
        next_input: [F; ABSORB_NEXT_INPUTS],
        flag: (Cell, F),
    ) -> Result<([F; 25], usize), Error> {
        let mut state_array = [F::zero(); 25];

        // State at offset + 0
        for (idx, (cell, value)) in state.iter().enumerate() {
            // Copy value into state_array
            state_array[idx] = *value;
            let new_cell = region.assign_advice(
                || format!("assign state {}", idx),
                self.state[idx],
                offset,
                || Ok(*value),
            )?;

            region.constrain_equal(*cell, new_cell)?;
        }

        // Assign next_mixing at offset + 1
        for (idx, lane) in next_input.iter().enumerate() {
            region.assign_advice(
                || format!("assign next_input {}", idx),
                self.state[idx],
                offset + 1,
                || Ok(*lane),
            )?;
        }
        // Assign flag at last column(18th) of the offset + 1 row.
        let obtained_cell = region.assign_advice(
            || format!("assign next_input {}", ABSORB_NEXT_INPUTS + 1),
            self.state[ABSORB_NEXT_INPUTS + 1],
            offset + 1,
            || Ok(flag.1),
        )?;
        region.constrain_equal(flag.0, obtained_cell)?;

        // Apply absorb outside circuit
        let out_state = KeccakFArith::absorb(
            &state_to_biguint(state_array),
            &state_to_state_bigint(next_input),
        );
        let out_state = state_bigint_to_pallas(out_state);

        // Assign out_state at offset + 2
        for (idx, lane) in out_state.iter().enumerate() {
            region.assign_advice(
                || format!("assign state {}", idx),
                self.state[idx],
                offset + 2,
                || Ok(*lane),
            )?;
        }

        Ok((out_state, offset + 2))
    }

    // TODO: Review with YT!
    pub fn assign_state_next_inp_and_flag(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        state: [F; 25],
        next_input: [F; ABSORB_NEXT_INPUTS],
        flag: bool,
    ) -> Result<([F; 25], usize), Error> {
        // Assign current state at offset + 0
        for (idx, lane) in state.iter().enumerate() {
            region.assign_advice(
                || format!("assign state {}", idx),
                self.state[idx],
                offset,
                || Ok(*lane),
            )?;
        }

        // Assign next_mixing at offset + 1
        for (idx, lane) in next_input.iter().enumerate() {
            region.assign_advice(
                || format!("assign next_input {}", idx),
                self.state[idx],
                offset + 1,
                || Ok(*lane),
            )?;
        }
        // Assign flag at last column of the offset + 1 row.
        let flag: F = flag.into();
        region.assign_advice(
            || format!("assign next_input {}", ABSORB_NEXT_INPUTS + 1),
            self.state[ABSORB_NEXT_INPUTS + 1],
            offset + 1,
            || Ok(flag),
        )?;

        // Apply absorb outside circuit
        let out_state = KeccakFArith::absorb(
            &state_to_biguint(state),
            &state_to_state_bigint(next_input),
        );
        let out_state = state_bigint_to_pallas(out_state);

        // Assign out_state at offset + 2
        for (idx, lane) in out_state.iter().enumerate() {
            region.assign_advice(
                || format!("assign state {}", idx),
                self.state[idx],
                offset + 2,
                || Ok(*lane),
            )?;
        }

        Ok((out_state, offset + 2))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::*;
    use halo2::circuit::Layouter;
    use halo2::plonk::{Advice, Column, ConstraintSystem, Error};
    use halo2::{circuit::SimpleFloorPlanner, dev::MockProver, plonk::Circuit};
    use itertools::Itertools;
    use pasta_curves::arithmetic::FieldExt;
    use pasta_curves::pallas;
    use std::convert::TryInto;
    use std::marker::PhantomData;

    #[test]
    fn test_absorb_gate() {
        #[derive(Default)]
        struct MyCircuit<F> {
            // TODO: Review with YT the idea of state being already [(Cell,
            // F;25)] since will always come from copied cells.
            in_state: [F; 25],
            next_input: [F; ABSORB_NEXT_INPUTS],
            is_mixing: bool,
            _marker: PhantomData<F>,
        }
        impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
            type Config = AbsorbConfig<F>;
            type FloorPlanner = SimpleFloorPlanner;

            fn without_witnesses(&self) -> Self {
                Self::default()
            }

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                let q_enable = meta.complex_selector();

                let state: [Column<Advice>; 25] = (0..25)
                    .map(|_| meta.advice_column())
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap();

                AbsorbConfig::configure(meta, state)
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<F>,
            ) -> Result<(), Error> {
                let val: F = self.is_mixing.into();
                let flag: (Cell, F) = layouter.assign_region(
                    || "witness_is_mixing_flag",
                    |mut region| {
                        let offset = 1;
                        let cell = region.assign_advice(
                            || "assign is_mising",
                            config.state[ABSORB_NEXT_INPUTS + 1],
                            offset,
                            || Ok(val),
                        )?;
                        Ok((cell, val))
                    },
                )?;

                // Witness `in_state`.
                let in_state: [(Cell, F); 25] = layouter.assign_region(
                    || "Witness input state",
                    |mut region| {
                        let mut state: Vec<(Cell, F)> = Vec::with_capacity(25);
                        for (idx, val) in self.in_state.iter().enumerate() {
                            let cell = region.assign_advice(
                                || "witness input state",
                                config.state[idx],
                                0,
                                || Ok(*val),
                            )?;
                            state.push((cell, *val))
                        }

                        Ok(state.try_into().unwrap())
                    },
                )?;

                layouter.assign_region(
                    || "assign input state",
                    |mut region| {
                        let offset = 0;
                        config.assign_state_and_next_inp_from_cell(
                            &mut region,
                            offset,
                            in_state,
                            self.next_input,
                            flag,
                        )
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

        let next_input: State = [
            [2, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
        ];

        let mut in_biguint = StateBigInt::default();
        let mut next_biguint = StateBigInt::default();

        let mut in_state: [Fp; 25] = [Fp::zero(); 25];
        let mut in_next_input_25: [Fp; 25] = [Fp::zero(); 25];

        for (x, y) in (0..5).cartesian_product(0..5) {
            in_biguint[(x, y)] = convert_b2_to_b9(input1[x][y]);
            next_biguint[(x, y)] = convert_b2_to_b9(next_input[x][y]);
            in_state[5 * x + y] = big_uint_to_pallas(&in_biguint[(x, y)]);
            in_next_input_25[5 * x + y] =
                big_uint_to_pallas(&next_biguint[(x, y)]);
        }

        let mut in_next_input_17 = [Fp::zero(); ABSORB_NEXT_INPUTS];
        in_next_input_17
            .copy_from_slice(&in_next_input_25[0..ABSORB_NEXT_INPUTS]);
        let s1_arith = KeccakFArith::absorb(&in_biguint, &next_input);

        let circuit = MyCircuit::<pallas::Base> {
            is_mixing: false,
            in_state,
            next_input: in_next_input_17,
            _marker: PhantomData,
        };

        // Test without public inputs
        let prover = MockProver::<Fp>::run(9, &circuit, vec![]).unwrap();

        assert_eq!(prover.verify(), Ok(()));
    }
}
