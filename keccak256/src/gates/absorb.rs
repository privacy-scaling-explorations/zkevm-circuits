use halo2::{
    circuit::Region,
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Selector},
    poly::Rotation,
};
use pasta_curves::arithmetic::FieldExt;
use std::marker::PhantomData;

/// The number of next_inputs that are used inside the `absorb` circuit.
pub(crate) const ABSORB_NEXT_INPUTS: usize = 17;

#[derive(Clone, Debug)]
pub struct AbsorbConfig<F> {
    q_enable: Selector,
    state: [Column<Advice>; 25],
    next_input: [Column<Advice>; ABSORB_NEXT_INPUTS],
    _marker: PhantomData<F>,
}

impl<F: FieldExt> AbsorbConfig<F> {
    // We assume state is recieved in base-9.
    pub fn configure(
        q_enable: Selector,
        meta: &mut ConstraintSystem<F>,
        state: [Column<Advice>; 25],
        next_input: [Column<Advice>; ABSORB_NEXT_INPUTS],
    ) -> AbsorbConfig<F> {
        // def absorb(state: List[List[int], next_input: List[List[int]):
        //     for x in range(5):
        //         for y in range(5):
        //             # state[x][y] has 2*a + b + 3*c already, now add 2*d to make it 2*a + b + 3*c + 2*d
        //             # coefficient in 0~8
        //             state[x][y] += 2 * next_input[x][y]
        //     return state
        meta.create_gate("absorb", |meta| {
            (0..ABSORB_NEXT_INPUTS)
                .map(|idx| {
                    let val = meta.query_advice(state[idx], Rotation::cur())
                        + (Expression::Constant(F::from(2))
                            * meta.query_advice(
                                next_input[idx],
                                Rotation::cur(),
                            ));

                    let next_lane =
                        meta.query_advice(state[idx], Rotation::next());

                    meta.query_selector(q_enable) * (val - next_lane)
                })
                .collect::<Vec<_>>()
        });

        AbsorbConfig {
            q_enable,
            state,
            next_input,
            _marker: PhantomData,
        }
    }

    pub fn assign_state(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        state: [F; 25],
    ) -> Result<[F; 25], Error> {
        for (idx, lane) in state.iter().enumerate() {
            region.assign_advice(
                || format!("assign state {}", idx),
                self.state[idx],
                offset,
                || Ok(*lane),
            )?;
        }
        Ok(state)
    }

    pub fn assign_next_input(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        next_input: [F; ABSORB_NEXT_INPUTS],
    ) -> Result<[F; ABSORB_NEXT_INPUTS], Error> {
        for (idx, lane) in next_input.iter().enumerate() {
            region.assign_advice(
                || format!("assign next_input {}", idx),
                self.next_input[idx],
                offset,
                || Ok(*lane),
            )?;
        }
        Ok(next_input)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arith_helpers::*;
    use crate::common::*;
    use crate::keccak_arith::*;
    use halo2::circuit::Layouter;
    use halo2::plonk::{Advice, Column, ConstraintSystem, Error};
    use halo2::{circuit::SimpleFloorPlanner, dev::MockProver, plonk::Circuit};
    use itertools::Itertools;
    use num_bigint::BigUint;
    use pasta_curves::arithmetic::FieldExt;
    use pasta_curves::pallas;
    use std::convert::TryInto;
    use std::marker::PhantomData;

    #[test]
    fn test_absorb_gate() {
        #[derive(Default)]
        struct MyCircuit<F> {
            in_state: [F; 25],
            next_input: [F; ABSORB_NEXT_INPUTS],
            out_state: [F; 25],
            _marker: PhantomData<F>,
        }
        impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
            type Config = AbsorbConfig<F>;
            type FloorPlanner = SimpleFloorPlanner;

            fn without_witnesses(&self) -> Self {
                Self::default()
            }

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                let q_enable = meta.selector();

                let state: [Column<Advice>; 25] = (0..25)
                    .map(|_| meta.advice_column())
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap();

                let next_input: [Column<Advice>; ABSORB_NEXT_INPUTS] = (0
                    ..ABSORB_NEXT_INPUTS)
                    .map(|_| meta.advice_column())
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap();

                AbsorbConfig::configure(q_enable, meta, state, next_input)
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<F>,
            ) -> Result<(), Error> {
                layouter.assign_region(
                    || "assign input state",
                    |mut region| {
                        let offset = 0;
                        config.q_enable.enable(&mut region, offset)?;
                        config.assign_state(
                            &mut region,
                            offset,
                            self.in_state,
                        )?;
                        config.assign_next_input(
                            &mut region,
                            offset,
                            self.next_input,
                        )?;
                        let offset = 1;
                        config.assign_state(&mut region, offset, self.out_state)
                    },
                )?;

                Ok(())
            }
        }
        fn big_uint_to_pallas(a: &BigUint) -> pallas::Base {
            let mut b: [u64; 4] = [0; 4];
            let mut iter = a.iter_u64_digits();

            for i in &mut b {
                *i = match &iter.next() {
                    Some(x) => *x,
                    None => 0u64,
                };
            }

            pallas::Base::from_raw(b)
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

        let mut in_state: [pallas::Base; 25] = [pallas::Base::zero(); 25];
        let mut in_next_input_25: [pallas::Base; 25] =
            [pallas::Base::zero(); 25];

        for (x, y) in (0..5).cartesian_product(0..5) {
            in_biguint[(x, y)] = convert_b2_to_b9(input1[x][y]);
            next_biguint[(x, y)] = convert_b2_to_b9(next_input[x][y]);
            in_state[5 * x + y] = big_uint_to_pallas(&in_biguint[(x, y)]);
            in_next_input_25[5 * x + y] =
                big_uint_to_pallas(&next_biguint[(x, y)]);
        }

        let mut in_next_input_17 = [pallas::Base::zero(); ABSORB_NEXT_INPUTS];
        in_next_input_17
            .copy_from_slice(&in_next_input_25[0..ABSORB_NEXT_INPUTS]);
        let s1_arith = KeccakFArith::absorb(&in_biguint, &next_input);
        let mut out_state: [pallas::Base; 25] = [pallas::Base::zero(); 25];
        for (x, y) in (0..5).cartesian_product(0..5) {
            out_state[5 * x + y] = big_uint_to_pallas(&s1_arith[(x, y)]);
        }
        let circuit = MyCircuit::<pallas::Base> {
            in_state,
            next_input: in_next_input_17,
            out_state,
            _marker: PhantomData,
        };

        // Test without public inputs
        let prover =
            MockProver::<pallas::Base>::run(9, &circuit, vec![]).unwrap();

        assert_eq!(prover.verify(), Ok(()));
    }
}
