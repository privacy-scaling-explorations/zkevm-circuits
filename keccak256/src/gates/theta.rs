use halo2::circuit::Layouter;
use halo2::{
    circuit::Region,
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Selector},
    poly::Rotation,
};
use itertools::Itertools;
use pasta_curves::arithmetic::FieldExt;
use std::marker::PhantomData;

#[derive(Clone, Debug)]
pub struct ThetaConfig<F> {
    q_enable: Selector,
    state: [Column<Advice>; 25],
    _marker: PhantomData<F>,
}

impl<F: FieldExt> ThetaConfig<F> {
    pub fn configure(
        q_enable: Selector,
        meta: &mut ConstraintSystem<F>,
        state: [Column<Advice>; 25],
    ) -> ThetaConfig<F> {
        meta.create_gate("theta", |meta| {
            let q_enable = meta.query_selector(q_enable);
            let column_sum: Vec<Expression<F>> = (0..5)
                .map(|x| {
                    let state_x0 =
                        meta.query_advice(state[5 * x], Rotation::cur());
                    let state_x1 =
                        meta.query_advice(state[5 * x + 1], Rotation::cur());
                    let state_x2 =
                        meta.query_advice(state[5 * x + 2], Rotation::cur());
                    let state_x3 =
                        meta.query_advice(state[5 * x + 3], Rotation::cur());
                    let state_x4 =
                        meta.query_advice(state[5 * x + 4], Rotation::cur());
                    state_x0 + state_x1 + state_x2 + state_x3 + state_x4
                })
                .collect::<Vec<_>>();

            (0..5)
                .cartesian_product(0..5)
                .map(|(x, y)| {
                    let new_state =
                        meta.query_advice(state[5 * x + y], Rotation::next());
                    let old_state =
                        meta.query_advice(state[5 * x + y], Rotation::cur());
                    let right = old_state
                        + column_sum[(x + 4) % 5].clone()
                        + Expression::Constant(F::from(13))
                            * column_sum[(x + 1) % 5].clone();
                    q_enable.clone() * (new_state - right)
                })
                .collect::<Vec<_>>()
        });

        ThetaConfig {
            q_enable,
            state,
            _marker: PhantomData,
        }
    }
    pub fn load(&self, _layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        Ok(())
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
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::common::*;
    use crate::keccak_arith::*;
    use halo2::circuit::Layouter;
    use halo2::plonk::{Advice, Column, ConstraintSystem, Error};
    use halo2::{
        circuit::SimpleFloorPlanner,
        dev::{MockProver, VerifyFailure},
        plonk::Circuit,
    };
    use itertools::Itertools;
    use num_bigint::BigUint;
    use pasta_curves::arithmetic::FieldExt;
    use pasta_curves::pallas;
    use std::convert::TryInto;
    use std::marker::PhantomData;

    #[test]
    fn test_theta_gates() {
        #[derive(Default)]
        struct MyCircuit<F> {
            in_state: [F; 25],
            out_state: [F; 25],
            _marker: PhantomData<F>,
        }
        impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
            type Config = ThetaConfig<F>;
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

                ThetaConfig::configure(q_enable, meta, state)
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<F>,
            ) -> Result<(), Error> {
                config.load(&mut layouter)?;

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
            [0, 0, 0, 9223372036854775808, 0],
            [0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
        ];
        let mut in_biguint = StateBigInt::default();
        let mut in_state: [pallas::Base; 25] = [pallas::Base::zero(); 25];

        for (x, y) in (0..5).cartesian_product(0..5) {
            in_biguint[(x, y)] = convert_b2_to_b13(input1[x][y]);
            in_state[5 * x + y] = big_uint_to_pallas(&in_biguint[(x, y)]);
        }
        let s1_arith = KeccakFArith::theta(&in_biguint);
        let mut out_state: [pallas::Base; 25] = [pallas::Base::zero(); 25];
        for (x, y) in (0..5).cartesian_product(0..5) {
            out_state[5 * x + y] = big_uint_to_pallas(&s1_arith[(x, y)]);
        }

        let circuit = MyCircuit::<pallas::Base> {
            in_state,
            out_state,
            _marker: PhantomData,
        };

        // Test without public inputs
        let prover =
            MockProver::<pallas::Base>::run(9, &circuit, vec![]).unwrap();

        assert_eq!(prover.verify(), Ok(()));

        let mut out_state2 = out_state;
        out_state2[0] = pallas::Base::from(5566u64);

        let circuit2 = MyCircuit::<pallas::Base> {
            in_state,
            out_state: out_state2,
            _marker: PhantomData,
        };

        let prover =
            MockProver::<pallas::Base>::run(9, &circuit2, vec![]).unwrap();
        assert_eq!(
            prover.verify(),
            Err(vec![VerifyFailure::ConstraintNotSatisfied {
                constraint: ((0, "theta").into(), 0, "").into(),
                row: 0
            }])
        );
    }
}
