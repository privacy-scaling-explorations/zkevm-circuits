use halo2::{
    circuit::Region,
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Selector},
    poly::Rotation,
};
use itertools::Itertools;
use pasta_curves::arithmetic::FieldExt;
use std::marker::PhantomData;

#[derive(Clone, Debug)]
pub struct XiConfig<F> {
    q_enable: Selector,
    state: [Column<Advice>; 25],
    _marker: PhantomData<F>,
}

impl<F: FieldExt> XiConfig<F> {
    // We assume state is recieved in base-9.
    pub fn configure(
        q_enable: Selector,
        meta: &mut ConstraintSystem<F>,
        state: [Column<Advice>; 25],
    ) -> XiConfig<F> {
        meta.create_gate("xi", |meta| {
            //  state in base 9, coefficient in 0~1
            //  def xi(state: List[List[int]]):
            //      new_state = [[0 for x in range(5)] for y in range(5)]
            //      # Xi step
            //      for x in range(5):
            //          for y in range(5):
            //              # a, b, c, d are base9, coefficient in 0~1
            //              a = state[x][y]
            //              b = state[(x + 1) % 5][y]
            //              c = state[(x + 2) % 5][y]
            //              # coefficient in 0~6
            //              new_state[x][y] = 2*a + b + 3*c
            //      return new_state
            (0..5)
                .cartesian_product(0..5usize)
                .map(|(x, y)| {
                    let a =
                        meta.query_advice(state[5 * x + y], Rotation::cur());
                    let b = meta.query_advice(
                        state[5 * ((x + 1) % 5) + y],
                        Rotation::cur(),
                    );
                    let c = meta.query_advice(
                        state[5 * ((x + 2) % 5) + y],
                        Rotation::cur(),
                    );
                    let next_lane =
                        meta.query_advice(state[5 * x + y], Rotation::next());
                    meta.query_selector(q_enable)
                        * ((Expression::Constant(F::from(2)) * a
                            + b
                            + Expression::Constant(F::from(3)) * c)
                            - next_lane)
                })
                .collect::<Vec<_>>()
        });

        XiConfig {
            q_enable,
            state,
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
    fn test_xi_gate() {
        #[derive(Default)]
        struct MyCircuit<F> {
            in_state: [F; 25],
            out_state: [F; 25],
            _marker: PhantomData<F>,
        }
        impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
            type Config = XiConfig<F>;
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

                XiConfig::configure(q_enable, meta, state)
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
        let mut in_biguint = StateBigInt::default();
        let mut in_state: [pallas::Base; 25] = [pallas::Base::zero(); 25];

        for (x, y) in (0..5).cartesian_product(0..5) {
            in_biguint[(x, y)] = convert_b2_to_b9(input1[x][y]);
            in_state[5 * x + y] = big_uint_to_pallas(&in_biguint[(x, y)]);
        }
        let s1_arith = KeccakFArith::xi(&in_biguint);
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
    }
}
