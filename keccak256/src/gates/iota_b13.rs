use halo2::plonk::Instance;
use halo2::{
    circuit::Region,
    plonk::{Advice, Column, ConstraintSystem, Error, Selector},
    poly::Rotation,
};
use pasta_curves::arithmetic::FieldExt;
use std::marker::PhantomData;

#[derive(Clone, Debug)]
pub struct IotaB13Config<F> {
    #[allow(dead_code)]
    q_enable: Selector,
    state: [Column<Advice>; 25],
    round_ctant_b13: Column<Advice>,
    round_constants: Column<Instance>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> IotaB13Config<F> {
    // We assume state is recieved in base-9.
    pub fn configure(
        q_enable: Selector,
        meta: &mut ConstraintSystem<F>,
        state: [Column<Advice>; 25],
        round_ctant_b13: Column<Advice>,
        round_constants: Column<Instance>,
    ) -> IotaB13Config<F> {
        meta.create_gate("iota_b13", |meta| {
            // def iota_b13(state: List[List[int], round_constant_base13: int):
            // state[0][0] += round_constant_base13
            // return state
            let state_00 = meta.query_advice(state[0], Rotation::cur())
                + meta.query_advice(round_ctant_b13, Rotation::cur());
            let next_lane = meta.query_advice(state[0], Rotation::next());
            vec![meta.query_selector(q_enable) * (state_00 - next_lane)]
        });
        IotaB13Config {
            q_enable,
            state,
            round_ctant_b13,
            round_constants,
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

    pub fn assign_round_ctant_b13(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        round_ctant: usize,
    ) -> Result<(), Error> {
        region.assign_advice_from_instance(
            || format!("assign round_ctant_b13 {}", 0),
            self.round_constants,
            round_ctant,
            self.round_ctant_b13,
            offset,
        )?;

        Ok(())
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
    fn test_iota_b13_gate() {
        #[derive(Default)]
        struct MyCircuit<F> {
            in_state: [F; 25],
            out_state: [F; 25],
            // This usize is indeed pointing the exact row of the
            // ROUND_CTANTS_B13 we want to use.
            round_ctant_b13: usize,
            _marker: PhantomData<F>,
        }
        impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
            type Config = IotaB13Config<F>;
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
                let round_ctant_b13 = meta.advice_column();
                let round_ctants = meta.instance_column();
                meta.enable_equality(round_ctant_b13.into());
                meta.enable_equality(round_ctants.into());
                IotaB13Config::configure(
                    q_enable,
                    meta,
                    state,
                    round_ctant_b13,
                    round_ctants,
                )
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<F>,
            ) -> Result<(), Error> {
                layouter.assign_region(
                    || "assign input & output state + constant in same region",
                    |mut region| {
                        let offset = 0;
                        config.q_enable.enable(&mut region, offset)?;
                        config.assign_state(
                            &mut region,
                            offset,
                            self.in_state,
                        )?;
                        let offset = 1;
                        config.assign_state(
                            &mut region,
                            offset,
                            self.out_state,
                        )?;
                        let offset = 0;
                        config.assign_round_ctant_b13(
                            &mut region,
                            offset,
                            self.round_ctant_b13,
                        )
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
            in_biguint[(x, y)] = convert_b2_to_b13(input1[x][y]);
            in_state[5 * x + y] = big_uint_to_pallas(&in_biguint[(x, y)]);
        }
        let s1_arith = KeccakFArith::iota_b13(&in_biguint, ROUND_CONSTANTS[0]);
        let mut out_state: [pallas::Base; 25] = [pallas::Base::zero(); 25];
        for (x, y) in (0..5).cartesian_product(0..5) {
            out_state[5 * x + y] = big_uint_to_pallas(&s1_arith[(x, y)]);
        }
        let circuit = MyCircuit::<pallas::Base> {
            in_state,
            out_state,
            round_ctant_b13: 0,
            _marker: PhantomData,
        };

        let constants = ROUND_CONSTANTS
            .iter()
            .map(|num| big_uint_to_pallas(&convert_b2_to_b13(*num)))
            .collect();
        // Test without public inputs
        let prover =
            MockProver::<pallas::Base>::run(9, &circuit, vec![constants])
                .unwrap();

        assert_eq!(prover.verify(), Ok(()));
    }
}
