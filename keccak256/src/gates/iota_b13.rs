use crate::common::ROUND_CONSTANTS;
use crate::{arith_helpers::*, keccak_arith::*};
use halo2::plonk::{Expression, Instance};
use halo2::{
    circuit::Region,
    plonk::{Advice, Column, ConstraintSystem, Error, VirtualCells},
    poly::Rotation,
};
use pairing::arithmetic::FieldExt;
use std::marker::PhantomData;

#[derive(Clone, Debug)]
pub struct IotaB13Config<F> {
    q_enable: Expression<F>,
    state: [Column<Advice>; 25],
    round_ctant_b13: Column<Advice>,
    round_constants: Column<Instance>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> IotaB13Config<F> {
    // We assume state is recieved in base-9.
    pub fn configure(
        q_enable_fn: impl FnOnce(&mut VirtualCells<'_, F>) -> Expression<F>,
        meta: &mut ConstraintSystem<F>,
        state: [Column<Advice>; 25],
        round_ctant_b13: Column<Advice>,
        round_constants: Column<Instance>,
    ) -> IotaB13Config<F> {
        let mut q_enable = Expression::Constant(F::zero());
        meta.create_gate("iota_b13", |meta| {
            // def iota_b13(state: List[List[int], round_constant_base13: int):
            // state[0][0] += round_constant_base13
            // return state
            q_enable = q_enable_fn(meta);
            let state_00 = meta.query_advice(state[0], Rotation::cur())
                + meta.query_advice(round_ctant_b13, Rotation::cur());
            let next_lane = meta.query_advice(state[0], Rotation::next());
            vec![q_enable * (state_00 - next_lane)]
        });
        IotaB13Config {
            q_enable,
            state,
            round_ctant_b13,
            round_constants,
            _marker: PhantomData,
        }
    }

    // We need to enable q_enable outside in parallel to the call to this!
    pub fn assign_state(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        state: [F; 25],
        round: usize,
    ) -> Result<([F; 25], usize), Error> {
        for (idx, lane) in state.iter().enumerate() {
            region.assign_advice(
                || format!("assign state {}", idx),
                self.state[idx],
                offset,
                || Ok(*lane),
            )?;
        }

        // Apply iota_b9 outside circuit
        let out_state = KeccakFArith::iota_b13(
            &state_to_biguint(state),
            ROUND_CONSTANTS[round],
        );
        let out_state = state_bigint_to_pallas(out_state);

        for (idx, lane) in out_state.iter().enumerate() {
            region.assign_advice(
                || format!("assign state {}", idx),
                self.state[idx],
                offset + 1,
                || Ok(*lane),
            )?;
        }
        Ok((out_state, offset + 1))
    }

    /// Assigns the ROUND_CONSTANTS_BASE_13to the `absolute_row` passed asn an
    /// absolute instance column.
    pub fn assign_round_ctant_b13(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        absolute_row: usize,
    ) -> Result<usize, Error> {
        region.assign_advice_from_instance(
            // `absolute_row` is the absolute offset in the overall Region
            // where the Column is laying.
            || format!("assign round_ctant_b13 {}", absolute_row),
            self.round_constants,
            absolute_row,
            self.round_ctant_b13,
            offset,
        )?;

        Ok(offset + ROUND_CONSTANTS.len())
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
    use halo2::{
        circuit::SimpleFloorPlanner,
        dev::MockProver,
        plonk::{Circuit, Selector},
    };
    use itertools::Itertools;
    use pasta_curves::arithmetic::FieldExt;
    use pasta_curves::pallas;
    use std::convert::TryInto;
    use std::marker::PhantomData;

    #[test]
    fn test_iota_b13_gate() {
        #[derive(Default)]
        struct MyCircuit<F> {
            in_state: [F; 25],
            // This usize is indeed pointing the exact row of the
            // ROUND_CTANTS_B13 we want to use.
            round_ctant_b13: usize,
            _marker: PhantomData<F>,
        }

        #[derive(Debug, Clone)]
        struct MyConfig<F> {
            q_enable: Selector,
            iota_b9_config: IotaB13Config<F>,
        }
        impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
            type Config = IotaB13Config<F>;
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
                let round_ctant_b13 = meta.advice_column();
                let round_ctants = meta.instance_column();
                meta.enable_equality(round_ctant_b13.into());
                meta.enable_equality(round_ctants.into());
                IotaB13Config::configure(
                    |meta| meta.query_selector(q_enable),
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
                        config.assign_state(
                            &mut region,
                            offset,
                            self.in_state,
                            0,
                        )?;
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

        let input1: State = [
            [1, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
        ];
        let mut in_biguint = StateBigInt::default();
        let mut in_state: [Fp; 25] = [Fp::zero(); 25];

        for (x, y) in (0..5).cartesian_product(0..5) {
            in_biguint[(x, y)] = convert_b2_to_b13(input1[x][y]);
            in_state[5 * x + y] = big_uint_to_pallas(&in_biguint[(x, y)]);
        }
        let s1_arith = KeccakFArith::iota_b13(&in_biguint, ROUND_CONSTANTS[0]);

        let circuit = MyCircuit::<pallas::Base> {
            in_state,
            round_ctant_b13: 0,
            _marker: PhantomData,
        };

        let constants = ROUND_CONSTANTS
            .iter()
            .map(|num| big_uint_to_pallas(&convert_b2_to_b13(*num)))
            .collect();
        // Test without public inputs
        let prover =
            MockProver::<Fp>::run(9, &circuit, vec![constants]).unwrap();

        assert_eq!(prover.verify(), Ok(()));
    }
}
