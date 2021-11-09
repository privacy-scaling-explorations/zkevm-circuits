use halo2::circuit::Cell;
use halo2::plonk::Instance;
use halo2::{
    circuit::Region,
    plonk::{
        Advice, Column, ConstraintSystem, Error, Expression, VirtualCells,
    },
    poly::Rotation,
};
use pairing::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::common::ROUND_CONSTANTS;

#[derive(Clone, Debug)]
pub struct IotaB9Config<F> {
    q_enable: Expression<F>,
    state: [Column<Advice>; 25],
    pub(crate) round_ctant_b9: Column<Advice>,
    pub(crate) round_constants: Column<Instance>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> IotaB9Config<F> {
    // We assume state is recieved in base-9.
    pub fn configure(
        q_enable_fn: impl FnOnce(&mut VirtualCells<'_, F>) -> Expression<F>,
        meta: &mut ConstraintSystem<F>,
        state: [Column<Advice>; 25],
        round_ctant_b9: Column<Advice>,
        round_constants: Column<Instance>,
    ) -> IotaB9Config<F> {
        let mut q_enable = Expression::Constant(F::zero());
        // Enable copy constraints over PI and the Advices.
        meta.enable_equality(round_ctant_b9.into());
        meta.enable_equality(round_constants.into());
        meta.create_gate("iota_b9", |meta| {
            // def iota_b9(state: List[List[int], round_constant_base9: int):
            //     d = round_constant_base9
            //     # state[0][0] has 2*a + b + 3*c already, now add 2*d to make
            // it 2*a + b + 3*c + 2*d     # coefficient in 0~8
            //     state[0][0] += 2*d
            //     return state
            q_enable = q_enable_fn(meta);
            let state_00 = meta.query_advice(state[0], Rotation::cur())
                + (Expression::Constant(F::from(2))
                    * meta.query_advice(round_ctant_b9, Rotation::cur()));
            let next_lane = meta.query_advice(state[0], Rotation::next());
            vec![q_enable * (state_00 - next_lane)]
        });
        IotaB9Config {
            q_enable,
            state,
            round_ctant_b9,
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
    ) -> Result<([F; 25], usize), Error> {
        for (idx, lane) in state.iter().enumerate() {
            region.assign_advice(
                || format!("assign state {}", idx),
                self.state[idx],
                offset,
                || Ok(*lane),
            )?;
        }

        // TODO: Compute out state
        Ok(out_state)
    }

    // We need to enable q_enable outside in parallel to the call to this!
    pub fn assign_state_from_cells(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        state: [(Cell, F); 25],
    ) -> Result<([F; 25], usize), Error> {
        for (idx, (cell, value)) in state.iter().enumerate() {
            let new_cell = region.assign_advice(
                || format!("assign state {}", idx),
                self.state[idx],
                offset,
                || Ok(*value),
            )?;

            region.constrain_equal(*cell, new_cell)?;
        }

        // TODO! COMPUTE OUT STATE
        Ok(out_state)
    }

    /// Assigns the ROUND_CONSTANTS_BASE_9 to the `absolute_row` passed asn an
    /// absolute instance column. Returns the new offset after the
    /// assigment.
    pub fn assign_round_ctant_b9(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        absolute_row: usize,
    ) -> Result<usize, Error> {
        region.assign_advice_from_instance(
            // `absolute_row` is the absolute offset in the overall Region
            // where the Column is laying.
            || format!("assign round_ctant_b9 {}", absolute_row),
            self.round_constants,
            absolute_row,
            self.round_ctant_b9,
            offset,
        )?;

        Ok(offset + 1)
    }

    pub fn assing_mixing_flag(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        absolute_row: usize,
        flag: bool,
    ) -> Result<usize, Error> {
        // Assign to the 25th column the flag that determinates if we have a
        // mixing or a non-mixing step.
        region.assign_advice_from_instance(
            || format!("assign mixing bool flag{}", flag),
            self.round_constants,
            absolute_row,
            self.round_ctant_b9,
            offset,
        )?;

        Ok(offset + 1)
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
    fn test_iota_b9_gate() {
        #[derive(Default)]
        struct MyCircuit<F> {
            in_state: [F; 25],
            out_state: [F; 25],
            // This usize is indeed pointing the exact row of the
            // ROUND_CTANTS_B9 we want to use.
            round_ctant_b9: usize,
            _marker: PhantomData<F>,
        }

        #[derive(Debug, Clone)]
        struct MyConfig<F> {
            q_enable: Selector,
            iota_b9_config: IotaB9Config<F>,
        }
        impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
            type Config = MyConfig<F>;
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
                let round_ctant_b9 = meta.advice_column();
                // Allocate space for the round constants in base-9 which is an
                // instance column
                let round_ctants = meta.instance_column();
                let iota_b9_config = IotaB9Config::configure(
                    |meta| meta.query_selector(q_enable),
                    meta,
                    state,
                    round_ctant_b9,
                    round_ctants,
                );

                MyConfig {
                    q_enable,
                    iota_b9_config,
                }
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
                        config.iota_b9_config.assign_state(
                            &mut region,
                            offset,
                            self.in_state,
                        )?;
                        // Within the Region itself, we use the constant in the
                        // same offset so at position
                        // (Rotation::curr()). Therefore we use `0` here.
                        config.iota_b9_config.assign_round_ctant_b9(
                            &mut region,
                            offset,
                            self.round_ctant_b9,
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
            in_biguint[(x, y)] = convert_b2_to_b9(input1[x][y]);
            in_state[5 * x + y] = big_uint_to_pallas(&in_biguint[(x, y)]);
        }
        let s1_arith = KeccakFArith::iota_b9(&in_biguint, ROUND_CONSTANTS[0]);
        let mut out_state: [Fp; 25] = [Fp::zero(); 25];
        for (x, y) in (0..5).cartesian_product(0..5) {
            out_state[5 * x + y] = big_uint_to_pallas(&s1_arith[(x, y)]);
        }
        let circuit = MyCircuit::<Fp> {
            in_state,
            out_state,
            round_ctant_b9: 0,
            _marker: PhantomData,
        };

        let constants = ROUND_CONSTANTS
            .iter()
            .map(|num| big_uint_to_pallas(&convert_b2_to_b9(*num)))
            .collect();
        // Test without public inputs
        let prover =
            MockProver::<Fp>::run(9, &circuit, vec![constants]).unwrap();

        assert_eq!(prover.verify(), Ok(()));
    }
}
