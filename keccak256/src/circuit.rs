use super::gates::{
    absorb::{AbsorbConfig, ABSORB_NEXT_INPUTS},
    iota_b13::IotaB13Config,
    iota_b9::IotaB9Config,
    pi::PiConfig,
    rho::RhoConfig,
    theta::ThetaConfig,
    xi::XiConfig,
};
use crate::keccak_arith::*;
use crate::{arith_helpers::*, common::ROUND_CONSTANTS};
use halo2::{
    circuit::Region,
    plonk::{
        Advice, Column, ConstraintSystem, Error, Expression, Instance, Selector,
    },
    poly::Rotation,
};
use itertools::Itertools;
use num_bigint::BigUint;
use pasta_curves::arithmetic::FieldExt;
use std::marker::PhantomData;

#[derive(Clone, Debug)]
pub struct KeccakFConfig<F: FieldExt> {
    q_enable_theta: Selector,
    theta_config: ThetaConfig<F>,
    q_enable_rho: Selector,
    rho_config: RhoConfig<F>,
    q_enable_pi: Selector,
    pi_config: PiConfig<F>,
    q_enable_xi: Selector,
    xi_config: XiConfig<F>,
    q_enable_iota_b9: Selector,
    iota_b9_config: IotaB9Config<F>,
    q_enable_iota_b13: Selector,
    iota_b13_config: IotaB13Config<F>,
    q_enable_absorb: Selector,
    absorb_config: AbsorbConfig<F>,
    state: [Column<Advice>; 25],
    _marker: PhantomData<F>,
}

impl<F: FieldExt> KeccakFConfig<F> {
    // We assume state is recieved in base-9.
    pub fn configure(
        q_enable: Selector,
        meta: &mut ConstraintSystem<F>,
        state: [Column<Advice>; 25],
    ) -> KeccakFConfig<F> {
        unimplemented!()
    }

    pub fn assign_state(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        state: [F; 25],
    ) -> Result<[F; 25], Error> {
        // In case is needed
        let old_state = state;
        let mut state = state;
        let mut offset = offset;

        // First 23 rounds
        for round in 0..24 {
            // State in base-13
            // theta
            state = {
                // assignment
                self.theta_config.assign_state(region, offset, state)?;
                // Apply theta outside circuit
                let state_after_theta =
                    KeccakFArith::theta(&state_to_biguint(state));
                state_bigint_to_pallas(state_after_theta)
            };

            offset += 1;

            // rho
            state = {
                // assignment
                self.rho_config.assign_state(region, offset, state)?;
                // Apply rho outside circuit
                let state_after_rho =
                    KeccakFArith::rho(&state_to_biguint(state));
                state_bigint_to_pallas(state_after_rho)
            };
            // Outputs in base-9 which is what Pi requires.

            // pi
            state = {
                // assignment
                self.pi_config.assign_state(region, offset, state)?;
                // Apply pi outside circuit
                let state_after_pi = KeccakFArith::pi(&state_to_biguint(state));
                state_bigint_to_pallas(state_after_pi)
            };

            // xi
            state = {
                // assignment
                self.xi_config.assign_state(region, offset, state)?;
                // Apply xi outside circuit
                let state_after_xi = KeccakFArith::xi(&state_to_biguint(state));
                state_bigint_to_pallas(state_after_xi)
            };

            // iota_b9
            state = {
                // assignment
                self.iota_b9_config.assign_state(region, offset, state)?;
                // Apply iota_b9 outside circuit
                let state_after_iota_b9 = KeccakFArith::iota_b9(
                    &state_to_biguint(state),
                    ROUND_CONSTANTS[round],
                );
                state_bigint_to_pallas(state_after_iota_b9)
            };
            // The resulting state is in Base-13 now. Which is what Theta requires again at the start of the loop.
        }
        let round = 24;
        // 24th round
        // State in base-13
        // theta
        state = {
            // assignment
            self.theta_config.assign_state(region, offset, state)?;
            // Apply theta outside circuit
            let state_after_theta =
                KeccakFArith::theta(&state_to_biguint(state));
            state_bigint_to_pallas(state_after_theta)
        };

        offset += 1;

        // rho
        state = {
            // assignment
            self.rho_config.assign_state(region, offset, state)?;
            // Apply rho outside circuit
            let state_after_rho = KeccakFArith::rho(&state_to_biguint(state));
            state_bigint_to_pallas(state_after_rho)
        };
        // Outputs in base-9 which is what Pi requires.

        // pi
        state = {
            // assignment
            self.pi_config.assign_state(region, offset, state)?;
            // Apply pi outside circuit
            let state_after_pi = KeccakFArith::pi(&state_to_biguint(state));
            state_bigint_to_pallas(state_after_pi)
        };

        // xi
        state = {
            // assignment
            self.xi_config.assign_state(region, offset, state)?;
            // Apply xi outside circuit
            let state_after_xi = KeccakFArith::xi(&state_to_biguint(state));
            state_bigint_to_pallas(state_after_xi)
        };

        // iota_b9
        state = {
            // assignment
            self.iota_b9_config.assign_state(region, offset, state)?;
            // Apply iota_b9 outside circuit
            let state_after_iota_b9 = KeccakFArith::iota_b9(
                &state_to_biguint(state),
                ROUND_CONSTANTS[round],
            );
            state_bigint_to_pallas(state_after_iota_b9)
        };

        // Final round (if / else)
        // TODO!!!

        Ok(state)
    }
}

fn state_to_biguint<F: FieldExt>(state: [F; 25]) -> StateBigInt {
    StateBigInt {
        xy: state
            .iter()
            .map(|elem| elem.to_bytes())
            .map(|bytes| BigUint::from_bytes_le(&bytes))
            .collect(),
    }
}

fn state_bigint_to_pallas<F: FieldExt>(state: StateBigInt) -> [F; 25] {
    let mut arr = [F::zero(); 25];
    let vector: Vec<F> = state
        .xy
        .iter()
        .map(|elem| {
            let mut array = [0u8; 32];
            let bytes = elem.to_bytes_le();
            array[0..32].copy_from_slice(&bytes[0..32]);
            array
        })
        .map(|bytes| F::from_bytes(&bytes).unwrap())
        .collect();
    arr[0..25].copy_from_slice(&vector[0..25]);
    arr
}
