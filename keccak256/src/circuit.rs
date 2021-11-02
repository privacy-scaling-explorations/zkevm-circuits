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
    plonk::{Advice, Column, ConstraintSystem, Error},
};
use itertools::Itertools;
use num_bigint::BigUint;
use pasta_curves::arithmetic::FieldExt;
use std::{convert::TryInto, marker::PhantomData};

#[derive(Clone, Debug)]
pub struct KeccakFConfig<F: FieldExt> {
    theta_config: ThetaConfig<F>,
    rho_config: RhoConfig<F>,
    pi_config: PiConfig<F>,
    xi_config: XiConfig<F>,
    iota_b9_config: IotaB9Config<F>,
    iota_b13_config: IotaB13Config<F>,
    absorb_config: AbsorbConfig<F>,
    state: [Column<Advice>; 25],
    _marker: PhantomData<F>,
}

impl<F: FieldExt> KeccakFConfig<F> {
    // We assume state is recieved in base-9.
    pub fn configure(
        &self,
        meta: &mut ConstraintSystem<F>,
    ) -> KeccakFConfig<F> {
        let state = (0..25)
            .map(|_| {
                let column = meta.advice_column();
                meta.enable_equality(column.into());
                column
            })
            .collect_vec()
            .try_into()
            .unwrap();

        // TMP for mixing
        let next_input = (0..ABSORB_NEXT_INPUTS)
            .map(|_| meta.advice_column())
            .collect_vec()
            .try_into()
            .unwrap();
        // theta
        let theta_config = ThetaConfig::configure(meta.selector(), meta, state);
        // rho
        let rho_config = RhoConfig::configure(meta.selector(), meta, state);
        // Pi
        let pi_config = PiConfig::configure(meta.selector(), meta, state);
        // xi
        let xi_config = XiConfig::configure(meta.selector(), meta, state);
        // Iotab9

        let iota_b9_config = {
            // Generate advice and instance column for Round constants in base9
            let round_ctant_b9 = meta.advice_column();
            let round_constants_b9 = meta.instance_column();
            IotaB9Config::configure(
                meta.selector(),
                meta,
                state,
                round_ctant_b9,
                round_constants_b9,
            )
        };

        // Just TMP until Mixing stage is done
        let iota_b13_config = {
            // Generate advice and instance column for Round constants in base13
            let round_ctant_b13 = meta.advice_column();
            let round_constants_b13 = meta.instance_column();
            IotaB13Config::configure(
                meta.selector(),
                meta,
                state,
                round_ctant_b13,
                round_constants_b13,
            )
        };

        // Absorb TMP
        let absorb_config =
            AbsorbConfig::configure(meta.selector(), meta, state, next_input);

        KeccakFConfig {
            theta_config,
            rho_config,
            pi_config,
            xi_config,
            iota_b9_config,
            iota_b13_config,
            absorb_config,
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
        // In case is needed
        let mut state = state;
        let mut offset = offset;

        // First 23 rounds
        for round in 0..24 {
            // State in base-13
            // theta
            state = {
                // Apply theta outside circuit
                let out_state = KeccakFArith::theta(&state_to_biguint(state));
                let out_state = state_bigint_to_pallas(out_state);
                // assignment
                self.theta_config
                    .assign_state(region, offset, state, out_state)?
            };

            offset += 1;

            // rho
            state = {
                // Apply rho outside circuit
                let out_state = KeccakFArith::rho(&state_to_biguint(state));
                let out_state = state_bigint_to_pallas(out_state);
                // assignment
                self.rho_config
                    .assign_state(region, offset, state, out_state)?
            };
            // Outputs in base-9 which is what Pi requires.
            offset += 1;

            // pi
            state = {
                // Apply pi outside circuit
                let out_state = KeccakFArith::pi(&state_to_biguint(state));
                let out_state = state_bigint_to_pallas(out_state);
                // assignment
                self.pi_config
                    .assign_state(region, offset, state, out_state)?
            };

            offset += 1;

            // xi
            state = {
                // Apply xi outside circuit
                let out_state = KeccakFArith::xi(&state_to_biguint(state));
                let out_state = state_bigint_to_pallas(out_state);
                // assignment
                self.xi_config
                    .assign_state(region, offset, state, out_state)?
            };

            offset += 1;

            // iota_b9
            state = {
                // Apply iota_b9 outside circuit
                let out_state = KeccakFArith::iota_b9(
                    &state_to_biguint(state),
                    ROUND_CONSTANTS[round],
                );
                let out_state = state_bigint_to_pallas(out_state);
                // assignment
                self.iota_b9_config
                    .assign_state(region, offset, state, out_state)?
            };
            // The resulting state is in Base-13 now. Which is what Theta requires again at the start of the loop.
            offset += 1;
        }
        let round = 24;
        // 24th round
        // State in base-13
        // theta
        state = {
            // Apply theta outside circuit
            let out_state = KeccakFArith::theta(&state_to_biguint(state));
            let out_state = state_bigint_to_pallas(out_state);
            // assignment
            self.theta_config
                .assign_state(region, offset, state, out_state)?
        };

        offset += 1;

        // rho
        state = {
            // Apply rho outside circuit
            let out_state = KeccakFArith::rho(&state_to_biguint(state));
            let out_state = state_bigint_to_pallas(out_state);
            // assignment
            self.rho_config
                .assign_state(region, offset, state, out_state)?
        };
        // Outputs in base-9 which is what Pi requires.
        offset += 1;

        // pi
        state = {
            // Apply pi outside circuit
            let out_state = KeccakFArith::pi(&state_to_biguint(state));
            let out_state = state_bigint_to_pallas(out_state);
            // assignment
            self.pi_config
                .assign_state(region, offset, state, out_state)?
        };

        offset += 1;

        // xi
        state = {
            // Apply xi outside circuit
            let out_state = KeccakFArith::xi(&state_to_biguint(state));
            let out_state = state_bigint_to_pallas(out_state);
            // assignment
            self.xi_config
                .assign_state(region, offset, state, out_state)?
        };

        offset += 1;

        // iota_b9
        state = {
            // Apply iota_b9 outside circuit
            let out_state = KeccakFArith::iota_b9(
                &state_to_biguint(state),
                ROUND_CONSTANTS[round],
            );
            let out_state = state_bigint_to_pallas(out_state);
            // assignment
            self.iota_b9_config
                .assign_state(region, offset, state, out_state)?
        };

        offset += 1;

        // Final round (if / else)
        // TODO!!!

        Ok(state)
    }
}

pub fn state_to_biguint<F: FieldExt>(state: [F; 25]) -> StateBigInt {
    StateBigInt {
        xy: state
            .iter()
            .map(|elem| elem.to_bytes())
            .map(|bytes| BigUint::from_bytes_le(&bytes))
            .collect(),
    }
}

pub fn state_bigint_to_pallas<F: FieldExt>(state: StateBigInt) -> [F; 25] {
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
