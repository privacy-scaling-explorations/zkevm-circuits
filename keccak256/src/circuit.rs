use super::gates::{
    absorb::{AbsorbConfig, ABSORB_NEXT_INPUTS},
    iota_b13::IotaB13Config,
    iota_b9::IotaB9Config,
    pi::PiConfig,
    rho::RhoConfig,
    theta::ThetaConfig,
    xi::XiConfig,
};
use crate::{
    arith_helpers::*, common::{ROUND_CONSTANTS, PERMUTATION, ROTATION_CONSTANTS}, gates::rho_checks::RhoAdvices,
};
use crate::{gates::mixing::MixingConfig, keccak_arith::*};
use halo2::{
    circuit::Region,
    plonk::{Advice, Column, ConstraintSystem, Error, Selector},
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
    mixing_config: MixingConfig<F>,
    state: [Column<Advice>; 25],
    _marker: PhantomData<F>,
}

impl<F: FieldExt> KeccakFConfig<F> {
    const B9_ROW: usize = 0;
    const B13_ROW: usize = 1;

    // We assume state is recieved in base-9.
    pub fn configure(meta: &mut ConstraintSystem<F>) -> KeccakFConfig<F> {
        let state = (0..25)
            .map(|_| {
                let column = meta.advice_column();
                meta.enable_equality(column.into());
                column
            })
            .collect_vec()
            .try_into()
            .unwrap();

        // theta
        let theta_config = ThetaConfig::configure(meta.selector(), meta, state);
        // rho
        let rho_config = {
            let cols: [Column<Advice>; 7] = state[0..7].try_into().unwrap();
            let adv = RhoAdvices::from(cols);
            let axiliary = [state[8], state[9]];

            let base13_to_9 = [
                meta.fixed_column(),
                meta.fixed_column(),
                meta.fixed_column(),
            ];
            let special = [meta.fixed_column(), meta.fixed_column()];
            RhoConfig::configure(
                meta,
                state,
                &adv,
                axiliary,
                base13_to_9,
                special,
            )
        };
        // Pi
        let pi_config = PiConfig::configure(meta.selector(), meta, state);
        // xi
        let xi_config = XiConfig::configure(meta.selector(), meta, state);

        // Iotab9
        // Generate advice and instance column for Round constants in base9
        let round_ctant_b9 = meta.advice_column();
        let round_constants_b9 = meta.instance_column();
        let iota_b9_config = IotaB9Config::configure(
            meta,
            state,
            round_ctant_b9,
            round_constants_b9,
        );
        let not_mixing_b9_to_13 = StateConversion::configure(meta);


       
        let mixing_config = MixingConfig::configure(meta, state);
        // in side mixing  let b9_to_13 = StateConversion::configure(meta);


        KeccakFConfig {
            theta_config,
            rho_config,
            pi_config,
            xi_config,
            iota_b9_config,
            mixing_config,
            state,
            _marker: PhantomData,
        }
    }

    pub fn assign_all(
        &self,
        region: &mut Region<'_, F>,
        mut offset: usize,
        state: [F; 25],
        out_state: [F;25],
        flag: bool,
        next_mixing: Option<[F; ABSORB_NEXT_INPUTS]>,
        absolute_row_b9: usize,
        absolute_row_b13: usize,
    ) -> Result<[F; 25], Error> {
        // In case is needed
        let mut state = state;

        // First 23 rounds
        for round in 0..PERMUTATION {
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

            offset += ThetaConfig::OFFSET;

            // rho
            state = {
                // Apply rho outside circuit
                let out_state = KeccakFArith::rho(&state_to_biguint(state));
                let out_state = state_bigint_to_pallas(out_state);
                // assignment
                self.rho_config
                    .assign_region(region, offset, out_state)?;
                out_state
            };
            // Outputs in base-9 which is what Pi requires.
            offset += RhoConfig::OFFSET;

            // pi
            state = {
                // Apply pi outside circuit
                let out_state = KeccakFArith::pi(&state_to_biguint(state));
                let out_state = state_bigint_to_pallas(out_state);
                // assignment
                self.pi_config
                    .assign_state(region, offset, state, out_state)?
            };

            offset += PiConfig::OFFSET;

            // xi
            state = {
                // Apply xi outside circuit
                let out_state = KeccakFArith::xi(&state_to_biguint(state));
                let out_state = state_bigint_to_pallas(out_state);
                // assignment
                self.xi_config
                    .assign_state(region, offset, state, out_state)?
            };

            offset += XiConfig::OFFSET;

            // iota_b9
            state = {
            let out_state = KeccakFArith::iota_b9(&state_to_biguint(state), ROUND_CONSTANTS[round]);
            let out_state = state_bigint_to_pallas(out_state); 
            self
                .iota_b9_config
                .not_last_round(region, offset, state, out_state, round)?;
                out_state
            };
            offset += IotaB9Config::OFFSET;
            // The resulting state is in Base-13 now. Which is what Theta
            // requires again at the start of the loop.

            self.not_mixing_b9_to_13.not_last_round();
        }

        // Final round.
        let round = PERMUTATION;
        // PERMUTATION'th round
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

        offset += PiConfig::OFFSET;

        // xi
        state = {
            // Apply xi outside circuit
            let out_state = KeccakFArith::xi(&state_to_biguint(state));
            let out_state = state_bigint_to_pallas(out_state);
            // assignment
            self.xi_config
                .assign_state(region, offset, state, out_state)?
        };

        offset += XiConfig::OFFSET;

        // Mixing step
        state = {
            let out_state = KeccakFArith::mixing(&state_to_biguint(state), next_mixing, ROUND_CONSTANTS[round]);
            let out_state = state_bigint_to_pallas(out_state);
            self.mixing_config.assign_state(region, offset, state, out_state, flag, next_mixing, round, round)?;
            out_state
        };

        Ok(state)
    }
}
