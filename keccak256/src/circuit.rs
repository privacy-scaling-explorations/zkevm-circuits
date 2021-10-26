use super::gates::{
    absorb::{AbsorbConfig, ABSORB_NEXT_INPUTS},
    iota_b13::IotaB13Config,
    iota_b9::IotaB9Config,
    pi::PiConfig,
    rho::RhoConfig,
    theta::ThetaConfig,
    xi::XiConfig,
};
use crate::arith_helpers::*;
use crate::keccak_arith::*;
use halo2::{
    circuit::Region,
    plonk::{
        Advice, Column, ConstraintSystem, Error, Expression, Instance, Selector,
    },
    poly::Rotation,
};
use itertools::Itertools;
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
        let mut offset = offset;

        // First 23 rounds
        for round in 0..23 {
            // theta
            let state = {
                // assignment
                self.theta_config.assign_state(region, offset, state)?;
                // Apply theta outside circuit
                KeccakFArith::theta(state)
            };

            offset += 1;

            // rho
            let state = {
                // assignment
                self.rho_config.assign_state(region, offset, state)?;
                // Apply rho outside circuit
                rho(state)
            };
        }

        // 24th round

        // Final round (if / else)
        Ok(state)
    }
}
