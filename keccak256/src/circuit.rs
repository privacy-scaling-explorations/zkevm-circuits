use super::gates::{
    absorb::ABSORB_NEXT_INPUTS, iota_b9::IotaB9Config, pi::pi_gate_permutation,
    rho::RhoConfig, state_conversion::StateBaseConversion,
    tables::FromBase9TableConfig, theta::ThetaConfig, xi::XiConfig,
};
use crate::{
    arith_helpers::*,
    common::{PERMUTATION, ROUND_CONSTANTS},
    gates::rho_checks::RhoAdvices,
};
use crate::{gates::mixing::MixingConfig, keccak_arith::*};
use halo2::{
    circuit::{Cell, Layouter},
    plonk::{Advice, Column, ConstraintSystem, Error},
};
use itertools::Itertools;
use pairing::arithmetic::FieldExt;
use std::{convert::TryInto, marker::PhantomData};

#[derive(Clone, Debug)]
pub struct KeccakFConfig<F: FieldExt> {
    theta_config: ThetaConfig<F>,
    rho_config: RhoConfig<F>,
    xi_config: XiConfig<F>,
    iota_b9_config: IotaB9Config<F>,
    base_conversion_config: StateBaseConversion<F>,
    mixing_config: MixingConfig<F>,
    state: [Column<Advice>; 25],
    _base_conv_activator: Column<Advice>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> KeccakFConfig<F> {
    // We assume state is recieved in base-9.
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        table: FromBase9TableConfig<F>,
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

        // Allocate space for the Advice column that activates the base
        // conversion during the `PERMUTATION - 1` rounds.
        // let is_mixing_flag = meta.advice_column();
        // meta.enable_equality(is_mixing_flag.into());

        // theta
        let theta_config = ThetaConfig::configure(meta.selector(), meta, state);
        // rho
        let rho_config = {
            let cols: [Column<Advice>; 7] = state[0..7].try_into().unwrap();
            let adv = RhoAdvices::from(cols);
            let axiliary = [state[8], state[9]];

            let base13_to_9 = [
                meta.lookup_table_column(),
                meta.lookup_table_column(),
                meta.lookup_table_column(),
            ];
            let special =
                [meta.lookup_table_column(), meta.lookup_table_column()];
            RhoConfig::configure(
                meta,
                state,
                &adv,
                axiliary,
                base13_to_9,
                special,
            )
        };
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

        // Allocate space for the activation flag of the base_conversion.
        let _base_conv_activator = meta.advice_column();
        meta.enable_equality(_base_conv_activator.into());
        // Base conversion config.
        let base_info = table.get_base_info(false);
        let base_conversion_config = StateBaseConversion::configure(
            meta,
            state,
            base_info,
            _base_conv_activator,
        );

        let mixing_config = MixingConfig::configure(meta, table);

        KeccakFConfig {
            theta_config,
            rho_config,
            xi_config,
            iota_b9_config,
            base_conversion_config,
            mixing_config,
            state,
            _base_conv_activator,
            _marker: PhantomData,
        }
    }

    pub fn assign_all(
        &self,
        layouter: &mut impl Layouter<F>,
        in_state: [(Cell, F); 25],
        out_state: [F; 25],
        flag: (Cell, F),
        next_mixing: Option<[F; ABSORB_NEXT_INPUTS]>,
    ) -> Result<[(Cell, F); 25], Error> {
        let mut state = in_state;

        // First 23 rounds
        for round in 0..=PERMUTATION {
            // State in base-13
            // theta
            state = {
                // Apply theta outside circuit
                let out_state = KeccakFArith::theta(&state_to_biguint(
                    split_state_cells(state),
                ));
                let out_state = state_bigint_to_field(out_state);
                // assignment
                self.theta_config.assign_state(layouter, state, out_state)?
            };

            // rho
            state = {
                // Apply rho outside circuit
                let out_state: [F; 25] =
                    state_bigint_to_field(KeccakFArith::rho(
                        &state_to_biguint(split_state_cells(state)),
                    ));
                // Witness out_rho_state
                let out_rho_state = layouter.assign_region(
                    || "Wittnes & assignation",
                    |mut region| {
                        // Witness `state`
                        let in_state: [(Cell, F); 25] = {
                            let mut state: Vec<(Cell, F)> =
                                Vec::with_capacity(25);
                            for (idx, val) in out_state.iter().enumerate() {
                                let cell = region.assign_advice(
                                    || "witness input state",
                                    self.state[idx],
                                    0,
                                    || Ok(*val),
                                )?;
                                state.push((cell, *val))
                            }
                            state.try_into().unwrap()
                        };
                        Ok(in_state)
                    },
                )?;
                // assignment
                self.rho_config.assign_region(layouter, out_rho_state)?;
                out_rho_state
            };
            // Outputs in base-9 which is what Pi requires

            // Apply Pi permutation
            state = pi_gate_permutation(state);

            // xi
            state = {
                // Apply xi outside circuit
                let out_state = KeccakFArith::xi(&state_to_biguint(
                    split_state_cells(state),
                ));
                let out_state = state_bigint_to_field(out_state);
                // assignment
                self.xi_config.assign_state(layouter, state, out_state)?
            };

            // iota_b9
            state = {
                let out_state = KeccakFArith::iota_b9(
                    &state_to_biguint(split_state_cells(state)),
                    ROUND_CONSTANTS[round],
                );
                let out_state = state_bigint_to_field(out_state);
                self.iota_b9_config
                    .not_last_round(layouter, state, out_state, round)?
            };

            // The resulting state is in Base-9 now. We now convert it to
            // base_13 which is what Theta requires again at the
            // start of the loop.
            state = {
                // Witness 1 for the activation flag.
                let activation_flag = layouter.assign_region(
                    || "Witness activation_flag",
                    |mut region| {
                        let cell = region.assign_advice(
                            || "witness is_mixing flag",
                            self._base_conv_activator,
                            0,
                            || Ok(F::one()),
                        )?;
                        Ok((cell, F::one()))
                    },
                )?;

                self.base_conversion_config.assign_region(
                    layouter,
                    state,
                    activation_flag,
                )?
            }
        }

        // Mixing step
        let (_, _, absorb_out_state, _) = MixingConfig::compute_circ_states(
            state_to_state_bigint(split_state_cells(state)),
            if next_mixing.is_some() {
                Some(state_to_state_bigint(next_mixing.unwrap()))
            } else {
                None
            },
        );

        self.mixing_config.assign_state(
            layouter,
            state,
            out_state,
            absorb_out_state,
            flag,
            next_mixing,
            // Last round = PERMUTATION
            PERMUTATION,
        )
    }
}
