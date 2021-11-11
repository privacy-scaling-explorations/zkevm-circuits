use halo2::{
    circuit::{Cell, Region},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Instance},
    poly::Rotation,
};
use pasta_curves::arithmetic::FieldExt;

use super::{
    absorb::{AbsorbConfig, ABSORB_NEXT_INPUTS},
    iota_b13::IotaB13Config,
    iota_b9::IotaB9Config,
};

#[derive(Clone, Debug)]
pub struct MixingConfig<F> {
    iota_b9_config: IotaB9Config<F>,
    iota_b13_config: IotaB13Config<F>,
    absorb_config: AbsorbConfig<F>,
    pub(crate) state: [Column<Advice>; 25],
}

impl<F: FieldExt> MixingConfig<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        state: [Column<Advice>; 25],
        round_ctant_b9: Column<Advice>,
        round_constants_b9: Column<Instance>,
        round_ctant_b13: Column<Advice>,
        round_constants_b13: Column<Instance>,
    ) -> MixingConfig<F> {
        // We mix
        let iota_b9_config = IotaB9Config::configure(
            |meta| {
                Expression::Constant(F::one())
                    - meta.query_advice(round_ctant_b9, Rotation::next())
            },
            meta,
            state,
            round_ctant_b9,
            round_constants_b9,
        );
        // We don't mix
        let absorb_config = AbsorbConfig::configure(meta, state);
        let iota_b13_config = IotaB13Config::configure(
            meta,
            state,
            round_ctant_b13,
            round_constants_b13,
        );

        MixingConfig {
            iota_b9_config,
            iota_b13_config,
            absorb_config,
            state,
        }
    }

    pub fn assign_state(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        state: [(Cell, F); 25],
        next_mixing: Option<[F; ABSORB_NEXT_INPUTS]>,
        absolute_row_b9: usize,
        absolute_row_b13: usize,
        round: usize,
    ) -> Result<[F; 25], Error> {
        let flag = next_mixing.is_some();
        let (flag, new_offset) =
            self.iota_b9_config.copy_state_and_mixing_flag_and_rc(
                &mut region,
                offset,
                flag,
                state,
                absolute_row_b9,
                round,
            )?;

        let (out_state, new_offset) =
            self.absorb_config.assign_state_and_next_inp_from_cell(
                &mut region,
                new_offset,
                state,
                next_mixing.unwrap_or_default(),
                flag,
            )?;
        let (out_state, new_offset) =
            self.iota_b13_config.assign_state_and_round_ctant(
                &mut region,
                new_offset,
                out_state,
                round,
                absolute_row_b13,
                flag,
            )?;

        Ok(out_state)
    }
}
