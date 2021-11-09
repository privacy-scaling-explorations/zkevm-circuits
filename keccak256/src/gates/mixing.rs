use crate::{arith_helpers::*, gates::iota_b9};
use halo2::{
    circuit::Region,
    plonk::{
        Advice, Column, ConstraintSystem, Error, Expression, Expression,
        Instance, Selector, VirtualCells,
    },
    poly::Rotation,
};
use itertools::Itertools;
use pasta_curves::arithmetic::FieldExt;
use std::marker::PhantomData;

use super::{absorb::{ABSORB_NEXT_INPUTS, AbsorbConfig}, iota_b13::IotaB13Config, iota_b9::IotaB9Config};

#[derive(Clone, Debug)]
pub struct MixingConfig<F> {
    is_mixing: Expression<F>,
    iota_b9_config: IotaB9Config<F>,
    iota_b13_config: IotaB13Config<F>,
    absorb_config: AbsorbConfig<F>,
    pub(crate) state: [Column<Advice>; 25],
    _marker: PhantomData<F>,
}

impl<F: FieldExt> MixingConfig<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        state: [Column<Advice>; 25],
        is_mixing: impl FnOnce(&mut VirtualCells<'_, F>) -> Expression<F>,
        is_not_mixing_absorb: impl FnOnce(&mut VirtualCells<'_, F>) -> Expression<F>,
        is_not_mixing_iota_b13: impl FnOnce(&mut VirtualCells<'_, F>) -> Expression<F>,
        round_ctant_b9: Column<Advice>,
        round_constants_b9: Column<Instance>,
        round_ctant_b13: Column<Advice>,
        round_constants_b13: Column<Instance>,
    ) -> MixingConfig<F> {
        // We mix
        let iota_b9_config = IotaB9Config::configure(
            is_mixing,
            meta,
            state,
            round_ctant_b9,
            round_constants_b9,
        );

        // We don't mix
        let absorb_config = AbsorbConfig::configure(is_not_mixing, meta, state);

        let iota_b13_config = IotaB13Config::configure(q_mixing_b9);
        meta.create_gate("theta", |meta| unimplemented!());
    }

    pub fn assign_state(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        is_mixing: bool,
        state: [F; 25],
        next_mixing: Option<[F;ABSORB_NEXT_INPUTS],
    ) -> Result<[F; 25], Error> {
        self.q_enable.enable(region, offset)?;
        
        let (out_state, new_offset) = self.iota_b9_config.assign_state(region, offset, state);
        let (out_state, new_offset) = self.iota_b13_config.assign_state(region, offset, state);

        Ok(out_state)
    }
}
