use halo2::{
    circuit::Layouter,
    plonk::{Advice, Column, ConstraintSystem, Error},
};

use crate::gates::base_conversion::BaseConversionConfig;
use crate::gates::tables::FromBinaryTableConfig;
use pairing::arithmetic::FieldExt;
use std::convert::TryInto;

struct FromBinaryState<F> {
    table: FromBinaryTableConfig<F>,
    bccs: [BaseConversionConfig<F>; 25],
    state: [Column<Advice>; 25],
    output_b9: bool,
}

impl<F: FieldExt> FromBinaryState<F> {
    fn configure(
        meta: &mut ConstraintSystem<F>,
        state: [Column<Advice>; 25],
        table: FromBinaryTableConfig<F>,
        output_b9: bool,
    ) -> Self {
        let bi = table.get_base_info(output_b9);
        let bccs: [BaseConversionConfig<F>; 25] = state
            .iter()
            .map(|&lane| {
                BaseConversionConfig::configure(meta, bi.clone(), lane)
            })
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        Self {
            table,
            bccs,
            state,
            output_b9,
        }
    }

    pub fn assign_region(
        &self,
        layouter: &mut impl Layouter<F>,
        input_state: [F; 25],
    ) -> Result<[F; 25], Error> {
        let output_state: Result<Vec<F>, Error> = input_state
            .iter()
            .zip(self.bccs.iter())
            .map(|(&lane, config)| {
                let output = config.assign_region(layouter, lane)?;
                Ok(output)
            })
            .into_iter()
            .collect();
        let output_state = output_state?;
        let output_state: [F; 25] = output_state.try_into().unwrap();
        Ok(output_state)
    }
}
