use super::mpt_updates::MptUpdates;
use crate::evm_circuit::table::CallContextFieldTag;
use eth_types::Field;
use halo2_proofs::{
    circuit::Layouter,
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed, VirtualCells},
    poly::Rotation,
};
use std::marker::PhantomData;
use strum::IntoEnumIterator;

#[derive(Clone, Copy)]
pub struct Config {
    // Can these be TableColumn's?
    // https://github.com/zcash/halo2/blob/642efc1536d3ea2566b04814bd60a00c4745ae22/halo2_proofs/src/plonk/circuit.rs#L266
    pub u8: Column<Fixed>,
    pub u10: Column<Fixed>,
    pub u16: Column<Fixed>,
    pub call_context_field_tag: Column<Fixed>,
    // TODO: move this into mpt_updates and rename this to fixed_lookups.
    pub mpt_update: Column<Advice>,
}

#[derive(Clone)]
pub struct Queries<F> {
    pub u8: Expression<F>,
    pub u10: Expression<F>,
    pub u16: Expression<F>,
    pub call_context_field_tag: Expression<F>,
    pub mpt_update: Expression<F>,
}

impl<F: Field> Queries<F> {
    pub fn new(meta: &mut VirtualCells<'_, F>, c: Config) -> Self {
        Self {
            u8: meta.query_fixed(c.u8, Rotation::cur()),
            u10: meta.query_fixed(c.u10, Rotation::cur()),
            u16: meta.query_fixed(c.u16, Rotation::cur()),
            call_context_field_tag: meta.query_fixed(c.call_context_field_tag, Rotation::cur()),
            mpt_update: meta.query_advice(c.mpt_update, Rotation::cur()),
        }
    }
}

pub struct Chip<F: Field> {
    config: Config,
    _marker: PhantomData<F>,
}

impl<F: Field> Chip<F> {
    pub fn construct(config: Config) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(meta: &mut ConstraintSystem<F>) -> Config {
        Config {
            u8: meta.fixed_column(),
            u10: meta.fixed_column(),
            u16: meta.fixed_column(),
            call_context_field_tag: meta.fixed_column(),
            mpt_update: meta.advice_column(),
        }
    }

    pub(super) fn load(
        &self,
        layouter: &mut impl Layouter<F>,
        updates: &MptUpdates,
        word_randomness: F,
        lookup_randomness: F,
    ) -> Result<(), Error> {
        for (column, exponent) in [
            (self.config.u8, 8),
            (self.config.u10, 10),
            (self.config.u16, 16),
        ] {
            layouter.assign_region(
                || format!("assign u{} fixed column", exponent),
                |mut region| {
                    for i in 0..(1 << exponent) {
                        region.assign_fixed(
                            || format!("assign {} in u{} fixed column", i, exponent),
                            column,
                            i,
                            || Ok(F::from(i as u64)),
                        )?;
                    }
                    Ok(())
                },
            )?;
        }
        layouter.assign_region(
            || "assign call_context_field_tags fixed column",
            |mut region| {
                for field_tag in CallContextFieldTag::iter() {
                    region.assign_fixed(
                        || {
                            format!(
                                "assign {:?} in call_context_field_tag fixed column",
                                field_tag
                            )
                        },
                        self.config.call_context_field_tag,
                        field_tag as usize,
                        || Ok(F::from(field_tag as u64)),
                    )?;
                }
                Ok(())
            },
        )?;

        // TODO: move this into mpt_updates since it's not fixed.
        layouter.assign_region(
            || "assign rlc(mpt_updates) lookup column",
            |mut region| {
                region.assign_advice(
                    || "0 mpt update lookup",
                    self.config.mpt_update,
                    0,
                    || Ok(F::zero()),
                )?;
                for (offset, update) in updates.iter().enumerate() {
                    region.assign_advice(
                        || "mpt update lookup",
                        self.config.mpt_update,
                        offset + 1,
                        || Ok(update.lookup_assignment(word_randomness, lookup_randomness)),
                    )?;
                }
                Ok(())
            },
        )?;

        Ok(())
    }
}
