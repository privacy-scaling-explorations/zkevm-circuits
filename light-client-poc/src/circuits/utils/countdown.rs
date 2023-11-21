use eth_types::Field;
use eyre::Result;
use gadgets::{
    is_zero::{IsZeroChip, IsZeroConfig, IsZeroInstruction},
    util::{and, not, Expr},
};
use halo2_proofs::{
    circuit::{Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Selector},
    poly::Rotation,
};

#[derive(Clone, Debug)]
pub struct Countdown<F: Field> {
    count: Column<Advice>,
    count_is_zero: IsZeroConfig<F>,
    count_propagate: IsZeroConfig<F>,
    count_decrement: IsZeroConfig<F>,
}

use super::xnif;

impl<F: Field> Countdown<F> {
    pub fn configure(meta: &mut ConstraintSystem<F>, q_enable: Selector) -> Self {
        let count = meta.advice_column();

        let count_is_zero_inv = meta.advice_column();
        let count_is_zero = IsZeroChip::configure(
            meta,
            |meta| meta.query_selector(q_enable),
            |meta| meta.query_advice(count, Rotation::cur()),
            count_is_zero_inv,
        );

        let count_propagate_inv = meta.advice_column();
        let count_propagate = IsZeroChip::configure(
            meta,
            |meta| meta.query_selector(q_enable),
            |meta| {
                meta.query_advice(count, Rotation::cur())
                    - meta.query_advice(count, Rotation::next())
            },
            count_propagate_inv,
        );

        let count_decrement_inv = meta.advice_column();
        let count_decrement = IsZeroChip::configure(
            meta,
            |meta| meta.query_selector(q_enable),
            |meta| {
                meta.query_advice(count, Rotation::cur())
                    - meta.query_advice(count, Rotation::next())
                    - 1.expr()
            },
            count_decrement_inv,
        );

        meta.create_gate("count decrements if > 0", |meta| {
            let q_enable = meta.query_selector(q_enable);

            [q_enable * xnif(not::expr(count_is_zero.expr()), count_decrement.expr())]
        });

        meta.create_gate("count propagates if == 0", |meta| {
            let q_enable = meta.query_selector(q_enable);

            [q_enable * xnif(count_is_zero.expr(), count_propagate.expr())]
        });

        Self {
            count,
            count_is_zero,
            count_propagate,
            count_decrement,
        }
    }

    pub fn name_columns(&self, region: &mut Region<'_, F>, prefix: &str) {
        region.name_column(|| format!("{}_countdown", prefix), self.count);
        region.name_column(
            || format!("{}_countdown_is_zero_inv", prefix),
            self.count_is_zero.value_inv,
        );
        region.name_column(
            || format!("{}_countdown_propagate_inv", prefix),
            self.count_propagate.value_inv,
        );
        region.name_column(
            || format!("{}_countdown_decrement_inv", prefix),
            self.count_decrement.value_inv,
        );
    }

    pub fn is_zero(&self) -> Expression<F> {
        self.count_is_zero.expr()
    }

    pub fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        prev_count: F,
        curr_count: F,
        last: bool,
    ) -> Result<(), Error> {

        region.assign_advice(|| "count", self.count, offset, || Value::known(curr_count))?;

        let count_is_zero = IsZeroChip::construct(self.count_is_zero.clone());
        let count_propagate = IsZeroChip::construct(self.count_propagate.clone());
        let count_decrement = IsZeroChip::construct(self.count_decrement.clone());

        count_is_zero.assign(region, offset, Value::known(curr_count))?;
        count_propagate.assign(region, offset, Value::known(prev_count - curr_count))?;
        count_decrement.assign(
            region,
            offset,
            Value::known(prev_count - curr_count - F::ONE),
        )?;

        if last {
            region.assign_advice(|| "count", self.count, offset+1, || Value::known(curr_count))?;
        }

        Ok(())
    }

}
