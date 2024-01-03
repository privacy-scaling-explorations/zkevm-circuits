use eth_types::Field;
use eyre::Result;
use gadgets::{
    is_zero::{IsZeroChip, IsZeroInstruction},
    util::{not, Expr},
};
use halo2_proofs::{
    circuit::{Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Selector},
    poly::Rotation,
};

#[derive(Clone, Debug)]
pub struct Countdown<F: Field> {
    count: Column<Advice>,
    is_zero_expr: Expression<F>,
    count_is_zero: IsZeroChip<F>,
    count_propagate: IsZeroChip<F>,
    count_decrement: IsZeroChip<F>,
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
            is_zero_expr: count_is_zero.expr(),
            count_is_zero: IsZeroChip::construct(count_is_zero),
            count_propagate: IsZeroChip::construct(count_propagate),
            count_decrement: IsZeroChip::construct(count_decrement),
        }
    }

    pub fn annotate_columns_in_region(&self, region: &mut Region<'_, F>, prefix: &str) {
        region.name_column(|| format!("{}_countdown", prefix), self.count);
        self.count_is_zero
            .annotate_columns_in_region(region, "count_is_zero");
        self.count_propagate
            .annotate_columns_in_region(region, "count_propagate");
        self.count_decrement
            .annotate_columns_in_region(region, "count_decrement");
    }

    pub fn is_zero(&self) -> Expression<F> {
        self.is_zero_expr.clone()
    }

    pub fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        curr_count: F,
        next_count: F,
        last: bool,
    ) -> Result<(), Error> {
        region.assign_advice(|| "count", self.count, offset, || Value::known(curr_count))?;

        self.count_is_zero
            .assign(region, offset, Value::known(curr_count))?;
        self.count_propagate
            .assign(region, offset, Value::known(curr_count - next_count))?;
        self.count_decrement.assign(
            region,
            offset,
            Value::known(curr_count - next_count - F::ONE),
        )?;

        if last {
            region.assign_advice(
                || "count",
                self.count,
                offset + 1,
                || Value::known(next_count),
            )?;
        }

        Ok(())
    }
}
