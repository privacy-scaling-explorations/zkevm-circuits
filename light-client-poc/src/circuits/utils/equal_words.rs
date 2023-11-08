
use eth_types::Field;
use eyre::Result;
use gadgets::{
    is_zero::{IsZeroChip, IsZeroConfig, IsZeroInstruction},
    util::and,
};
use halo2_proofs::{
    circuit::{Region, Value},
    plonk::{
        Advice, Column, ConstraintSystem, Error, Expression,
        Selector,
    },
    poly::Rotation,
};
use zkevm_circuits::util::word::Word;

#[derive(Clone, Debug)]
pub struct EqualWordsConfig<F: Field>(Word<IsZeroConfig<F>>);
impl<F: Field> EqualWordsConfig<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: Selector,
        first: (Word<Column<Advice>>, Rotation),
        second: (Word<Column<Advice>>, Rotation),
    ) -> Self {
        let lo_inv = meta.advice_column();
        let lo = IsZeroChip::configure(
            meta,
            |meta| meta.query_selector(q_enable),
            |meta| {
                meta.query_advice(first.0.lo(), first.1)
                    - meta.query_advice(second.0.lo(), second.1)
            },
            lo_inv,
        );

        let hi_inv = meta.advice_column();
        let hi = IsZeroChip::configure(
            meta,
            |meta| meta.query_selector(q_enable),
            |meta| {
                meta.query_advice(first.0.hi(), first.1)
                    - meta.query_advice(second.0.hi(), second.1)
            },
            hi_inv,
        );

        Self(Word::new([lo, hi]))
    }

    pub fn expr(&self) -> Expression<F> {
        and::expr([self.0.hi().expr(), self.0.lo().expr()])
    }

    pub fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        name: &str,
        first: &Word<F>,
        second: &Word<F>,
    ) -> Result<(), Error> {
        region.name_column(|| format!("{}_lo_inv", name), self.0.lo().value_inv);
        region.name_column(|| format!("{}_hi_inv", name), self.0.hi().value_inv);

        let lo = IsZeroChip::construct(self.0.lo());
        let hi = IsZeroChip::construct(self.0.hi());

        lo.assign(region, offset, Value::known(first.lo() - second.lo()))?;
        hi.assign(region, offset, Value::known(first.hi() - second.hi()))?;

        Ok(())
    }
}
