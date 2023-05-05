use eth_types::Field;
use gadgets::util::and;
use halo2_proofs::{
    circuit::Value,
    plonk::{Error, Expression},
};

use crate::evm_circuit::util::{
    constraint_builder::EVMConstraintBuilder, transpose_val_ret, CachedRegion, Word,
};

use super::IsZeroGadget;

/// Returns `1` when `lhs == rhs`, and returns `0` otherwise.
#[derive(Clone, Debug)]
pub struct IsEqualWordGadget<F> {
    is_zero_lo: IsZeroGadget<F>,
    is_zero_hi: IsZeroGadget<F>,
}

impl<F: Field> IsEqualWordGadget<F> {
    pub(crate) fn construct(
        cb: &mut EVMConstraintBuilder<F>,
        lhs: Word<Expression<F>>,
        rhs: Word<Expression<F>>,
    ) -> Self {
        let (lhs_lo, lhs_hi) = lhs.to_lo_hi();
        let (rhs_lo, rhs_hi) = rhs.to_lo_hi();
        let is_zero_lo = IsZeroGadget::construct(cb, lhs_lo.clone() - rhs_lo.clone());
        let is_zero_hi = IsZeroGadget::construct(cb, lhs_hi.clone() - rhs_hi.clone());

        Self {
            is_zero_lo,
            is_zero_hi,
        }
    }

    pub(crate) fn expr(&self) -> Expression<F> {
        and::expr([self.is_zero_lo.expr(), self.is_zero_hi.expr()])
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        lhs_lo: F,
        lhs_hi: F,
        rhs_lo: F,
        rhs_hi: F,
    ) -> Result<F, Error> {
        self.is_zero_lo.assign(region, offset, rhs_lo - lhs_lo)?;
        self.is_zero_hi.assign(region, offset, rhs_hi - lhs_hi)?;
        Ok(F::one())
    }

    pub(crate) fn assign_value(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        lhs_lo: Value<F>,
        lhs_hi: Value<F>,
        rhs_lo: Value<F>,
        rhs_hi: Value<F>,
    ) -> Result<Value<F>, Error> {
        let lo = lhs_lo.zip(rhs_lo);
        let hi = lhs_hi.zip(rhs_hi);
        transpose_val_ret(lo.zip(hi).map(|((lhs_lo, rhs_lo), (lhs_hi, rhs_hi))| {
            self.assign(region, offset, lhs_lo, lhs_hi, rhs_lo, rhs_hi)
        }))
    }
}

// TODO add unittest
