use std::marker::PhantomData;

use eth_types::Field;
use gadgets::util::and;
use halo2_proofs::{
    circuit::Value,
    plonk::{Error, Expression},
};

use crate::{
    evm_circuit::util::{
        constraint_builder::EVMConstraintBuilder, transpose_val_ret, CachedRegion,
    },
    util::word::{Word, WordExpr},
};

use super::IsZeroGadget;

/// Returns `1` when `lhs == rhs`, and returns `0` otherwise.
#[derive(Clone, Debug)]
pub struct IsEqualWordGadget<F, T> {
    is_zero_lo: IsZeroGadget<F>,
    is_zero_hi: IsZeroGadget<F>,
    marker: PhantomData<T>,
}

impl<F: Field, T: WordExpr<F>> IsEqualWordGadget<F, T> {
    pub(crate) fn construct(cb: &mut EVMConstraintBuilder<F>, lhs: T, rhs: T) -> Self {
        let (lhs_lo, lhs_hi) = lhs.to_lo_hi();
        let (rhs_lo, rhs_hi) = rhs.to_lo_hi();
        let is_zero_lo = IsZeroGadget::construct(cb, lhs_lo.clone() - rhs_lo.clone());
        let is_zero_hi = IsZeroGadget::construct(cb, lhs_hi.clone() - rhs_hi.clone());

        Self {
            is_zero_lo,
            is_zero_hi,
            marker: Default::default(),
        }
    }

    pub(crate) fn expr(&self) -> Expression<F> {
        and::expr([self.is_zero_lo.expr(), self.is_zero_hi.expr()])
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        lhs: Word<F>,
        rhs: Word<F>,
    ) -> Result<F, Error> {
        let (lhs_lo, lhs_hi) = lhs.to_lo_hi();
        let (rhs_lo, rhs_hi) = rhs.to_lo_hi();
        self.is_zero_lo.assign(region, offset, *rhs_lo - *lhs_lo)?;
        self.is_zero_hi.assign(region, offset, *rhs_hi - *lhs_hi)?;
        Ok(F::from(2))
    }

    pub(crate) fn assign_value(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        lhs: Value<Word<F>>,
        rhs: Value<Word<F>>,
    ) -> Result<Value<F>, Error> {
        transpose_val_ret(
            lhs.zip(rhs)
                .map(|(lhs, rhs)| self.assign(region, offset, lhs, rhs)),
        )
    }
}

// TODO add unittest
