use super::super::CaseAllocation;
use super::super::Cell;
use crate::util::Expr;
use halo2::plonk::Error;
use halo2::{arithmetic::FieldExt, circuit::Region, plonk::Expression};

use super::constraint_builder::ConstraintBuilder;

// Returns `1` when `value == 0`, and returns `0` otherwise.
#[derive(Clone, Debug)]
pub struct IsZeroGadget<F> {
    pub(crate) inverse: Cell<F>,
}

impl<F: FieldExt> IsZeroGadget<F> {
    pub const NUM_CELLS: usize = 1;
    pub const NUM_WORDS: usize = 0;

    pub(crate) fn construct(alloc: &mut CaseAllocation<F>) -> Self {
        Self {
            inverse: alloc.cells.pop().unwrap(),
        }
    }

    pub(crate) fn constraints(
        &self,
        cb: &mut ConstraintBuilder<F>,
        value: Expression<F>,
    ) -> Expression<F> {
        let is_zero = 1.expr() - (value.clone() * self.inverse.expr());
        // when `value != 0` check `inverse = a.invert()`: value * (1 - value * inverse)
        cb.add_expression(value * is_zero.clone());
        // when `value == 0` check `inverse = 0`: `inverse ⋅ (1 - value * inverse)`
        cb.add_expression(self.inverse.expr() * is_zero.clone());

        is_zero
    }

    pub(crate) fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        value: F,
    ) -> Result<bool, Error> {
        let inverse = value.invert().unwrap_or(F::zero());
        self.inverse.assign(region, offset, Some(inverse))?;
        Ok(value.is_zero())
    }
}

// Returns `1` when `lhs == rhs`, and returns `0` otherwise.
#[derive(Clone, Debug)]
pub struct IsEqualGadget<F> {
    pub(crate) is_zero: IsZeroGadget<F>,
}

impl<F: FieldExt> IsEqualGadget<F> {
    pub const NUM_CELLS: usize = IsZeroGadget::<F>::NUM_CELLS;
    pub const NUM_WORDS: usize = IsZeroGadget::<F>::NUM_WORDS;

    pub(crate) fn construct(alloc: &mut CaseAllocation<F>) -> Self {
        Self {
            is_zero: IsZeroGadget::<F>::construct(alloc),
        }
    }

    pub(crate) fn constraints(
        &self,
        cb: &mut ConstraintBuilder<F>,
        lhs: Expression<F>,
        rhs: Expression<F>,
    ) -> Expression<F> {
        self.is_zero.constraints(cb, (lhs) - (rhs))
    }

    pub(crate) fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        lhs: F,
        rhs: F,
    ) -> Result<bool, Error> {
        self.is_zero.assign(region, offset, lhs - rhs)
    }
}
