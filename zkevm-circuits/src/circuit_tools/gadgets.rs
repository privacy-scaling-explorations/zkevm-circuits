//! Circuit gadgets
use eth_types::Field;
use gadgets::util::{and, Expr};
use halo2_proofs::{
    circuit::Value,
    plonk::{Error, Expression},
};

use crate::util::{
    from_bytes, pow_of_two, transpose_val_ret,
    word::{Word, WordExpr},
};

use super::{
    cached_region::CachedRegion,
    cell_manager::{Cell, CellType},
    constraint_builder::ConstraintBuilder,
};

/// Returns `1` when `value == 0`, and returns `0` otherwise.
#[derive(Clone, Debug, Default)]
pub struct IsZeroGadget<F> {
    inverse: Option<Cell<F>>,
    is_zero: Option<Expression<F>>,
}

impl<F: Field> IsZeroGadget<F> {
    pub fn construct<C: CellType>(cb: &mut ConstraintBuilder<F, C>, value: Expression<F>) -> Self {
        circuit!([meta, cb], {
            let inverse = cb.query_cell_with_type(CellType::storage_for_expr(&value));

            let is_zero = 1.expr() - (value.expr() * inverse.expr());
            // `value != 0` => check `inverse = a.invert()`: value * (1 - value * inverse)
            require!(value * is_zero.clone() => 0);
            // `value == 0` => check `inverse = 0`: `inverse ⋅ (1 - value * inverse)`
            require!(inverse.expr() * is_zero.expr() => 0);

            Self {
                inverse: Some(inverse),
                is_zero: Some(is_zero),
            }
        })
    }

    pub(crate) fn expr(&self) -> Expression<F> {
        self.is_zero.as_ref().unwrap().clone()
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        value: F,
    ) -> Result<F, Error> {
        let inverse = value.invert().unwrap_or(F::ZERO);
        self.inverse
            .as_ref()
            .unwrap()
            .assign(region, offset, inverse)?;
        Ok(if value.is_zero().into() {
            F::ONE
        } else {
            F::ZERO
        })
    }
}

/// Returns `1` when `lhs == rhs`, and returns `0` otherwise.
#[derive(Clone, Debug, Default)]
pub struct IsEqualGadget<F> {
    is_zero: IsZeroGadget<F>,
}

impl<F: Field> IsEqualGadget<F> {
    pub(crate) fn construct<C: CellType>(
        cb: &mut ConstraintBuilder<F, C>,
        lhs: Expression<F>,
        rhs: Expression<F>,
    ) -> Self {
        let is_zero = IsZeroGadget::construct(cb, lhs - rhs);

        Self { is_zero }
    }

    pub(crate) fn expr(&self) -> Expression<F> {
        self.is_zero.expr()
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        lhs: F,
        rhs: F,
    ) -> Result<F, Error> {
        self.is_zero.assign(region, offset, lhs - rhs)
    }
}

/// Returns `1` when `lhs == rhs`, and returns `0` otherwise.
#[derive(Clone, Debug, Default)]
pub struct IsEqualWordGadget<F> {
    is_equal_lo: IsEqualGadget<F>,
    is_equal_hi: IsEqualGadget<F>,
}

impl<F: Field> IsEqualWordGadget<F> {
    pub(crate) fn construct<C: CellType>(
        cb: &mut ConstraintBuilder<F, C>,
        lhs: &Word<Expression<F>>,
        rhs: &Word<Expression<F>>,
    ) -> Self {
        let (lhs_lo, lhs_hi) = lhs.to_word().to_lo_hi();
        let (rhs_lo, rhs_hi) = rhs.to_word().to_lo_hi();
        let is_equal_lo = IsEqualGadget::construct(cb, lhs_lo, rhs_lo);
        let is_equal_hi = IsEqualGadget::construct(cb, lhs_hi, rhs_hi);

        Self {
            is_equal_lo,
            is_equal_hi,
        }
    }

    pub(crate) fn expr(&self) -> Expression<F> {
        and::expr([self.is_equal_lo.expr(), self.is_equal_hi.expr()])
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
        self.is_equal_lo.assign(region, offset, lhs_lo, rhs_lo)?;
        self.is_equal_hi.assign(region, offset, lhs_hi, rhs_hi)?;
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

    pub(crate) fn assign_u256(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        lhs: eth_types::Word,
        rhs: eth_types::Word,
    ) -> Result<F, Error> {
        self.assign(region, offset, Word::from(lhs), Word::from(rhs))
    }
}

/// Returns `1` when `lhs < rhs`, and returns `0` otherwise.
/// lhs and rhs `< 256**N_BYTES`
/// `N_BYTES` is required to be `<= MAX_N_BYTES_INTEGER` to prevent overflow:
/// values are stored in a single field element and two of these are added
/// together.
/// The equation that is enforced is `lhs - rhs == diff - (lt * range)`.
/// Because all values are `<= 256**N_BYTES` and `lt` is boolean, `lt` can only
/// be `1` when `lhs < rhs`.
#[derive(Clone, Debug, Default)]
pub struct LtGadget<F, const N_BYTES: usize> {
    lt: Option<Cell<F>>, // `1` when `lhs < rhs`, `0` otherwise.
    diff: Option<[Cell<F>; N_BYTES]>, /* The byte values of `diff`.
                          * `diff` equals `lhs - rhs` if `lhs >= rhs`,
                          * `lhs - rhs + range` otherwise. */
    range: F, // The range of the inputs, `256**N_BYTES`
}

impl<F: Field, const N_BYTES: usize> LtGadget<F, N_BYTES> {
    pub(crate) fn construct<C: CellType>(
        cb: &mut ConstraintBuilder<F, C>,
        lhs: Expression<F>,
        rhs: Expression<F>,
    ) -> Self {
        let lt = cb.query_bool();
        let diff = cb.query_bytes();
        let range = pow_of_two(N_BYTES * 8);

        // The equation we require to hold: `lhs - rhs == diff - (lt * range)`.
        cb.require_equal(
            "lhs - rhs == diff - (lt ⋅ range)",
            lhs - rhs,
            from_bytes::expr(&diff) - (lt.expr() * range),
        );

        Self {
            lt: Some(lt),
            diff: Some(diff),
            range,
        }
    }

    pub(crate) fn expr(&self) -> Expression<F> {
        self.lt.as_ref().unwrap().expr()
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        lhs: F,
        rhs: F,
    ) -> Result<(F, Vec<u8>), Error> {
        // Set `lt`
        let lt = lhs < rhs;
        self.lt
            .as_ref()
            .unwrap()
            .assign(region, offset, if lt { F::ONE } else { F::ZERO })?;
        // Set the bytes of diff
        let diff = (lhs - rhs) + (if lt { self.range } else { F::ZERO });
        let diff_bytes = diff.to_repr();
        for (idx, diff) in self.diff.as_ref().unwrap().iter().enumerate() {
            diff.assign(region, offset, F::from(diff_bytes[idx] as u64))?;
        }

        Ok((if lt { F::ONE } else { F::ZERO }, diff_bytes.to_vec()))
    }

    pub(crate) fn diff_bytes(&self) -> Vec<Cell<F>> {
        self.diff.as_ref().unwrap().to_vec()
    }
}
