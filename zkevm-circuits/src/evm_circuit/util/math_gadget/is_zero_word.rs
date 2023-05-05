use eth_types::Field;
use gadgets::util::{or, Expr};
use halo2_proofs::{
    circuit::Value,
    plonk::{Error, Expression},
};

use crate::evm_circuit::util::{
    constraint_builder::{ConstrainBuilderCommon, EVMConstraintBuilder},
    transpose_val_ret, CachedRegion, Cell, CellType, ToWordExpr, Word32, WordCells,
};

/// Returns `1` when `word == 0`, and returns `0` otherwise.
#[derive(Clone, Debug)]
pub struct IsZeroWordGadget<F> {
    inverse_lo: Cell<F>,
    inverse_hi: Cell<F>,
    is_zero: Expression<F>,
}

impl<F: Field> IsZeroWordGadget<F> {
    pub(crate) fn construct(cb: &mut EVMConstraintBuilder<F>, word: Word32<Cell<F>>) -> Self {
        let (word_lo, word_hi) = word.expr().to_word().to_lo_hi();
        let inverse_lo = cb.query_cell_with_type(CellType::storage_for_expr(word_lo));
        let inverse_hi = cb.query_cell_with_type(CellType::storage_for_expr(word_hi));

        let is_zero_lo = 1.expr() - (word_lo.clone() * inverse_lo.expr().clone());
        let is_zero_hi = 1.expr() - (word_hi.clone() * inverse_hi.expr().clone());
        // when `value != 0` check `inverse = a.invert()`: value * (1 - value *
        // inverse)
        cb.add_constraint(
            "word_lo ⋅ (1 - word_lo ⋅ word_lo_inv)",
            word_lo.clone() * is_zero_lo.clone(),
        );
        cb.add_constraint(
            "word_hi ⋅ (1 - word_hi ⋅ word_hi_inv)",
            word_hi.clone() * is_zero_hi.clone(),
        );
        // when `value == 0` check `inverse = 0`: `inverse ⋅ (1 - value *
        // inverse)`
        cb.add_constraint(
            "word_lo_inv ⋅ (1 - word_lo ⋅ word_lo_inv)",
            inverse_lo.expr() * is_zero_lo.clone(),
        );
        cb.add_constraint(
            "word_hi_inv ⋅ (1 - word_hi ⋅ word_hi_inv)",
            inverse_hi.expr() * is_zero_hi.clone(),
        );

        Self {
            inverse_lo,
            inverse_hi,
            is_zero: or::expr([is_zero_lo, is_zero_hi]),
        }
    }

    pub(crate) fn expr(&self) -> Expression<F> {
        self.is_zero.clone()
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        value_lo: F,
        value_hi: F,
    ) -> Result<F, Error> {
        let inverse_lo = value_lo.invert().unwrap_or(F::zero());
        self.inverse_lo
            .assign(region, offset, Value::known(inverse_lo))?;
        let inverse_hi = value_hi.invert().unwrap_or(F::zero());
        self.inverse_hi
            .assign(region, offset, Value::known(inverse_hi))?;
        Ok(if value_lo.is_zero().into() && value_hi.is_zero().into() {
            F::one()
        } else {
            F::zero()
        })
    }

    pub(crate) fn assign_value(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        value_lo: Value<F>,
        value_hi: Value<F>,
    ) -> Result<Value<F>, Error> {
        transpose_val_ret(
            value_lo
                .zip(value_hi)
                .map(|(value_lo, value_hi)| self.assign(region, offset, value_lo, value_hi)),
        )
    }
}

// TODO adding unittest
