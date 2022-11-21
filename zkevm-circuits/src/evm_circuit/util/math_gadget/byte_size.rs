use super::CachedRegion;
use crate::{
    evm_circuit::{
        param::N_BYTES_WORD,
        util::{
            self, constraint_builder::ConstraintBuilder, from_bytes, math_gadget::*, pow_of_two,
            pow_of_two_expr, select, split_u256, split_u256_limb64, sum, Cell,
        },
    },
    util::Expr,
};
use eth_types::{Field, ToLittleEndian, ToScalar, Word};
use halo2_proofs::{
    circuit::Value,
    plonk::{Error, Expression},
};

/// Gadget to verify the byte-size of a word, i.e. the minimum number of bytes
/// it takes to represent the word.
#[derive(Clone, Debug)]
pub(crate) struct ByteSizeGadget<F> {
    /// Array of indices from which only one will be turned on. The turned on
    /// index is the index of the most significant non-zero byte in value.
    most_significant_nonzero_byte_index: [Cell<F>; N_BYTES_WORD + 1],
    /// The inverse of the most significant non-zero byte in value. The inverse
    /// should exist if the byte-size is non-zero.
    most_significant_nonzero_byte_inverse: Cell<F>,
}

impl<F: Field> ByteSizeGadget<F> {
    pub(crate) fn construct(cb: &mut ConstraintBuilder<F>, value_rlc: &util::Word<F>) -> Self {
        let most_significant_nonzero_byte_index = [(); N_BYTES_WORD + 1].map(|()| cb.query_bool());
        cb.require_equal(
            "exactly one cell in indices is 1",
            sum::expr(&most_significant_nonzero_byte_index),
            1.expr(),
        );

        let most_significant_nonzero_byte_inverse = cb.query_cell();
        for (i, index) in most_significant_nonzero_byte_index.iter().enumerate() {
            cb.condition(index.expr(), |cb| {
                cb.require_zero(
                    "more significant bytes are 0",
                    sum::expr(&value_rlc.cells[i..32]),
                );
                if i > 0 {
                    cb.require_equal(
                        "most significant nonzero byte's inverse exists",
                        value_rlc.cells[i - 1].expr()
                            * most_significant_nonzero_byte_inverse.expr(),
                        1.expr(),
                    )
                } else {
                    cb.require_zero(
                        "byte size == 0",
                        most_significant_nonzero_byte_inverse.expr(),
                    );
                }
            });
        }

        Self {
            most_significant_nonzero_byte_index,
            most_significant_nonzero_byte_inverse,
        }
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        value: Word,
    ) -> Result<(), Error> {
        let byte_size = (value.bits() + 7) / 8;
        for (i, byte_index) in self.most_significant_nonzero_byte_index.iter().enumerate() {
            byte_index.assign(
                region,
                offset,
                Value::known(if i == byte_size { F::one() } else { F::zero() }),
            )?;
        }
        if byte_size > 0 {
            let most_significant_nonzero_byte = value.to_le_bytes()[byte_size - 1];
            self.most_significant_nonzero_byte_inverse.assign(
                region,
                offset,
                Value::known(
                    F::from(u64::try_from(most_significant_nonzero_byte).unwrap())
                        .invert()
                        .unwrap(),
                ),
            )?;
        } else {
            self.most_significant_nonzero_byte_inverse.assign(
                region,
                offset,
                Value::known(F::zero()),
            )?;
        }
        Ok(())
    }

    pub(crate) fn byte_size(&self) -> Expression<F> {
        sum::expr(
            self.most_significant_nonzero_byte_index
                .iter()
                .enumerate()
                .map(|(i, cell)| i.expr() * cell.expr()),
        )
    }
}
