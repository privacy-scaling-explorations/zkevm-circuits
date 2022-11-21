use super::CachedRegion;
use crate::{
    evm_circuit::util::{constraint_builder::ConstraintBuilder, Cell},
    util::Expr,
};
use eth_types::Field;
use halo2_proofs::{
    circuit::Value,
    plonk::{Error, Expression},
};

#[derive(Clone, Debug)]
pub struct BatchedIsZeroGadget<F, const N: usize> {
    is_zero: Cell<F>,
    nonempty_witness: Cell<F>,
}

impl<F: Field, const N: usize> BatchedIsZeroGadget<F, N> {
    pub(crate) fn construct(cb: &mut ConstraintBuilder<F>, values: [Expression<F>; N]) -> Self {
        let is_zero = cb.query_bool();
        let nonempty_witness = cb.query_cell();

        for value in values.iter() {
            cb.require_zero(
                "is_zero is 0 if there is any non-zero value",
                is_zero.expr() * value.clone(),
            );
        }

        cb.require_zero(
            "is_zero is 1 if values are all zero",
            values.iter().fold(1.expr() - is_zero.expr(), |acc, value| {
                acc * (1.expr() - value.expr() * nonempty_witness.clone().expr())
            }),
        );

        Self {
            is_zero,
            nonempty_witness,
        }
    }

    pub(crate) fn expr(&self) -> Expression<F> {
        self.is_zero.expr()
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        values: [F; N],
    ) -> Result<F, Error> {
        let is_zero =
            if let Some(inverse) = values.iter().find_map(|value| Option::from(value.invert())) {
                self.nonempty_witness
                    .assign(region, offset, Value::known(inverse))?;
                F::zero()
            } else {
                F::one()
            };
        self.is_zero.assign(region, offset, Value::known(is_zero))?;

        Ok(is_zero)
    }
}

#[cfg(test)]
mod tests {
    use super::super::test_util::*;
    use super::*;
    use crate::evm_circuit::util;
    use eth_types::*;
    use halo2_proofs::halo2curves::bn256::Fr;
    use halo2_proofs::plonk::Error;

    #[test]
    fn test_batched_iszero() {
        const N: usize = 32;
        #[derive(Clone)]
        /// all(n.cells) == 0
        struct IsZeroGadgetTestContainer<F> {
            z_gadget: BatchedIsZeroGadget<F, N>,
            n: util::Word<F>,
        }

        impl<F: Field> MathGadgetContainer<F> for IsZeroGadgetTestContainer<F> {
            const NAME: &'static str = "BatchedIsZeroGadget";

            fn configure_gadget_container(cb: &mut ConstraintBuilder<F>) -> Self {
                let n = cb.query_word();
                let z_gadget = BatchedIsZeroGadget::<F, N>::construct(
                    cb,
                    n.cells
                        .iter()
                        .map(|cell| cell.expr())
                        .collect::<Vec<Expression<F>>>()
                        .try_into()
                        .unwrap(),
                );
                cb.require_equal("Input must be all 0", z_gadget.expr(), 1.expr());
                IsZeroGadgetTestContainer { z_gadget, n }
            }

            fn assign_gadget_container(
                &self,
                input_words: &[Word],
                region: &mut CachedRegion<'_, '_, F>,
            ) -> Result<(), Error> {
                let n = input_words[0];
                let offset = 0;

                self.n.assign(region, offset, Some(n.to_le_bytes()))?;
                self.z_gadget.assign(
                    region,
                    0,
                    n.to_le_bytes().map(|byte| F::from(byte as u64)),
                )?;

                Ok(())
            }
        }

        test_math_gadget_container::<Fr, IsZeroGadgetTestContainer<Fr>>(vec![Word::from(0)], true);

        test_math_gadget_container::<Fr, IsZeroGadgetTestContainer<Fr>>(vec![Word::from(1)], false);

        test_math_gadget_container::<Fr, IsZeroGadgetTestContainer<Fr>>(
            vec![Word::from(1u64 << 32)],
            false,
        );

        test_math_gadget_container::<Fr, IsZeroGadgetTestContainer<Fr>>(vec![Word::MAX], false);
    }
}
