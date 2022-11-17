use super::CachedRegion;
use crate::{
    evm_circuit::util::{self, constraint_builder::ConstraintBuilder, sum, Cell},
    util::Expr,
};
use eth_types::{Field, ToLittleEndian};
use halo2_proofs::{
    circuit::Value,
    plonk::{Error, Expression},
};

/// Returns `1` when `value == 0`, and returns `0` otherwise.
#[derive(Clone, Debug)]
pub struct IsZeroGadget<F> {
    inverse: Cell<F>,
    is_zero: Expression<F>,
}

impl<F: Field> IsZeroGadget<F> {
    pub(crate) fn construct(cb: &mut ConstraintBuilder<F>, value: Expression<F>) -> Self {
        let inverse = cb.query_cell();

        let is_zero = 1.expr() - (value.clone() * inverse.expr());
        // when `value != 0` check `inverse = a.invert()`: value * (1 - value *
        // inverse)
        cb.add_constraint("value ⋅ (1 - value ⋅ value_inv)", value * is_zero.clone());
        // when `value == 0` check `inverse = 0`: `inverse ⋅ (1 - value *
        // inverse)`
        cb.add_constraint(
            "value_inv ⋅ (1 - value ⋅ value_inv)",
            inverse.expr() * is_zero.clone(),
        );

        Self { inverse, is_zero }
    }

    pub(crate) fn expr(&self) -> Expression<F> {
        self.is_zero.clone()
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        value: F,
    ) -> Result<F, Error> {
        let inverse = value.invert().unwrap_or(F::zero());
        self.inverse.assign(region, offset, Value::known(inverse))?;
        Ok(if value.is_zero().into() {
            F::one()
        } else {
            F::zero()
        })
    }
}

mod tests {
    use super::util::math_gadget::tests::*;
    use super::*;
    use eth_types::Word;
    use halo2_proofs::halo2curves::bn256::Fr;
    use halo2_proofs::plonk::Error;

    #[test]
    fn test_iszero() {
        #[derive(Clone)]
        /// n != 0
        struct IsZeroGadgetTestContainer<F> {
            z_gadget: IsZeroGadget<F>,
            n: util::Word<F>,
        }

        impl<F: Field> MathGadgetContainer<F> for IsZeroGadgetTestContainer<F> {
            const NAME: &'static str = "IsZeroGadget";

            fn configure_gadget_container(cb: &mut ConstraintBuilder<F>) -> Self {
                let n = cb.query_word();
                let z_gadget = IsZeroGadget::<F>::construct(cb, sum::expr(&n.cells));
                cb.require_equal("Input must not be 0", z_gadget.expr(), 0.expr());
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
                self.z_gadget
                    .assign(region, 0, sum::value(&n.to_le_bytes()))?;

                Ok(())
            }
        }

        test_math_gadget_container::<Fr, IsZeroGadgetTestContainer<Fr>>(vec![Word::from(0)], false);

        test_math_gadget_container::<Fr, IsZeroGadgetTestContainer<Fr>>(vec![Word::from(1)], true);

        test_math_gadget_container::<Fr, IsZeroGadgetTestContainer<Fr>>(
            vec![Word::from(1000)],
            true,
        );

        test_math_gadget_container::<Fr, IsZeroGadgetTestContainer<Fr>>(vec![Word::MAX], true);
    }
}
