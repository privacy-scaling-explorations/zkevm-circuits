use super::CachedRegion;
use crate::{
    evm_circuit::{
        util::math_gadget::*,
        util::{self, constraint_builder::ConstraintBuilder, sum},
    },
    util::Expr,
};
use eth_types::{Field, ToLittleEndian};
use halo2_proofs::plonk::{Error, Expression};

/// Returns `1` when `lhs == rhs`, and returns `0` otherwise.
#[derive(Clone, Debug)]
pub struct IsEqualGadget<F> {
    is_zero: IsZeroGadget<F>,
}

impl<F: Field> IsEqualGadget<F> {
    pub(crate) fn construct(
        cb: &mut ConstraintBuilder<F>,
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

mod tests {
    use super::util::math_gadget::tests::*;
    use super::*;
    use eth_types::Word;
    use halo2_proofs::halo2curves::bn256::Fr;
    use halo2_proofs::plonk::Error;

    #[test]
    fn test_isequal() {
        #[derive(Clone)]
        /// a == b
        struct IsEqualGadgetTestContainer<F> {
            eq_gadget: IsEqualGadget<F>,
            a: util::Word<F>,
            b: util::Word<F>,
        }

        impl<F: Field> MathGadgetContainer<F> for IsEqualGadgetTestContainer<F> {
            const NAME: &'static str = "IsEqualGadget";

            fn configure_gadget_container(cb: &mut ConstraintBuilder<F>) -> Self {
                let a = cb.query_rlc();
                let b = cb.query_rlc();
                let eq_gadget =
                    IsEqualGadget::<F>::construct(cb, sum::expr(&a.cells), sum::expr(&b.cells));
                cb.require_equal("Inputs must equal", eq_gadget.expr(), 1.expr());
                IsEqualGadgetTestContainer {
                    eq_gadget: eq_gadget,
                    a,
                    b,
                }
            }

            fn assign_gadget_container(
                &self,
                input_words: &[Word],
                region: &mut CachedRegion<'_, '_, F>,
            ) -> Result<(), Error> {
                let a = input_words[0];
                let b = input_words[1];
                let offset = 0;

                self.a.assign(region, offset, Some(a.to_le_bytes()))?;
                self.b.assign(region, offset, Some(b.to_le_bytes()))?;
                self.eq_gadget.assign(
                    region,
                    0,
                    sum::value(&a.to_le_bytes()),
                    sum::value(&b.to_le_bytes()),
                )?;

                Ok(())
            }
        }

        test_math_gadget_container::<Fr, IsEqualGadgetTestContainer<Fr>>(
            vec![Word::from(0), Word::from(0)],
            true,
        );

        test_math_gadget_container::<Fr, IsEqualGadgetTestContainer<Fr>>(
            vec![Word::from(1), Word::from(1)],
            true,
        );

        test_math_gadget_container::<Fr, IsEqualGadgetTestContainer<Fr>>(
            vec![Word::from(1000), Word::from(1000)],
            true,
        );

        test_math_gadget_container::<Fr, IsEqualGadgetTestContainer<Fr>>(
            vec![Word::from(1), Word::from(0)],
            false,
        );

        test_math_gadget_container::<Fr, IsEqualGadgetTestContainer<Fr>>(
            vec![Word::from(0), Word::from(1)],
            false,
        );
    }
}
