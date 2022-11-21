use super::CachedRegion;
use crate::evm_circuit::{
    util::math_gadget::*,
    util::{constraint_builder::ConstraintBuilder, sum},
};
use eth_types::Field;
use halo2_proofs::plonk::{Error, Expression};

/// Returns (lt, eq):
/// - `lt` is `1` when `lhs < rhs`, `0` otherwise.
/// - `eq` is `1` when `lhs == rhs`, `0` otherwise.
/// lhs and rhs `< 256**N_BYTES`
/// `N_BYTES` is required to be `<= MAX_N_BYTES_INTEGER`.
#[derive(Clone, Debug)]
pub struct ComparisonGadget<F, const N_BYTES: usize> {
    lt: LtGadget<F, N_BYTES>,
    eq: IsZeroGadget<F>,
}

impl<F: Field, const N_BYTES: usize> ComparisonGadget<F, N_BYTES> {
    pub(crate) fn construct(
        cb: &mut ConstraintBuilder<F>,
        lhs: Expression<F>,
        rhs: Expression<F>,
    ) -> Self {
        let lt = LtGadget::<F, N_BYTES>::construct(cb, lhs, rhs);
        let eq = IsZeroGadget::<F>::construct(cb, sum::expr(&lt.diff_bytes()));

        Self { lt, eq }
    }

    pub(crate) fn expr(&self) -> (Expression<F>, Expression<F>) {
        (self.lt.expr(), self.eq.expr())
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        lhs: F,
        rhs: F,
    ) -> Result<(F, F), Error> {
        // lt
        let (lt, diff) = self.lt.assign(region, offset, lhs, rhs)?;

        // eq
        let eq = self.eq.assign(region, offset, sum::value(&diff))?;

        Ok((lt, eq))
    }
}

#[cfg(test)]
mod tests {
    use super::test_util::*;
    use super::*;
    use crate::evm_circuit::util::Cell;
    use eth_types::*;
    use halo2_proofs::halo2curves::bn256::Fr;
    use halo2_proofs::plonk::Error;

    #[test]
    fn test_comparison() {
        const N: usize = 4;
        #[derive(Clone)]
        /// a < b
        struct ComparisonTestContainer<F, const CHECK_EQ: bool> {
            cmp_gadget: ComparisonGadget<F, N>,
            a: Cell<F>,
            b: Cell<F>,
        }

        impl<F: Field, const CHECK_EQ: bool> MathGadgetContainer<F>
            for ComparisonTestContainer<F, CHECK_EQ>
        {
            const NAME: &'static str = "ComparisonGadget";

            fn configure_gadget_container(cb: &mut ConstraintBuilder<F>) -> Self {
                let a = cb.query_cell();
                let b = cb.query_cell();
                let cmp_gadget = ComparisonGadget::<F, N>::construct(cb, a.expr(), b.expr());
                cb.require_equal(
                    "(a < b) * (a == b) == 0",
                    cmp_gadget.expr().0 * cmp_gadget.expr().1,
                    0.expr(),
                );

                if CHECK_EQ {
                    cb.require_equal("a == b", cmp_gadget.expr().1, 1.expr());
                } else {
                    cb.require_equal("a < b", cmp_gadget.expr().0, 1.expr());
                }

                ComparisonTestContainer { cmp_gadget, a, b }
            }

            fn assign_gadget_container(
                &self,
                input_words: &[Word],
                region: &mut CachedRegion<'_, '_, F>,
            ) -> Result<(), Error> {
                let a = input_words[0].to_scalar().unwrap();
                let b = input_words[1].to_scalar().unwrap();
                let offset = 0;

                self.a.assign(region, offset, Value::known(a))?;
                self.b.assign(region, offset, Value::known(b))?;
                self.cmp_gadget.assign(region, offset, a, b)?;

                Ok(())
            }
        }

        // a == b check
        test_math_gadget_container::<Fr, ComparisonTestContainer<Fr, true>>(
            vec![Word::from(0), Word::from(0)],
            true,
        );

        test_math_gadget_container::<Fr, ComparisonTestContainer<Fr, true>>(
            vec![Word::from(1), Word::from(1)],
            true,
        );

        test_math_gadget_container::<Fr, ComparisonTestContainer<Fr, true>>(
            vec![Word::from(1 << N), Word::from(1 << N)],
            true,
        );

        test_math_gadget_container::<Fr, ComparisonTestContainer<Fr, true>>(
            vec![Word::from(0), Word::from(1 << N)],
            false,
        );

        // a < b check
        test_math_gadget_container::<Fr, ComparisonTestContainer<Fr, false>>(
            vec![Word::from(0), Word::from(1)],
            true,
        );

        test_math_gadget_container::<Fr, ComparisonTestContainer<Fr, false>>(
            vec![Word::from(1), Word::from(1 << N)],
            true,
        );

        test_math_gadget_container::<Fr, ComparisonTestContainer<Fr, false>>(
            vec![Word::from(1), Word::from(0)],
            false,
        );

        test_math_gadget_container::<Fr, ComparisonTestContainer<Fr, false>>(
            vec![Word::from(10000), Word::from(2 << N)],
            false,
        );
    }
}
