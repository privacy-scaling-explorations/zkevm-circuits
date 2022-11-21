use super::CachedRegion;
use crate::{
    evm_circuit::util::{constraint_builder::ConstraintBuilder, math_gadget::*, Cell},
    util::Expr,
};
use eth_types::Field;
use halo2_proofs::{
    circuit::Value,
    plonk::{Error, Expression},
};
/// Returns (quotient: numerator/denominator, remainder: numerator%denominator),
/// with `numerator` an expression and `denominator` a constant.
/// Input requirements:
/// - `quotient < 256**N_BYTES`
/// - `quotient * denominator < field size`
/// - `remainder < denominator` requires a range lookup table for `denominator`
#[derive(Clone, Debug)]
pub struct ConstantDivisionGadget<F, const N_BYTES: usize> {
    quotient: Cell<F>,
    remainder: Cell<F>,
    denominator: u64,
    quotient_range_check: RangeCheckGadget<F, N_BYTES>,
}

impl<F: Field, const N_BYTES: usize> ConstantDivisionGadget<F, N_BYTES> {
    pub(crate) fn construct(
        cb: &mut ConstraintBuilder<F>,
        numerator: Expression<F>,
        denominator: u64,
    ) -> Self {
        let quotient = cb.query_cell();
        let remainder = cb.query_cell();

        // Require that remainder < denominator
        cb.range_lookup(remainder.expr(), denominator);

        // Require that quotient < 2**N_BYTES
        // so we can't have any overflow when doing `quotient * denominator`.
        let quotient_range_check = RangeCheckGadget::construct(cb, quotient.expr());

        // Check if the division was done correctly
        cb.require_equal(
            "numerator - remainder == quotient ⋅ denominator",
            numerator - remainder.expr(),
            quotient.expr() * denominator.expr(),
        );

        Self {
            quotient,
            remainder,
            denominator,
            quotient_range_check,
        }
    }

    pub(crate) fn quotient(&self) -> Expression<F> {
        self.quotient.expr()
    }

    pub(crate) fn remainder(&self) -> Expression<F> {
        self.remainder.expr()
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        numerator: u128,
    ) -> Result<(u128, u128), Error> {
        let denominator = self.denominator as u128;
        let quotient = numerator / denominator;
        let remainder = numerator % denominator;

        self.quotient
            .assign(region, offset, Value::known(F::from_u128(quotient)))?;
        self.remainder
            .assign(region, offset, Value::known(F::from_u128(remainder)))?;

        self.quotient_range_check
            .assign(region, offset, F::from_u128(quotient))?;

        Ok((quotient, remainder))
    }
}

#[cfg(test)]
mod tests {
    use super::test_util::*;
    use super::*;
    use eth_types::*;
    use halo2_proofs::halo2curves::bn256::Fr;
    use halo2_proofs::plonk::Error;

    #[test]
    fn test_constantdivisiongadget() {
        const N: usize = 4;
        #[derive(Clone)]
        /// a < b
        struct ConstantDivisionTestContainer<F, const DENOMINATOR: u64, const REMINDER: u64> {
            constdiv_gadget: ConstantDivisionGadget<F, N>,
            a: Cell<F>,
        }

        impl<F: Field, const DENOMINATOR: u64, const REMAINDER: u64> MathGadgetContainer<F>
            for ConstantDivisionTestContainer<F, DENOMINATOR, REMAINDER>
        {
            const NAME: &'static str = "ConstantDivisionGadget";

            fn configure_gadget_container(cb: &mut ConstraintBuilder<F>) -> Self {
                let a = cb.query_cell();
                let constdiv_gadget =
                    ConstantDivisionGadget::<F, N>::construct(cb, a.expr(), DENOMINATOR);

                cb.require_equal(
                    "a == n * denom",
                    constdiv_gadget.remainder(),
                    REMAINDER.expr(),
                );

                ConstantDivisionTestContainer { constdiv_gadget, a }
            }

            fn assign_gadget_container(
                &self,
                input_words: &[Word],
                region: &mut CachedRegion<'_, '_, F>,
            ) -> Result<(), Error> {
                let a = u64::from_le_bytes(input_words[0].to_le_bytes()[..8].try_into().unwrap());
                let offset = 0;

                self.a.assign(region, offset, Value::known(F::from(a)))?;
                self.constdiv_gadget.assign(region, offset, a as u128)?;

                Ok(())
            }
        }

        test_math_gadget_container::<Fr, ConstantDivisionTestContainer<Fr, 5, 0>>(
            vec![Word::from(0)],
            true,
        );

        test_math_gadget_container::<Fr, ConstantDivisionTestContainer<Fr, 5, 0>>(
            vec![Word::from(5)],
            true,
        );

        test_math_gadget_container::<Fr, ConstantDivisionTestContainer<Fr, 5, 1>>(
            vec![Word::from(1)],
            true,
        );

        test_math_gadget_container::<Fr, ConstantDivisionTestContainer<Fr, 5, 4>>(
            vec![Word::from(1)],
            false,
        );

        test_math_gadget_container::<Fr, ConstantDivisionTestContainer<Fr, 16, 0>>(
            vec![Word::from(1 << N)],
            true,
        );
    }
}
