use std::marker::PhantomData;

use crate::{
    evm_circuit::util::{
        self, constraint_builder::EVMConstraintBuilder, from_bytes, math_gadget::*, split_u256,
        CachedRegion,
    },
    util::word::WordExpr,
};
use eth_types::{Field, Word};
use halo2_proofs::plonk::{Error, Expression};

/// Returns `1` when `lhs < rhs`, and returns `0` otherwise.
/// lhs and rhs are both 256-bit word.
#[derive(Clone, Debug)]
#[deprecated(note = "LtWordGadget is favored")]
pub struct LtWordGadgetLegacy<F> {
    comparison_hi: ComparisonGadget<F, 16>,
    lt_lo: LtGadget<F, 16>,
}

impl<F: Field> LtWordGadgetLegacy<F> {
    pub(crate) fn construct(
        cb: &mut EVMConstraintBuilder<F>,
        lhs: &util::WordLegacy<F>,
        rhs: &util::WordLegacy<F>,
    ) -> Self {
        let comparison_hi = ComparisonGadget::construct(
            cb,
            from_bytes::expr(&lhs.cells[16..]),
            from_bytes::expr(&rhs.cells[16..]),
        );
        let lt_lo = LtGadget::construct(
            cb,
            from_bytes::expr(&lhs.cells[..16]),
            from_bytes::expr(&rhs.cells[..16]),
        );
        Self {
            comparison_hi,
            lt_lo,
        }
    }

    pub(crate) fn expr(&self) -> Expression<F> {
        let (hi_lt, hi_eq) = self.comparison_hi.expr();
        hi_lt + hi_eq * self.lt_lo.expr()
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        lhs: Word,
        rhs: Word,
    ) -> Result<(), Error> {
        let (lhs_lo, lhs_hi) = split_u256(&lhs);
        let (rhs_lo, rhs_hi) = split_u256(&rhs);
        self.comparison_hi.assign(
            region,
            offset,
            F::from_u128(lhs_hi.as_u128()),
            F::from_u128(rhs_hi.as_u128()),
        )?;
        self.lt_lo.assign(
            region,
            offset,
            F::from_u128(lhs_lo.as_u128()),
            F::from_u128(rhs_lo.as_u128()),
        )?;
        Ok(())
    }
}

/// Returns `1` when `lhs < rhs`, and returns `0` otherwise.
/// lhs and rhs are both 256-bit word.
#[derive(Clone, Debug)]
pub struct LtWordGadget<F, T1, T2> {
    comparison_hi: ComparisonGadget<F, 16>,
    lt_lo: LtGadget<F, 16>,
    _marker: PhantomData<(T1, T2)>,
}

impl<F: Field, T1: WordExpr<F>, T2: WordExpr<F>> LtWordGadget<F, T1, T2> {
    pub(crate) fn construct(cb: &mut EVMConstraintBuilder<F>, lhs: T1, rhs: T2) -> Self {
        let lhs_expr = lhs.to_word();
        let rhs_expr = rhs.to_word();
        let comparison_hi =
            ComparisonGadget::construct(cb, lhs_expr.hi().clone(), rhs_expr.hi().clone());
        let lt_lo = LtGadget::construct(cb, lhs_expr.lo().clone(), rhs_expr.lo().clone());
        Self {
            comparison_hi,
            lt_lo,
            _marker: Default::default(),
        }
    }

    pub(crate) fn expr(&self) -> Expression<F> {
        let (hi_lt, hi_eq) = self.comparison_hi.expr();
        hi_lt + hi_eq * self.lt_lo.expr()
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        lhs: Word,
        rhs: Word,
    ) -> Result<(), Error> {
        let (lhs_lo, lhs_hi) = split_u256(&lhs);
        let (rhs_lo, rhs_hi) = split_u256(&rhs);
        self.comparison_hi.assign(
            region,
            offset,
            F::from_u128(lhs_hi.as_u128()),
            F::from_u128(rhs_hi.as_u128()),
        )?;
        self.lt_lo.assign(
            region,
            offset,
            F::from_u128(lhs_lo.as_u128()),
            F::from_u128(rhs_lo.as_u128()),
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        evm_circuit::util::constraint_builder::ConstrainBuilderCommon, util::word::Word32Cell,
    };

    use super::{test_util::*, *};
    use eth_types::*;
    use halo2_proofs::{halo2curves::bn256::Fr, plonk::Error};

    #[derive(Clone)]
    /// LtWordTestContainer: require(a < b)
    struct LtWordTestContainer<F> {
        ltword_gadget: LtWordGadget<F, Word32Cell<F>, Word32Cell<F>>,
        a: Word32Cell<F>,
        b: Word32Cell<F>,
    }

    impl<F: Field> MathGadgetContainer<F> for LtWordTestContainer<F> {
        fn configure_gadget_container(cb: &mut EVMConstraintBuilder<F>) -> Self {
            let a = cb.query_word32();
            let b = cb.query_word32();
            let ltword_gadget = LtWordGadget::<F>::construct(cb, &a, &b);
            cb.require_equal("a < b", ltword_gadget.expr(), 1.expr());
            LtWordTestContainer {
                ltword_gadget,
                a,
                b,
            }
        }

        fn assign_gadget_container(
            &self,
            witnesses: &[Word],
            region: &mut CachedRegion<'_, '_, F>,
        ) -> Result<(), Error> {
            let a = witnesses[0];
            let b = witnesses[1];
            let offset = 0;

            self.a.assign(region, offset, Some(a.to_le_bytes()))?;
            self.b.assign(region, offset, Some(b.to_le_bytes()))?;
            self.ltword_gadget.assign(region, 0, a, b)?;

            Ok(())
        }
    }

    #[test]
    fn test_ltword_expect() {
        try_test!(
            LtWordTestContainer<Fr>,
            vec![Word::from(0), Word::from(1)],
            true,
        );
        try_test!(
            LtWordTestContainer<Fr>,
            vec![Word::from(1), Word::MAX],
            true,
        );
        try_test!(
            LtWordTestContainer<Fr>,
            vec![WORD_LOW_MAX, WORD_HIGH_MAX],
            true,
        );
        try_test!(
            LtWordTestContainer<Fr>,
            vec![Word::from(90), WORD_LOW_MAX],
            true,
        );
        try_test!(
            LtWordTestContainer<Fr>,
            vec![Word::from(90), WORD_HIGH_MAX],
            true,
        );
    }

    #[test]
    fn test_ltword_unexpect() {
        try_test!(
            LtWordTestContainer<Fr>,
            vec![Word::from(1), Word::from(0)],
            false,
        );
        try_test!(LtWordTestContainer<Fr>, vec![Word::MAX, Word::MAX], false,);

        try_test!(
            LtWordTestContainer<Fr>,
            vec![WORD_HIGH_MAX, WORD_LOW_MAX],
            false,
        );
    }
}
