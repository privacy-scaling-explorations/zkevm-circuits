use crate::evm_circuit::util::{
    self, constraint_builder::EVMConstraintBuilder, math_gadget::*, select, CachedRegion,
};
use eth_types::{Field, Word};
use halo2_proofs::plonk::{Error, Expression};

/// Returns `rhs` when `lhs < rhs`, and returns `lhs` otherwise.
#[derive(Clone, Debug)]
pub struct MinMaxWordGadget<F> {
    lt: LtWordGadget<F>,
    min: Expression<F>,
    max: Expression<F>,
}

impl<F: Field> MinMaxWordGadget<F> {
    pub(crate) fn construct(
        cb: &mut EVMConstraintBuilder<F>,
        lhs: &util::Word<F>,
        rhs: &util::Word<F>,
    ) -> Self {
        let lt = LtWordGadget::construct(cb, lhs, rhs);
        let max = select::expr(lt.expr(), rhs.expr(), lhs.expr());
        let min = select::expr(lt.expr(), lhs.expr(), rhs.expr());

        Self { lt, min, max }
    }

    pub(crate) fn min(&self) -> Expression<F> {
        self.min.clone()
    }

    pub(crate) fn max(&self) -> Expression<F> {
        self.max.clone()
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        lhs: Word,
        rhs: Word,
    ) -> Result<(), Error> {
        self.lt.assign(region, offset, lhs, rhs)
    }
}

#[cfg(test)]
mod tests {
    use super::{test_util::*, *};
    use crate::evm_circuit::util::constraint_builder::ConstrainBuilderCommon;
    use eth_types::{ToLittleEndian, Word};
    use halo2_proofs::{halo2curves::bn256::Fr, plonk::Error};

    #[derive(Clone)]
    /// MinMaxTestContainer: require(min(a, b) == (a if MIN_IS_A else b))
    struct MinMaxWordTestContainer<F, const MIN_IS_A: bool> {
        minmax_word_gadget: MinMaxWordGadget<F>,
        a: util::Word<F>,
        b: util::Word<F>,
    }

    impl<F: Field, const MIN_IS_A: bool> MathGadgetContainer<F>
        for MinMaxWordTestContainer<F, MIN_IS_A>
    {
        fn configure_gadget_container(cb: &mut EVMConstraintBuilder<F>) -> Self {
            let a = cb.query_word_rlc();
            let b = cb.query_word_rlc();
            let minmax_word_gadget = MinMaxWordGadget::<F>::construct(cb, &a, &b);

            if MIN_IS_A {
                cb.require_equal("min == a", minmax_word_gadget.min(), a.expr());
                cb.require_equal("max == b", minmax_word_gadget.max(), b.expr());
            } else {
                cb.require_equal("min == b", minmax_word_gadget.min(), b.expr());
                cb.require_equal("max == a", minmax_word_gadget.max(), a.expr());
            }

            MinMaxWordTestContainer {
                minmax_word_gadget,
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
            self.minmax_word_gadget.assign(region, offset, a, b)?;

            Ok(())
        }
    }

    #[test]
    fn test_minmax_eq() {
        // a == b
        try_test!(
            MinMaxWordTestContainer<Fr, true>,
            vec![Word::from(0), Word::from(0)],
            true,
        );
        try_test!(
            MinMaxWordTestContainer<Fr, true>,
            vec![Word::from(5), Word::from(5)],
            true,
        );
        try_test!(
            MinMaxWordTestContainer<Fr, true>,
            vec![WORD_LOW_MAX, WORD_LOW_MAX],
            true,
        );
    }

    #[test]
    fn test_minmax_expect_min_a() {
        // min == a, max == b
        try_test!(
            MinMaxWordTestContainer<Fr, true>,
            vec![Word::from(0), Word::from(1)],
            true,
        );
        try_test!(
            MinMaxWordTestContainer<Fr, true>,
            vec![Word::from(3), Word::from(5)],
            true,
        );
        try_test!(
            MinMaxWordTestContainer<Fr, true>,
            vec![WORD_LOW_MAX, WORD_LOW_MAX],
            true,
        );
    }

    #[test]
    fn test_minmax_unexpect_min_a() {
        // min == b, max == a
        try_test!(
            MinMaxWordTestContainer<Fr, true>,
            vec![Word::from(1), Word::from(0)],
            false,
        );
        try_test!(
            MinMaxWordTestContainer<Fr, true>,
            vec![Word::from(256), Word::from(3)],
            false,
        );
        try_test!(
            MinMaxWordTestContainer<Fr, true>,
            vec![WORD_LOW_MAX, Word::from(123456)],
            false,
        );
    }

    #[test]
    fn test_minmax_expect_min_b() {
        // min == a, max == b
        try_test!(
            MinMaxWordTestContainer<Fr, false>,
            vec![Word::from(1), Word::from(0)],
            true,
        );

        try_test!(
            MinMaxWordTestContainer<Fr, false>,
            vec![Word::from(777), Word::from(44)],
            true,
        );

        try_test!(
            MinMaxWordTestContainer<Fr, false>,
            vec![WORD_LOW_MAX+1, WORD_LOW_MAX],
            true,
        );
    }
}
