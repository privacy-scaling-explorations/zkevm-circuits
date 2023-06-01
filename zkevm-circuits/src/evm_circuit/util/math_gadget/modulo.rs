use crate::{
    evm_circuit::util::{
        constraint_builder::{ConstrainBuilderCommon, EVMConstraintBuilder},
        math_gadget::{LtWordGadgetNew as LtWordGadget, *},
        CachedRegion, Word as WordLegacy,
    },
    util::{
        word::{self, Word32Cell},
        Expr,
    },
};
use eth_types::{Field, ToLittleEndian, Word};
use halo2_proofs::{circuit::Value, plonk::Error};

/// Constraints for the words a, n, r:
/// a mod n = r, if n!=0
/// r = 0,       if n==0
///
/// We use the auxiliary a_or_zero word, whose value is constrained to be:
/// a_or_zero = a if n!=0, 0 if n==0.  This allows to use the equation
/// k * n + r = a_or_zero to verify the modulus, which holds with r=0 in the
/// case of n=0. Unlike the usual k * n + r = a, which forces r = a when n=0,
/// this equation assures that r<n or r=n=0.
#[derive(Clone, Debug)]
pub(crate) struct ModGadget<F> {
    k: Word32Cell<F>,
    a_or_zero: Word32Cell<F>,
    mul_add_words: MulAddWordsGadget<F>,
    n_is_zero: IsZeroWordGadget<F, Word32Cell<F>>,
    a_or_is_zero: IsZeroWordGadget<F, Word32Cell<F>>,
    eq: IsEqualWordGadget<F, Word32Cell<F>, Word32Cell<F>>,
    lt: LtWordGadget<F, Word32Cell<F>, Word32Cell<F>>,
}
impl<F: Field> ModGadget<F> {
    pub(crate) fn construct(
        _cb: &mut EVMConstraintBuilder<F>,
        _words: [&WordLegacy<F>; 3],
    ) -> Self {
        todo!()
    }

    pub(crate) fn construct_new(
        cb: &mut EVMConstraintBuilder<F>,
        words: [&Word32Cell<F>; 3],
    ) -> Self {
        let (a, n, r) = (words[0], words[1], words[2]);
        let k = cb.query_word32();
        let a_or_zero = cb.query_word32();
        let n_is_zero = IsZeroWordGadget::construct(cb, n.clone());
        let a_or_is_zero = IsZeroWordGadget::construct(cb, a_or_zero.clone());
        let mul_add_words = MulAddWordsGadget::construct_new(cb, [&k, n, r, &a_or_zero]);
        let eq = IsEqualWordGadget::construct(cb, a.clone(), a_or_zero.clone());
        let lt = LtWordGadget::construct(cb, r.clone(), n.clone());
        // Constrain the aux variable a_or_zero to be =a or =0 if n==0:
        // (a == a_or_zero) ^ (n == 0 & a_or_zero == 0)
        cb.add_constraint(
            " (1 - (a == a_or_zero)) * ( 1 - (n == 0) * (a_or_zero == 0)",
            (1.expr() - eq.expr()) * (1.expr() - n_is_zero.expr() * a_or_is_zero.expr()),
        );

        // Constrain the result r to be valid: (r<n) ^ n==0
        cb.add_constraint(
            " (1 - (r<n) - (n==0) ",
            1.expr() - lt.expr() - n_is_zero.expr(),
        );

        // Constrain k * n + r no overflow
        cb.add_constraint("overflow == 0 for k * n + r", mul_add_words.overflow());

        Self {
            k,
            a_or_zero,
            mul_add_words,
            n_is_zero,
            a_or_is_zero,
            eq,
            lt,
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        a: Word,
        n: Word,
        r: Word,
        k: Word,
    ) -> Result<(), Error> {
        let a_or_zero = if n.is_zero() { Word::zero() } else { a };

        self.k.assign(region, offset, Some(k.to_le_bytes()))?;
        self.a_or_zero
            .assign(region, offset, Some(a_or_zero.to_le_bytes()))?;
        let n_sum = (0..32).fold(0, |acc, idx| acc + n.byte(idx) as u64);
        self.n_is_zero
            .assign(region, offset, word::Word::from_u64(n_sum))?;
        self.a_or_is_zero
            .assign(region, offset, word::Word::from_u256(a_or_zero))?;
        self.mul_add_words
            .assign(region, offset, [k, n, r, a_or_zero])?;
        self.lt.assign(region, offset, r, n)?;
        self.eq.assign_value(
            region,
            offset,
            Value::known(word::Word::from_u256(a)),
            Value::known(word::Word::from_u256(a_or_zero)),
        )?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::{test_util::*, *};
    use eth_types::{Word, U256, U512};
    use halo2_proofs::{halo2curves::bn256::Fr, plonk::Error};

    #[derive(Clone)]
    /// ModGadgetTestContainer: require(a % n == r)
    struct ModGadgetTestContainer<F> {
        mod_gadget: ModGadget<F>,
        a: Word32Cell<F>,
        n: Word32Cell<F>,
        r: Word32Cell<F>,
    }

    impl<F: Field> MathGadgetContainer<F> for ModGadgetTestContainer<F> {
        fn configure_gadget_container(cb: &mut EVMConstraintBuilder<F>) -> Self {
            let a = cb.query_word32();
            let n = cb.query_word32();
            let r = cb.query_word32();
            let mod_gadget = ModGadget::<F>::construct_new(cb, [&a, &n, &r]);
            ModGadgetTestContainer {
                mod_gadget,
                a,
                n,
                r,
            }
        }

        fn assign_gadget_container(
            &self,
            witnesses: &[Word],
            region: &mut CachedRegion<'_, '_, F>,
        ) -> Result<(), Error> {
            let a = witnesses[0];
            let n = witnesses[1];
            let r = witnesses[2];
            let k =
                witnesses
                    .get(3)
                    .copied()
                    .unwrap_or(if n.is_zero() { Word::zero() } else { a / n });

            let offset = 0;

            self.a.assign(region, offset, Some(a.to_le_bytes()))?;
            self.n.assign(region, offset, Some(n.to_le_bytes()))?;
            self.r.assign(region, offset, Some(r.to_le_bytes()))?;

            self.mod_gadget.assign(region, 0, a, n, r, k)
        }
    }

    #[test]
    fn test_mod_n_expected_rem() {
        try_test!(
            ModGadgetTestContainer<Fr>,
            vec![Word::from(0), Word::from(0), Word::from(0)],
            true,
        );
        try_test!(
            ModGadgetTestContainer<Fr>,
            vec![Word::from(1), Word::from(0), Word::from(0)],
            true,
        );
        try_test!(
            ModGadgetTestContainer<Fr>,
            vec![Word::from(548), Word::from(50), Word::from(48)],
            true,
        );
        try_test!(
            ModGadgetTestContainer<Fr>,
            vec![Word::from(30), Word::from(50), Word::from(30)],
            true,
        );
        try_test!(
            ModGadgetTestContainer<Fr>,
            vec![WORD_LOW_MAX, Word::from(1024), Word::from(1023)],
            true,
        );
        try_test!(
            ModGadgetTestContainer<Fr>,
            vec![WORD_HIGH_MAX, Word::from(1024), Word::from(0)],
            true,
        );
        try_test!(
            ModGadgetTestContainer<Fr>,
            vec![WORD_CELL_MAX, Word::from(2), Word::from(0)],
            true,
        );
    }

    #[test]
    fn test_mod_n_unexpected_rem() {
        // test soundness by manipulating k to make a' = k * n + r and a' >=
        // 2^256 cause overflow and trigger soundness bug: (a' != a) ^ a' ≡ a
        // (mod 2^256)
        // Here, the attacker tries to convince you of a false statement `2 % 3 = 0` by
        // showing you `2 = ((2^256 + 2) / 3) * 3 + 0`. In the `MulAddWordsGadget`, `k *
        // n + r = a  (modulo 2**256)` would have been a valid statement. But the gadget
        // would have the overflow = 1. Since we constrain the overflow to be 0 in the
        // ModGadget, the statement would be invalid in the ModGadget.
        try_test!(
            ModGadgetTestContainer<Fr>,
            vec![
                Word::from(2),
                Word::from(3),
                Word::from(0),
                // magic number (2^256 + 2) / 3, and 2^256 + 2 is divisible by 3
                U256::try_from(U512([2, 0, 0, 0, 1, 0, 0, 0]) / U512::from(3)).unwrap(),
            ],
            false,
        );
        try_test!(
            ModGadgetTestContainer<Fr>,
            vec![Word::from(1), Word::from(1), Word::from(1)],
            false,
        );
        try_test!(
            ModGadgetTestContainer<Fr>,
            vec![Word::from(46), Word::from(50), Word::from(48)],
            false,
        );
        try_test!(
            ModGadgetTestContainer<Fr>,
            vec![WORD_LOW_MAX, Word::from(999999), Word::from(888888)],
            false,
        );
        try_test!(
            ModGadgetTestContainer<Fr>,
            vec![WORD_CELL_MAX, Word::from(999999999), Word::from(666666666)],
            false,
        );
        try_test!(
            ModGadgetTestContainer<Fr>,
            vec![WORD_HIGH_MAX, Word::from(999999), Word::from(777777)],
            false,
        );
    }
}
