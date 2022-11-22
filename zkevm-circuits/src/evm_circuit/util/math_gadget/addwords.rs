use super::CachedRegion;
use crate::{
    evm_circuit::util::{
        self, constraint_builder::ConstraintBuilder, from_bytes, pow_of_two_expr, split_u256, sum,
        Cell,
    },
    util::Expr,
};
use eth_types::{Field, ToLittleEndian, ToScalar, Word};
use halo2_proofs::{circuit::Value, plonk::Error};

/// Construction of 2 256-bit words addition and result, which is useful for
/// opcode ADD, SUB and balance operation
#[derive(Clone, Debug)]
pub(crate) struct AddWordsGadget<F, const N_ADDENDS: usize, const CHECK_OVERFLOW: bool> {
    addends: [util::Word<F>; N_ADDENDS],
    sum: util::Word<F>,
    carry_lo: Cell<F>,
    carry_hi: Option<Cell<F>>,
}

impl<F: Field, const N_ADDENDS: usize, const CHECK_OVERFLOW: bool>
    AddWordsGadget<F, N_ADDENDS, CHECK_OVERFLOW>
{
    pub(crate) fn construct(
        cb: &mut ConstraintBuilder<F>,
        addends: [util::Word<F>; N_ADDENDS],
        sum: util::Word<F>,
    ) -> Self {
        let carry_lo = cb.query_cell();
        let carry_hi = if CHECK_OVERFLOW {
            None
        } else {
            Some(cb.query_cell())
        };

        let addends_lo = &addends
            .iter()
            .map(|addend| from_bytes::expr(&addend.cells[..16]))
            .collect::<Vec<_>>();
        let addends_hi = &addends
            .iter()
            .map(|addend| from_bytes::expr(&addend.cells[16..]))
            .collect::<Vec<_>>();
        let sum_lo = from_bytes::expr(&sum.cells[..16]);
        let sum_hi = from_bytes::expr(&sum.cells[16..]);

        cb.require_equal(
            "sum(addends_lo) == sum_lo + carry_lo ⋅ 2^128",
            sum::expr(addends_lo),
            sum_lo + carry_lo.expr() * pow_of_two_expr(128),
        );
        cb.require_equal(
            if CHECK_OVERFLOW {
                "sum(addends_hi) + carry_lo == sum_hi"
            } else {
                "sum(addends_hi) + carry_lo == sum_hi + carry_hi ⋅ 2^128"
            },
            sum::expr(addends_hi) + carry_lo.expr(),
            if CHECK_OVERFLOW {
                sum_hi
            } else {
                sum_hi + carry_hi.as_ref().unwrap().expr() * pow_of_two_expr(128)
            },
        );

        for carry in if CHECK_OVERFLOW {
            vec![&carry_lo]
        } else {
            vec![&carry_lo, carry_hi.as_ref().unwrap()]
        } {
            cb.require_in_set(
                "carry_lo in 0..N_ADDENDS",
                carry.expr(),
                (0..N_ADDENDS).map(|idx| idx.expr()).collect(),
            );
        }

        Self {
            addends,
            sum,
            carry_lo,
            carry_hi,
        }
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        addends: [Word; N_ADDENDS],
        sum: Word,
    ) -> Result<(), Error> {
        for (word, value) in self.addends.iter().zip(addends.iter()) {
            word.assign(region, offset, Some(value.to_le_bytes()))?;
        }
        self.sum.assign(region, offset, Some(sum.to_le_bytes()))?;

        let (addends_lo, addends_hi): (Vec<_>, Vec<_>) = addends.iter().map(split_u256).unzip();
        let (sum_lo, sum_hi) = split_u256(&sum);

        let sum_of_addends_lo = addends_lo
            .into_iter()
            .fold(Word::zero(), |acc, addend_lo| acc + addend_lo);
        let sum_of_addends_hi = addends_hi
            .into_iter()
            .fold(Word::zero(), |acc, addend_hi| acc + addend_hi);

        let carry_lo = (sum_of_addends_lo - sum_lo) >> 128;
        self.carry_lo.assign(
            region,
            offset,
            Value::known(
                carry_lo
                    .to_scalar()
                    .expect("unexpected U256 -> Scalar conversion failure"),
            ),
        )?;

        if !CHECK_OVERFLOW {
            let carry_hi = (sum_of_addends_hi + carry_lo - sum_hi) >> 128;
            self.carry_hi.as_ref().unwrap().assign(
                region,
                offset,
                Value::known(
                    carry_hi
                        .to_scalar()
                        .expect("unexpected U256 -> Scalar conversion failure"),
                ),
            )?;
        }

        Ok(())
    }

    pub(crate) fn addends(&self) -> &[util::Word<F>] {
        &self.addends
    }

    pub(crate) fn sum(&self) -> &util::Word<F> {
        &self.sum
    }

    pub(crate) fn carry(&self) -> &Option<util::Cell<F>> {
        &self.carry_hi
    }
}

#[cfg(test)]
mod tests {
    use super::super::test_util::*;
    use super::*;
    use eth_types::Word;
    use halo2_proofs::halo2curves::bn256::Fr;
    use halo2_proofs::plonk::Error;

    #[derive(Clone)]
    /// sum = a + b
    struct AddWordsTestContainer<F, const N_ADDENDS: usize, const CHECK_OVERFLOW: bool> {
        addwords_gadget: AddWordsGadget<F, N_ADDENDS, CHECK_OVERFLOW>,
        addends: [util::Word<F>; N_ADDENDS],
        sum: util::Word<F>,
    }

    impl<F: Field, const N_ADDENDS: usize, const CHECK_OVERFLOW: bool> MathGadgetContainer<F>
        for AddWordsTestContainer<F, N_ADDENDS, CHECK_OVERFLOW>
    {
        const NAME: &'static str = "AddWordsGadget";

        fn configure_gadget_container(cb: &mut ConstraintBuilder<F>) -> Self {
            let addends = [(); N_ADDENDS].map(|_| cb.query_word());
            let sum = cb.query_word();
            let addwords_gadget = AddWordsGadget::<F, N_ADDENDS, CHECK_OVERFLOW>::construct(
                cb,
                addends.clone(),
                sum.clone(),
            );
            AddWordsTestContainer {
                addwords_gadget,
                addends,
                sum,
            }
        }

        fn assign_gadget_container(
            &self,
            input_words: &[Word],
            region: &mut CachedRegion<'_, '_, F>,
        ) -> Result<(), Error> {
            assert_eq!(N_ADDENDS, input_words.len() - 1);
            let offset = 0;
            for (i, addend) in self.addends.iter().enumerate() {
                let a = input_words[i];
                addend.assign(region, offset, Some(a.to_le_bytes()))?;
            }
            let sum = input_words[N_ADDENDS];
            self.sum.assign(region, offset, Some(sum.to_le_bytes()))?;

            let addends = input_words[0..N_ADDENDS].try_into().unwrap();
            self.addwords_gadget.assign(region, 0, addends, sum)?;

            Ok(())
        }
    }

    #[test]
    fn test_add_0_0() {
        test_math_gadget_container::<Fr, AddWordsTestContainer<Fr, 2, true>>(
            vec![Word::from(0), Word::from(0), Word::from(0)],
            true,
        );
    }

    #[test]
    fn test_addwords_1_1() {
        test_math_gadget_container::<Fr, AddWordsTestContainer<Fr, 2, true>>(
            vec![Word::from(1), Word::from(1), Word::from(2)],
            true,
        );
    }

    #[test]
    fn test_addwords_1000_1000() {
        test_math_gadget_container::<Fr, AddWordsTestContainer<Fr, 2, true>>(
            vec![Word::from(1000), Word::from(1000), Word::from(2000)],
            true,
        );
    }

    #[test]
    fn test_addwords_to_wordmax() {
        test_math_gadget_container::<Fr, AddWordsTestContainer<Fr, 2, true>>(
            vec![Word::MAX - 1, Word::from(1), Word::MAX],
            true,
        );
    }

    #[test]
    fn test_addwords_overflow() {
        test_math_gadget_container::<Fr, AddWordsTestContainer<Fr, 2, true>>(
            vec![Word::MAX, Word::from(1), Word::from(0)],
            false,
        );
    }

    #[test]
    fn test_addwords_neq0() {
        test_math_gadget_container::<Fr, AddWordsTestContainer<Fr, 2, true>>(
            vec![Word::from(1), Word::from(0), Word::from(0)],
            false,
        );
    }

    #[test]
    fn test_addwords_neq2() {
        test_math_gadget_container::<Fr, AddWordsTestContainer<Fr, 2, true>>(
            vec![Word::from(2), Word::from(1), Word::from(2)],
            false,
        );
    }

    //non overflow check cases
    #[test]
    fn test_addwords_no_overflow_check() {
        test_math_gadget_container::<Fr, AddWordsTestContainer<Fr, 2, false>>(
            vec![Word::MAX, Word::from(1), Word::from(0)],
            true,
        );
    }

    #[test]
    fn test_addwords_3_addends() {
        test_math_gadget_container::<Fr, AddWordsTestContainer<Fr, 3, false>>(
            vec![Word::from(0), Word::from(1), Word::from(0), Word::from(1)],
            true,
        );
    }

    #[test]
    fn test_addwords_3_addends_with_overflow_check() {
        test_math_gadget_container::<Fr, AddWordsTestContainer<Fr, 3, true>>(
            vec![Word::MAX, Word::from(1), Word::from(0), Word::from(0)],
            false,
        );
    }

    #[test]
    fn test_addwords_3_addends_without_overflow_check() {
        test_math_gadget_container::<Fr, AddWordsTestContainer<Fr, 3, false>>(
            vec![Word::MAX, Word::from(1), Word::from(0), Word::from(0)],
            true,
        );
    }
}
