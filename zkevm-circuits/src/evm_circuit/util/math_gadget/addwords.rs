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
pub(crate) struct AddWordsGadget<F, const N_ADDENDS: usize, const CHECK_OVREFLOW: bool> {
    addends: [util::Word<F>; N_ADDENDS],
    sum: util::Word<F>,
    carry_lo: Cell<F>,
    carry_hi: Option<Cell<F>>,
}

impl<F: Field, const N_ADDENDS: usize, const CHECK_OVREFLOW: bool>
    AddWordsGadget<F, N_ADDENDS, CHECK_OVREFLOW>
{
    pub(crate) fn construct(
        cb: &mut ConstraintBuilder<F>,
        addends: [util::Word<F>; N_ADDENDS],
        sum: util::Word<F>,
    ) -> Self {
        let carry_lo = cb.query_cell();
        let carry_hi = if CHECK_OVREFLOW {
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
            if CHECK_OVREFLOW {
                "sum(addends_hi) + carry_lo == sum_hi"
            } else {
                "sum(addends_hi) + carry_lo == sum_hi + carry_hi ⋅ 2^128"
            },
            sum::expr(addends_hi) + carry_lo.expr(),
            if CHECK_OVREFLOW {
                sum_hi
            } else {
                sum_hi + carry_hi.as_ref().unwrap().expr() * pow_of_two_expr(128)
            },
        );

        for carry in if CHECK_OVREFLOW {
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

        if !CHECK_OVREFLOW {
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

mod tests {
    use super::util::math_gadget::tests::*;
    use super::*;
    use eth_types::Word;
    use halo2_proofs::halo2curves::bn256::Fr;
    use halo2_proofs::plonk::Error;

    #[test]
    fn test_addwords() {
        #[derive(Clone)]
        /// sum = a + b
        struct AddWordsTestContainer<F> {
            addwords_gadget: AddWordsGadget<F, 2, true>,
            a: util::Word<F>,
            b: util::Word<F>,
            sum: util::Word<F>,
        }

        impl<F: Field> MathGadgetContainer<F> for AddWordsTestContainer<F> {
            const NAME: &'static str = "AddWordsGadget";

            fn configure_gadget_container(cb: &mut ConstraintBuilder<F>) -> Self {
                let a = cb.query_word();
                let b = cb.query_word();
                let sum = cb.query_word();
                let addwords_gadget = AddWordsGadget::<F, 2, true>::construct(
                    cb,
                    [a.clone(), b.clone()],
                    sum.clone(),
                );
                AddWordsTestContainer {
                    addwords_gadget,
                    a,
                    b,
                    sum,
                }
            }

            fn assign_gadget_container(
                &self,
                input_words: &[Word],
                region: &mut CachedRegion<'_, '_, F>,
            ) -> Result<(), Error> {
                let a = input_words[0];
                let b = input_words[1];
                let sum = input_words[2];
                let offset = 0;

                self.a.assign(region, offset, Some(a.to_le_bytes()))?;
                self.b.assign(region, offset, Some(b.to_le_bytes()))?;
                self.sum.assign(region, offset, Some(sum.to_le_bytes()))?;
                self.addwords_gadget.assign(region, 0, [a, b], sum)?;

                Ok(())
            }
        }

        test_math_gadget_container::<Fr, AddWordsTestContainer<Fr>>(
            vec![Word::from(0), Word::from(0), Word::from(0)],
            true,
        );

        test_math_gadget_container::<Fr, AddWordsTestContainer<Fr>>(
            vec![Word::from(1), Word::from(1), Word::from(2)],
            true,
        );

        test_math_gadget_container::<Fr, AddWordsTestContainer<Fr>>(
            vec![Word::from(1000), Word::from(1000), Word::from(2000)],
            true,
        );

        test_math_gadget_container::<Fr, AddWordsTestContainer<Fr>>(
            vec![Word::MAX - 1, Word::from(1), Word::MAX],
            true,
        );

        test_math_gadget_container::<Fr, AddWordsTestContainer<Fr>>(
            vec![Word::MAX, Word::from(1), Word::from(0)],
            false,
        );

        test_math_gadget_container::<Fr, AddWordsTestContainer<Fr>>(
            vec![Word::from(1), Word::from(0), Word::from(0)],
            false,
        );

        test_math_gadget_container::<Fr, AddWordsTestContainer<Fr>>(
            vec![Word::from(0), Word::from(1), Word::from(0)],
            false,
        );
    }
}
