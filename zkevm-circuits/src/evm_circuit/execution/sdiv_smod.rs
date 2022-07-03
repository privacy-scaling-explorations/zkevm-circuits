use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        step::ExecutionState,
        util::{
            self,
            common_gadget::SameContextGadget,
            constraint_builder::{ConstraintBuilder, StepStateTransition, Transition::Delta},
            math_gadget::{AbsWordGadget, IsZeroGadget, LtGadget, LtWordGadget, MulAddWordsGadget},
            select, sum, CachedRegion,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    util::Expr,
};
use bus_mapping::evm::OpcodeId;
use eth_types::{Field, ToLittleEndian, U256};
use halo2_proofs::plonk::Error;

#[derive(Clone, Debug)]
pub(crate) struct SignedDivModGadget<F> {
    same_context: SameContextGadget<F>,
    quotient: util::Word<F>,
    divisor: util::Word<F>,
    remainder: util::Word<F>,
    dividend: util::Word<F>,
    quotient_abs: util::Word<F>,
    divisor_abs: util::Word<F>,
    remainder_abs: util::Word<F>,
    dividend_abs: util::Word<F>,
    mul_add_words: MulAddWordsGadget<F>,
    remainder_abs_lt_divisor_abs: LtWordGadget<F>,
    dividend_is_signed_overflow: LtGadget<F, 1>,
    quotient_is_zero: IsZeroGadget<F>,
    divisor_is_zero: IsZeroGadget<F>,
    remainder_is_zero: IsZeroGadget<F>,
    abs_words: [AbsWordGadget<F>; 4],
}

impl<F: Field> ExecutionGadget<F> for SignedDivModGadget<F> {
    const NAME: &'static str = "SDIV_SMOD";

    const EXECUTION_STATE: ExecutionState = ExecutionState::SDIV_SMOD;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        let opcode = cb.query_cell();
        let is_sdiv = (OpcodeId::SMOD.expr() - opcode.expr()) * F::from(2).invert().unwrap();

        let quotient = cb.query_word();
        let divisor = cb.query_word();
        let remainder = cb.query_word();
        let dividend = cb.query_word();
        let quotient_abs = cb.query_word();
        let divisor_abs = cb.query_word();
        let remainder_abs = cb.query_word();
        let dividend_abs = cb.query_word();
        let quotient_is_zero = IsZeroGadget::construct(cb, sum::expr(&quotient_abs.cells));
        let divisor_is_zero = IsZeroGadget::construct(cb, sum::expr(&divisor_abs.cells));
        let remainder_is_zero = IsZeroGadget::construct(cb, sum::expr(&remainder_abs.cells));

        let abs_words = [
            AbsWordGadget::construct(cb, &quotient_abs),
            AbsWordGadget::construct(cb, &divisor_abs),
            AbsWordGadget::construct(cb, &remainder_abs),
            AbsWordGadget::construct(cb, &dividend_abs),
        ];

        cb.stack_pop(abs_words[3].x.expr());
        cb.stack_pop(abs_words[1].x.expr());
        cb.stack_push(select::expr(
            is_sdiv,
            abs_words[0].x.expr() * (1.expr() - divisor_is_zero.expr()),
            abs_words[2].x.expr() * (1.expr() - divisor_is_zero.expr()),
        ));

        // Constrain `|quotient| * |divisor| + |remainder| = |dividend|`.
        let mul_add_words = MulAddWordsGadget::construct(
            cb,
            [&quotient_abs, &divisor_abs, &remainder_abs, &dividend_abs],
        );
        cb.add_constraint("overflow == 0", mul_add_words.overflow());

        let remainder_abs_lt_divisor_abs =
            LtWordGadget::construct(cb, &remainder_abs, &divisor_abs);
        cb.add_constraint(
            "abs(remainder) < abs(divisor) when divisor != 0",
            (1.expr() - remainder_abs_lt_divisor_abs.expr()) * (1.expr() - divisor_is_zero.expr()),
        );

        cb.condition(
            (1.expr() - quotient_is_zero.expr())
            * (1.expr() - divisor_is_zero.expr())
            * (1.expr() - remainder_is_zero.expr()),
            |cb| cb.add_constraint(
                "sign(dividend) == sign(remainder) when quotient != 0, divisor != 0 and remainder != 0",
                abs_words[3].sign_check.expr() - abs_words[2].sign_check.expr(),
            )
        );

        // For a special `SDIV` case, when input `dividend = -(1 << 255)` and
        // `divisor = -1`, the quotient result should be `1 << 255`. But a
        // `signed` word could only express `signed` value from `-(1 << 255)` to
        // `(1 << 255) - 1`. So below constraint
        // `sign(dividend) == sign(divisor) ^ sign(quotient)` cannot be applied
        // for this case.
        let dividend_is_signed_overflow =
            LtGadget::construct(cb, 127.expr(), dividend_abs.cells[31].expr());

        // Constrain sign(dividend) == sign(divisor) ^ sign(quotient) when both
        // quotient and divisor are non-zero and dividend is not signed overflow.
        cb.condition(
            (1.expr() - quotient_is_zero.expr())
                * (1.expr() - divisor_is_zero.expr())
                * (1.expr() - dividend_is_signed_overflow.expr()),
            |cb| {
                cb.add_constraint(
                    "sign(dividend) == sign(divisor) ^ sign(quotient)",
                    1.expr() - abs_words[0].sign_check.expr() - abs_words[1].sign_check.expr()
                        + abs_words[3].sign_check.expr()
                        - 2.expr()
                            * (1.expr() - abs_words[0].sign_check.expr())
                            * (1.expr() - abs_words[1].sign_check.expr()),
                )
            },
        );

        let step_state_transition = StepStateTransition {
            rw_counter: Delta(3.expr()),
            program_counter: Delta(1.expr()),
            stack_pointer: Delta(1.expr()),
            gas_left: Delta(-OpcodeId::SDIV.constant_gas_cost().expr()),
            ..Default::default()
        };
        let same_context = SameContextGadget::construct(cb, opcode, step_state_transition);

        Self {
            same_context,
            quotient,
            divisor,
            remainder,
            dividend,
            quotient_abs,
            divisor_abs,
            remainder_abs,
            dividend_abs,
            mul_add_words,
            remainder_abs_lt_divisor_abs,
            dividend_is_signed_overflow,
            quotient_is_zero,
            divisor_is_zero,
            remainder_is_zero,
            abs_words,
        }
    }

    fn assign_exec_step(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        block: &Block<F>,
        _: &Transaction,
        _: &Call,
        step: &ExecStep,
    ) -> Result<(), Error> {
        self.same_context.assign_exec_step(region, offset, step)?;
        let indices = [step.rw_indices[0], step.rw_indices[1], step.rw_indices[2]];
        let [pop1, pop2, push] = indices.map(|idx| block.rws[idx].stack_value());
        let pop1_abs = get_abs(pop1);
        let pop2_abs = get_abs(pop2);
        let push_abs = get_abs(push);
        let is_pop1_neg = is_neg(pop1);
        let is_pop2_neg = is_neg(pop2);
        let (quotient, divisor, remainder, dividend) = match step.opcode.unwrap() {
            OpcodeId::SDIV => (
                push,
                pop2,
                if is_pop1_neg {
                    get_neg(pop1_abs - push_abs * pop2_abs)
                } else {
                    pop1_abs - push_abs * pop2_abs
                },
                pop1,
            ),
            OpcodeId::SMOD => (
                if pop2.is_zero() {
                    U256::from(0)
                } else if is_pop1_neg == is_pop2_neg {
                    pop1_abs / pop2_abs
                } else {
                    get_neg(pop1_abs / pop2_abs)
                },
                pop2,
                if pop2.is_zero() { pop1 } else { push },
                pop1,
            ),
            _ => unreachable!(),
        };
        let quotient_abs = get_abs(quotient);
        let divisor_abs = get_abs(divisor);
        let remainder_abs = get_abs(remainder);
        let dividend_abs = get_abs(dividend);
        self.quotient
            .assign(region, offset, Some(quotient.to_le_bytes()))?;
        self.divisor
            .assign(region, offset, Some(quotient.to_le_bytes()))?;
        self.remainder
            .assign(region, offset, Some(remainder.to_le_bytes()))?;
        self.dividend
            .assign(region, offset, Some(dividend.to_le_bytes()))?;
        self.quotient_abs
            .assign(region, offset, Some(quotient_abs.to_le_bytes()))?;
        self.divisor_abs
            .assign(region, offset, Some(divisor_abs.to_le_bytes()))?;
        self.remainder_abs
            .assign(region, offset, Some(remainder_abs.to_le_bytes()))?;
        self.dividend_abs
            .assign(region, offset, Some(dividend_abs.to_le_bytes()))?;
        self.mul_add_words.assign(
            region,
            offset,
            [quotient_abs, divisor_abs, remainder_abs, dividend_abs],
        )?;
        self.remainder_abs_lt_divisor_abs
            .assign(region, offset, remainder_abs, divisor_abs)?;
        self.dividend_is_signed_overflow.assign(
            region,
            offset,
            127.into(),
            u64::from(dividend_abs.to_le_bytes()[31]).into(),
        )?;
        let quotient_sum = (0..32).fold(0, |acc, idx| acc + quotient_abs.byte(idx) as u64);
        let divisor_sum = (0..32).fold(0, |acc, idx| acc + divisor_abs.byte(idx) as u64);
        let remainder_sum = (0..32).fold(0, |acc, idx| acc + remainder_abs.byte(idx) as u64);
        self.quotient_is_zero
            .assign(region, offset, F::from(quotient_sum))?;
        self.divisor_is_zero
            .assign(region, offset, F::from(divisor_sum))?;
        self.remainder_is_zero
            .assign(region, offset, F::from(remainder_sum))?;
        self.abs_words[0].assign(region, offset, quotient)?;
        self.abs_words[1].assign(region, offset, divisor)?;
        self.abs_words[2].assign(region, offset, remainder)?;
        self.abs_words[3].assign(region, offset, dividend)
    }
}

#[inline]
fn get_abs(x: U256) -> U256 {
    if is_neg(x) {
        get_neg(x)
    } else {
        x
    }
}

#[inline]
fn get_neg(x: U256) -> U256 {
    if x.is_zero() {
        x
    } else {
        U256::from_big_endian(&[255u8; 32]) - x + U256::from(1)
    }
}

#[inline]
fn is_neg(x: U256) -> bool {
    127 < x.to_le_bytes()[31]
}

#[cfg(test)]
mod test {
    use crate::{evm_circuit::test::rand_word, test_util::run_test_circuits};
    use eth_types::evm_types::OpcodeId;
    use eth_types::{bytecode, Word};
    use mock::TestContext;

    fn test_ok(opcode: OpcodeId, a: Word, b: Word) {
        let bytecode = bytecode! {
            PUSH32(b)
            PUSH32(a)
            #[start]
            .write_op(opcode)
            STOP
        };
        assert_eq!(
            run_test_circuits(
                TestContext::<2, 1>::simple_ctx_with_bytecode(bytecode).unwrap(),
                None
            ),
            Ok(())
        );
    }

    #[test]
    fn sdiv_gadget_simple() {
        test_ok(OpcodeId::SDIV, 0xFFFFFF.into(), 0xABC.into());
        test_ok(OpcodeId::SDIV, 0xABC.into(), 0xFFFFFF.into());
        test_ok(OpcodeId::SDIV, 0xFFFFFF.into(), 0xFFFFFFF.into());
        test_ok(OpcodeId::SDIV, 0xABC.into(), 0.into());
        test_ok(
            OpcodeId::SDIV,
            Word::from_big_endian(&[255u8; 32]),
            0xABCDEF.into(),
        );
        test_ok(
            OpcodeId::SDIV,
            0xABCDEF.into(),
            Word::from_big_endian(&[255u8; 32]),
        );
        let mut x = [0u8; 32];
        x[31] = 128u8;
        test_ok(
            OpcodeId::SDIV,
            Word::from_big_endian(&x),
            Word::from_big_endian(&[255u8; 32]),
        );
    }

    #[test]
    fn sdiv_gadget_rand() {
        let dividend = rand_word();
        let divisor = rand_word();
        test_ok(OpcodeId::SDIV, dividend, divisor);
    }

    #[test]
    fn smod_gadget_simple() {
        test_ok(OpcodeId::SMOD, 0xFFFFFF.into(), 0xABC.into());
        test_ok(OpcodeId::SMOD, 0xABC.into(), 0xFFFFFF.into());
        test_ok(OpcodeId::SMOD, 0xFFFFFF.into(), 0xFFFFFFF.into());
        test_ok(OpcodeId::SMOD, 0xABC.into(), 0.into());
        test_ok(
            OpcodeId::SMOD,
            Word::from_big_endian(&[255u8; 32]),
            0xABCDEF.into(),
        );
        test_ok(
            OpcodeId::SMOD,
            0xABCDEF.into(),
            Word::from_big_endian(&[255u8; 32]),
        );
        let mut x = [0u8; 32];
        x[31] = 128u8;
        test_ok(
            OpcodeId::SMOD,
            Word::from_big_endian(&x),
            Word::from_big_endian(&[255u8; 32]),
        );
    }

    #[test]
    fn smod_gadget_rand() {
        let dividend = rand_word();
        let divisor = rand_word();
        test_ok(OpcodeId::SMOD, dividend, divisor);
    }
}
