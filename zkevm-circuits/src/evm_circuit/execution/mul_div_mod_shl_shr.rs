use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        step::ExecutionState,
        util::{
            self,
            common_gadget::SameContextGadget,
            constraint_builder::{ConstraintBuilder, StepStateTransition, Transition::Delta},
            math_gadget::{
                generate_lagrange_base_polynomial, IsZeroGadget, LtWordGadget, MulAddWordsGadget,
            },
            sum, CachedRegion, Cell,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    util::Expr,
};
use bus_mapping::evm::OpcodeId;
use eth_types::{Field, ToLittleEndian, U256};
use halo2_proofs::plonk::{Error, Expression};

/// MulDivModShlShrGadget verifies opcode MUL, DIV, MOD, SHL and SHR.
/// For MUL, verify pop1 * pop2 == push;
/// For DIV, verify pop1 / pop2 == push;
/// For MOD, verify pop1 % pop2 == push;
/// For SHL, verify pop1 * (2^pop2) == push;
/// For SHR, verify pop1 / (2^pop2) = push;
/// when pop1, pop2, push are 256-bit words.
#[derive(Clone, Debug)]
pub(crate) struct MulDivModShlShrGadget<F> {
    same_context: SameContextGadget<F>,
    quotient: util::Word<F>,
    divisor: util::Word<F>,
    remainder: util::Word<F>,
    dividend: util::Word<F>,
    /// Shift word used for opcode SHL and SHR
    pop1: util::Word<F>,
    /// Gadget that verifies quotient * divisor + remainder = dividend
    mul_add_words: MulAddWordsGadget<F>,
    /// Check if divisor is zero for opcode DIV, MOD and SHR
    divisor_is_zero: IsZeroGadget<F>,
    /// Check if remainder is zero for opcode MUL and SHL
    remainder_is_zero: IsZeroGadget<F>,
    /// Check if remainder < divisor when divisor != 0
    remainder_lt_divisor: LtWordGadget<F>,
}

impl<F: Field> ExecutionGadget<F> for MulDivModShlShrGadget<F> {
    const NAME: &'static str = "MUL_DIV_MOD_SHL_SHR";

    const EXECUTION_STATE: ExecutionState = ExecutionState::MUL_DIV_MOD_SHL_SHR;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        let opcode = cb.query_cell();
        let is_mul = is_opcode(&opcode, OpcodeId::MUL);
        let is_div = is_opcode(&opcode, OpcodeId::DIV);
        let is_mod = is_opcode(&opcode, OpcodeId::MOD);
        let is_shl = is_opcode(&opcode, OpcodeId::SHL);
        let is_shr = is_opcode(&opcode, OpcodeId::SHR);

        let quotient = cb.query_word();
        let divisor = cb.query_word();
        let remainder = cb.query_word();
        let dividend = cb.query_word();
        let pop1 = cb.query_word();

        let mul_add_words =
            MulAddWordsGadget::construct(cb, [&quotient, &divisor, &remainder, &dividend]);
        let divisor_is_zero = IsZeroGadget::construct(cb, sum::expr(&divisor.cells));
        let remainder_is_zero = IsZeroGadget::construct(cb, sum::expr(&remainder.cells));
        let remainder_lt_divisor = LtWordGadget::construct(cb, &remainder, &divisor);

        // Based on different opcode cases, constrain stack pops and pushes as:
        // - for `MUL`, two pops are quotient and divisor, and push is dividend.
        // - for `DIV`, two pops are dividend and divisor, and push is quotient.
        // - for `MOD`, two pops are dividend and divisor, and push is remainder.
        // - for `SHL`, two pops are shift and quotient, and push is dividend.
        // - for `SHR`, two pops are shift and dividend, and push is quotient.
        cb.stack_pop(pop1.expr());
        cb.stack_pop(
            (is_mul.clone() + is_div.clone() + is_mod.clone()) * divisor.expr()
                + is_shl.clone() * quotient.expr()
                + is_shr.clone() * dividend.expr(),
        );
        cb.stack_push(
            (is_mul.clone() + is_shl.clone()) * dividend.expr()
                + (is_div.clone() + is_shr.clone())
                    * quotient.expr()
                    * (1.expr() - divisor_is_zero.expr())
                + is_mod.clone() * remainder.expr() * (1.expr() - divisor_is_zero.expr()),
        );

        cb.require_zero(
            "remainder < divisor when divisor != 0",
            (1.expr() - divisor_is_zero.expr()) * (1.expr() - remainder_lt_divisor.expr()),
        );

        cb.require_zero(
            "remainder == 0 for both opcode MUL and SHL",
            (is_mul.clone() + is_shl.clone()) * (1.expr() - remainder_is_zero.expr()),
        );

        cb.require_zero(
            "overflow == 0 for opcode DIV, MOD and SHR",
            (is_div.clone() + is_mod.clone() + is_shr.clone()) * mul_add_words.overflow(),
        );

        cb.require_zero(
            "pop1 == pop1.cells[0] when divisor != 0 for opcode SHL and SHR",
            (is_shl.clone() + is_shr.clone())
                * (1.expr() - divisor_is_zero.expr())
                * (pop1.expr() - pop1.cells[0].expr()),
        );

        let gas_cost = is_mul * OpcodeId::MUL.constant_gas_cost().expr()
            + is_div * OpcodeId::DIV.constant_gas_cost().expr()
            + is_mod * OpcodeId::MOD.constant_gas_cost().expr()
            + is_shl * OpcodeId::SHL.constant_gas_cost().expr()
            + is_shr * OpcodeId::SHR.constant_gas_cost().expr();

        let step_state_transition = StepStateTransition {
            rw_counter: Delta(3.expr()),
            program_counter: Delta(1.expr()),
            stack_pointer: Delta(1.expr()),
            gas_left: Delta(-gas_cost),
            ..Default::default()
        };

        let same_context = SameContextGadget::construct(cb, opcode, step_state_transition);

        Self {
            same_context,
            quotient,
            divisor,
            remainder,
            dividend,
            pop1,
            mul_add_words,
            divisor_is_zero,
            remainder_is_zero,
            remainder_lt_divisor,
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

        // First byte of shift word used for opcode SHL and SHR
        let shf0 = pop1.to_le_bytes()[0];

        let (quotient, divisor, remainder, dividend) = match step.opcode.unwrap() {
            OpcodeId::MUL => (pop1, pop2, U256::from(0), push),
            OpcodeId::DIV => (push, pop2, pop1 - push * pop2, pop1),
            OpcodeId::MOD => (
                if pop2.is_zero() {
                    U256::from(0)
                } else {
                    pop1 / pop2
                },
                pop2,
                if pop2.is_zero() { pop1 } else { push },
                pop1,
            ),
            OpcodeId::SHL => (
                pop2,
                if U256::from(shf0) == pop1 {
                    U256::from(1) << shf0
                } else {
                    U256::from(0)
                },
                U256::from(0),
                push,
            ),
            OpcodeId::SHR => {
                let divisor = if U256::from(shf0) == pop1 {
                    U256::from(1) << shf0
                } else {
                    U256::from(0)
                };
                (push, divisor, pop2 - push * divisor, pop2)
            }
            _ => unreachable!(),
        };

        self.quotient
            .assign(region, offset, Some(quotient.to_le_bytes()))?;
        self.divisor
            .assign(region, offset, Some(divisor.to_le_bytes()))?;
        self.remainder
            .assign(region, offset, Some(remainder.to_le_bytes()))?;
        self.dividend
            .assign(region, offset, Some(dividend.to_le_bytes()))?;
        self.pop1.assign(region, offset, Some(pop1.to_le_bytes()))?;
        self.mul_add_words
            .assign(region, offset, [quotient, divisor, remainder, dividend])?;
        let divisor_sum = (0..32).fold(0, |acc, idx| acc + divisor.byte(idx) as u64);
        self.divisor_is_zero
            .assign(region, offset, F::from(divisor_sum))?;
        let remainder_sum = (0..32).fold(0, |acc, idx| acc + remainder.byte(idx) as u64);
        self.remainder_is_zero
            .assign(region, offset, F::from(remainder_sum))?;
        self.remainder_lt_divisor
            .assign(region, offset, remainder, divisor)
    }
}

#[inline]
fn is_opcode<F: Field>(opcode: &Cell<F>, opcode_id: OpcodeId) -> Expression<F> {
    generate_lagrange_base_polynomial(
        opcode,
        opcode_id.as_u8() as usize,
        [
            OpcodeId::MUL,
            OpcodeId::DIV,
            OpcodeId::MOD,
            OpcodeId::SHL,
            OpcodeId::SHR,
        ]
        .into_iter()
        .map(|op_id| op_id.as_u8() as usize),
    )
}

#[cfg(test)]
mod test {
    use crate::{evm_circuit::test::rand_word, test_util::run_test_circuits};
    use eth_types::evm_types::OpcodeId;
    use eth_types::{bytecode, Word};
    use mock::TestContext;

    fn test_ok(opcode: OpcodeId, pop1: Word, pop2: Word) {
        let bytecode = bytecode! {
            PUSH32(pop1)
            PUSH32(pop2)
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
    fn mul_gadget_tests() {
        test_ok(OpcodeId::MUL, Word::from(0xABCD), Word::from(0x1234));
        test_ok(OpcodeId::MUL, Word::from(0xABCD), Word::from(0x1234) << 240);
        test_ok(
            OpcodeId::MUL,
            Word::from(0xABCD) << 240,
            Word::from(0x1234) << 240,
        );
        let max_word = Word::from_big_endian(&[255_u8; 32]);
        test_ok(OpcodeId::MUL, max_word, Word::from(0x1234));
        test_ok(OpcodeId::MUL, max_word, Word::from(0));
        test_ok(OpcodeId::MUL, rand_word(), rand_word());
    }

    #[test]
    fn div_gadget_tests() {
        test_ok(OpcodeId::DIV, Word::from(0xABCD), Word::from(0x1234));
        test_ok(OpcodeId::DIV, Word::from(0xABCD), Word::from(0x1234) << 240);
        test_ok(
            OpcodeId::DIV,
            Word::from(0xABCD) << 240,
            Word::from(0x1234) << 240,
        );
        let max_word = Word::from_big_endian(&[255_u8; 32]);
        test_ok(OpcodeId::DIV, max_word, Word::from(0x1234));
        test_ok(OpcodeId::DIV, max_word, Word::from(0));
        test_ok(OpcodeId::DIV, rand_word(), rand_word());
    }

    #[test]
    fn mod_gadget_tests() {
        test_ok(OpcodeId::MOD, Word::from(0xABCD), Word::from(0x1234));
        test_ok(OpcodeId::MOD, Word::from(0xABCD), Word::from(0x1234) << 240);
        test_ok(
            OpcodeId::MOD,
            Word::from(0xABCD) << 240,
            Word::from(0x1234) << 240,
        );
        let max_word = Word::from_big_endian(&[255_u8; 32]);
        test_ok(OpcodeId::MOD, max_word, Word::from(0x1234));
        test_ok(OpcodeId::MOD, max_word, Word::from(0));
        test_ok(OpcodeId::MOD, rand_word(), rand_word());
    }

    #[test]
    fn shl_gadget_tests() {
        test_ok(OpcodeId::SHL, Word::from(0xABCD) << 240, Word::from(8));
        test_ok(OpcodeId::SHL, Word::from(0x1234) << 240, Word::from(7));
        test_ok(OpcodeId::SHL, Word::from(0x8765) << 240, Word::from(17));
        test_ok(OpcodeId::SHL, Word::from(0x4321) << 240, Word::from(0));
        test_ok(OpcodeId::SHL, Word::from(0xFFFF), Word::from(256));
        test_ok(OpcodeId::SHL, Word::from(0x12345), Word::from(256 + 8 + 1));
        let max_word = Word::from_big_endian(&[255_u8; 32]);
        test_ok(OpcodeId::SHL, max_word, Word::from(63));
        test_ok(OpcodeId::SHL, max_word, Word::from(128));
        test_ok(OpcodeId::SHL, max_word, Word::from(129));
        test_ok(OpcodeId::SHL, rand_word(), rand_word());
    }

    #[test]
    fn shr_gadget_tests() {
        test_ok(OpcodeId::SHR, Word::from(0xABCD), Word::from(8));
        test_ok(OpcodeId::SHR, Word::from(0x1234), Word::from(7));
        test_ok(OpcodeId::SHR, Word::from(0x8765), Word::from(17));
        test_ok(OpcodeId::SHR, Word::from(0x4321), Word::from(0));
        test_ok(OpcodeId::SHR, Word::from(0xFFFF), Word::from(256));
        test_ok(OpcodeId::SHR, Word::from(0x12345), Word::from(256 + 8 + 1));
        let max_word = Word::from_big_endian(&[255_u8; 32]);
        test_ok(OpcodeId::SHR, max_word, Word::from(63));
        test_ok(OpcodeId::SHR, max_word, Word::from(128));
        test_ok(OpcodeId::SHR, max_word, Word::from(129));
        test_ok(OpcodeId::SHR, rand_word(), rand_word());
    }
}
