use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        step::ExecutionState,
        util::{
            self,
            common_gadget::SameContextGadget,
            constraint_builder::{ConstraintBuilder, StepStateTransition, Transition::Delta},
            math_gadget::{IsZeroGadget, LtWordGadget, MulAddWordsGadget},
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
    /// Words quotient, divisor, remainder, dividend and
    /// pop1 (used for shift value of SHL and SHR)
    pub words: [util::Word<F>; 5],
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
        let is_mul = is_mul(&opcode);
        let is_div = is_div(&opcode);
        let is_mod = is_mod(&opcode);
        let is_shl = is_shl(&opcode);
        let is_shr = is_shr(&opcode);

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
            (is_mul + is_shl) * (1.expr() - remainder_is_zero.expr()),
        );

        cb.require_zero(
            "overflow == 0 for opcode DIV, MOD and SHR",
            (is_div + is_mod + is_shr) * mul_add_words.overflow(),
        );

        let step_state_transition = StepStateTransition {
            rw_counter: Delta(3.expr()),
            program_counter: Delta(1.expr()),
            stack_pointer: Delta(1.expr()),
            gas_left: Delta(-OpcodeId::MUL.constant_gas_cost().expr()),
            ..Default::default()
        };

        let same_context = SameContextGadget::construct(cb, opcode, step_state_transition);

        Self {
            same_context,
            words: [quotient, divisor, remainder, dividend, pop1],
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

        // Shift values are only used for opcode SHL and SHR.
        let shf0 = pop1.to_le_bytes()[0];
        let shf_lt256 = pop1
            .to_le_bytes()
            .iter()
            .fold(0, |acc, val| acc + *val as u128)
            - shf0 as u128;

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
                if shf_lt256 == 0 {
                    U256::from(1) << shf0
                } else {
                    U256::from(0)
                },
                U256::from(0),
                push,
            ),
            OpcodeId::SHR => {
                let divisor = if shf_lt256 == 0 {
                    U256::from(1) << shf0
                } else {
                    U256::from(0)
                };
                (push, divisor, pop2 - push * divisor, pop2)
            }
            _ => unreachable!(),
        };
        self.words[0].assign(region, offset, Some(quotient.to_le_bytes()))?;
        self.words[1].assign(region, offset, Some(divisor.to_le_bytes()))?;
        self.words[2].assign(region, offset, Some(remainder.to_le_bytes()))?;
        self.words[3].assign(region, offset, Some(dividend.to_le_bytes()))?;
        self.words[4].assign(region, offset, Some(pop1.to_le_bytes()))?;
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

// The opcode value for MUL, DIV, MOD, SHL and SHR are 2, 4, 6, 0x1b and 0x1c.
// When the opcode is MUL, the result of below formula is 5200:
// (DIV - opcode) * (MOD- opcode) * (SHL - opcode) * (SHR - opcode)
// To make `is_mul` be either 0 or 1, the result needs to be divided by 5200,
// which is equivalent to multiply it by inversion of 5200.
// And calculate `is_div`, `is_mod`, `is_shl` and `is_shr` respectively.
#[inline]
fn is_mul<F: Field>(opcode: &Cell<F>) -> Expression<F> {
    (OpcodeId::DIV.expr() - opcode.expr())
        * (OpcodeId::MOD.expr() - opcode.expr())
        * (OpcodeId::SHL.expr() - opcode.expr())
        * (OpcodeId::SHR.expr() - opcode.expr())
        * F::from(5200).invert().unwrap()
}

#[inline]
fn is_div<F: Field>(opcode: &Cell<F>) -> Expression<F> {
    (opcode.expr() - OpcodeId::MUL.expr())
        * (OpcodeId::MOD.expr() - opcode.expr())
        * (OpcodeId::SHL.expr() - opcode.expr())
        * (OpcodeId::SHR.expr() - opcode.expr())
        * F::from(2208).invert().unwrap()
}

#[inline]
fn is_mod<F: Field>(opcode: &Cell<F>) -> Expression<F> {
    (opcode.expr() - OpcodeId::MUL.expr())
        * (opcode.expr() - OpcodeId::DIV.expr())
        * (OpcodeId::SHL.expr() - opcode.expr())
        * (OpcodeId::SHR.expr() - opcode.expr())
        * F::from(3696).invert().unwrap()
}

#[inline]
fn is_shl<F: Field>(opcode: &Cell<F>) -> Expression<F> {
    (opcode.expr() - OpcodeId::MUL.expr())
        * (opcode.expr() - OpcodeId::DIV.expr())
        * (opcode.expr() - OpcodeId::MOD.expr())
        * (OpcodeId::SHR.expr() - opcode.expr())
        * F::from(12075).invert().unwrap()
}

#[inline]
fn is_shr<F: Field>(opcode: &Cell<F>) -> Expression<F> {
    (opcode.expr() - OpcodeId::MUL.expr())
        * (opcode.expr() - OpcodeId::DIV.expr())
        * (opcode.expr() - OpcodeId::MOD.expr())
        * (opcode.expr() - OpcodeId::SHL.expr())
        * F::from(13728).invert().unwrap()
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
    fn mul_gadget_simple() {
        test_ok(OpcodeId::MUL, 0x030201.into(), 0x060504.into());
    }

    #[test]
    fn mul_gadget_overflow() {
        let a = Word::from_dec_str("3402823669209384634633746074317682114560").unwrap(); // 2**128 * 10
        let b = Word::from_dec_str("34028236692093846346337460743176821145600").unwrap(); // 2**128 * 100
        test_ok(OpcodeId::MUL, a, b);

        let a = Word::from_dec_str("3402823669209384634633746074317682114560").unwrap(); // 2**128 * 10
        let b = Word::from_dec_str("34028236692093846346337460743176821145500").unwrap(); // (2**128 - 1) * 100
        test_ok(OpcodeId::MUL, a, b);
    }

    #[test]
    fn mul_gadget_rand() {
        let a = rand_word();
        let b = rand_word();
        test_ok(OpcodeId::MUL, a, b);
    }

    #[test]
    fn div_gadget_simple() {
        test_ok(OpcodeId::DIV, 0xFFFFFF.into(), 0xABC.into());
        test_ok(OpcodeId::DIV, 0xABC.into(), 0xFFFFFF.into());
        test_ok(OpcodeId::DIV, 0xFFFFFF.into(), 0xFFFFFFF.into());
        test_ok(OpcodeId::DIV, 0xABC.into(), 0.into());
        test_ok(
            OpcodeId::DIV,
            Word::from_big_endian(&[255u8; 32]),
            0xABCDEF.into(),
        );
    }

    #[test]
    fn div_gadget_rand() {
        let dividend = rand_word();
        let divisor = rand_word();
        test_ok(OpcodeId::DIV, dividend, divisor);
    }

    #[test]
    fn mod_gadget_simple() {
        test_ok(OpcodeId::MOD, 0xFFFFFF.into(), 0xABC.into());
        test_ok(OpcodeId::MOD, 0xABC.into(), 0xFFFFFF.into());
        test_ok(OpcodeId::MOD, 0xFFFFFF.into(), 0xFFFFFFF.into());
        test_ok(OpcodeId::MOD, 0xABC.into(), 0.into());
        test_ok(
            OpcodeId::MOD,
            Word::from_big_endian(&[255u8; 32]),
            0xABCDEF.into(),
        );
    }

    #[test]
    fn mod_gadget_rand() {
        let dividend = rand_word();
        let divisor = rand_word();
        test_ok(OpcodeId::MOD, dividend, divisor);
    }
}
