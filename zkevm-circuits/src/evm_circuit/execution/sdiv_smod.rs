use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        step::ExecutionState,
        util::{
            common_gadget::SameContextGadget,
            constraint_builder::{ConstraintBuilder, StepStateTransition, Transition::Delta},
            math_gadget::{AbsWordGadget, IsZeroGadget, LtWordGadget, MulAddWordsGadget},
            select, sum,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    util::Expr,
};
use bus_mapping::evm::OpcodeId;
use eth_types::{Field, ToLittleEndian, U256};
use halo2_proofs::{circuit::Region, plonk::Error};

#[derive(Clone, Debug)]
pub(crate) struct SignedDivModGadget<F> {
    same_context: SameContextGadget<F>,
    mul_add_words: MulAddWordsGadget<F>,
    divisor_is_zero: IsZeroGadget<F>,
    quotient_is_zero: IsZeroGadget<F>,
    lt_word: LtWordGadget<F>,
    abs_words: [AbsWordGadget<F>; 4],
}

pub(crate) fn get_sign(x: U256) -> u8 {
    let x_le_bytes = x.to_le_bytes();
    if x_le_bytes[31] < 128 {
        0u8
    } else {
        1u8
    }
}

pub(crate) fn get_neg(x: U256) -> U256 {
    if x.is_zero() {
        x
    } else {
        U256::from_big_endian(&[255u8; 32]) - x + U256::from(1)
    }
}

pub(crate) fn get_word_abs(x: U256) -> U256 {
    if get_sign(x) == 0u8 {
        x
    } else {
        get_neg(x)
    }
}

impl<F: Field> ExecutionGadget<F> for SignedDivModGadget<F> {
    const NAME: &'static str = "SDIV_SMOD";

    const EXECUTION_STATE: ExecutionState = ExecutionState::SDIV_SMOD;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        let opcode = cb.query_cell();

        let is_sdiv = (OpcodeId::SMOD.expr() - opcode.expr()) * F::from(2).invert().unwrap();

        let mul_add_words = MulAddWordsGadget::construct(cb);
        let divisor_is_zero = IsZeroGadget::construct(cb, sum::expr(&mul_add_words.b.cells));
        let quotient_is_zero = IsZeroGadget::construct(cb, sum::expr(&mul_add_words.a.cells));
        let lt_word = LtWordGadget::construct(cb, &mul_add_words.c, &mul_add_words.b);

        let abs_words = [
            AbsWordGadget::construct(cb, &mul_add_words.a),
            AbsWordGadget::construct(cb, &mul_add_words.b),
            AbsWordGadget::construct(cb, &mul_add_words.c),
            AbsWordGadget::construct(cb, &mul_add_words.d),
        ];

        cb.stack_pop(abs_words[3].x.expr());
        cb.stack_pop(abs_words[1].x.expr());
        cb.stack_push(select::expr(
            is_sdiv,
            abs_words[0].x.expr() * (1.expr() - divisor_is_zero.expr()),
            abs_words[2].x.expr() * (1.expr() - divisor_is_zero.expr()),
        ));

        cb.add_constraint(
            "abs(residue) < abs(divisor) when divisor != 0 for opcode SDIV/SMOD",
            (1.expr() - lt_word.expr()) * (1.expr() - divisor_is_zero.expr()),
        );
        cb.add_constraint(
            "overflow == 0 for opcode SDIV/SMOD",
            mul_add_words.overflow(),
        );

        cb.condition(
            (1.expr() - quotient_is_zero.expr()) * (1.expr() - divisor_is_zero.expr()),
            |cb| {
                cb.require_equal(
                    "sgn(dividend) == sgn(residue) when quotient or divisor != 0 for opcode SDIV/SMOD",
                    abs_words[3].sign_check.expr(),
                    abs_words[2].sign_check.expr(),
                );
                cb.require_equal(
                    "sgn(dividend) == sgn(divisor) * sgn(quotient) when quotient or divisor != 0 for opcode SDIV/SMOD",
                    abs_words[3].sign_check.expr() * (1.expr() - quotient_is_zero.expr() * divisor_is_zero.expr()),
                    abs_words[0].sign_check.expr() * abs_words[1].sign_check.expr()
                        + (1.expr() - abs_words[0].sign_check.expr()) * (1.expr() - abs_words[1].sign_check.expr()),
                );
            }
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
            mul_add_words,
            divisor_is_zero,
            quotient_is_zero,
            lt_word,
            abs_words,
        }
    }

    fn assign_exec_step(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        block: &Block<F>,
        _: &Transaction,
        _: &Call,
        step: &ExecStep,
    ) -> Result<(), Error> {
        self.same_context.assign_exec_step(region, offset, step)?;
        let indices = [step.rw_indices[0], step.rw_indices[1], step.rw_indices[2]];
        let [pop1, pop2, push] = indices.map(|idx| block.rws[idx].stack_value());
        let pop1_abs = get_word_abs(pop1);
        let pop2_abs = get_word_abs(pop2);
        let push_abs = get_word_abs(push);
        let pop1_sign = get_sign(pop1);
        let pop2_sign = get_sign(pop2);
        let (a, b, c, d) = match step.opcode.unwrap() {
            OpcodeId::SDIV => (
                push,
                pop2,
                if get_sign(pop1) == 0u8 {
                    pop1_abs - push_abs * pop2_abs
                } else {
                    get_neg(pop1_abs - push_abs * pop2_abs)
                },
                pop1,
            ),
            OpcodeId::SMOD => (
                if pop2.is_zero() {
                    U256::from(0)
                } else if pop1_sign == pop2_sign {
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
        let a_abs = get_word_abs(a);
        let b_abs = get_word_abs(b);
        let c_abs = get_word_abs(c);
        let d_abs = get_word_abs(d);
        self.mul_add_words
            .assign(region, offset, [a_abs, b_abs, c_abs, d_abs])?;
        self.lt_word.assign(region, offset, c_abs, b_abs)?;
        let b_sum = (0..32).fold(0, |acc, idx| acc + b_abs.byte(idx) as u64);
        let a_sum = (0..32).fold(0, |acc, idx| acc + a_abs.byte(idx) as u64);
        self.divisor_is_zero
            .assign(region, offset, F::from(b_sum))?;
        self.quotient_is_zero
            .assign(region, offset, F::from(a_sum))?;
        self.abs_words[0].assign(region, offset, a)?;
        self.abs_words[1].assign(region, offset, b)?;
        self.abs_words[2].assign(region, offset, c)?;
        self.abs_words[3].assign(region, offset, d)?;
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::{evm_circuit::test::rand_word, test_util::run_test_circuits};
    use eth_types::evm_types::OpcodeId;
    use eth_types::{bytecode, Word};

    fn test_ok(opcode: OpcodeId, a: Word, b: Word) {
        let bytecode = bytecode! {
            PUSH32(b)
            PUSH32(a)
            #[start]
            .write_op(opcode)
            STOP
        };
        assert_eq!(run_test_circuits(bytecode), Ok(()));
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
