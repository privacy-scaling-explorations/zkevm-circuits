use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        step::ExecutionState,
        util::{
            and,
            common_gadget::SameContextGadget,
            constraint_builder::{
                ConstraintBuilder, StepStateTransition, Transition,
            },
            from_bytes,
            math_gadget::{ComparisonGadget, IsEqualGadget, LtGadget},
            select, Word,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    util::Expr,
};

use bus_mapping::{eth_types::ToBigEndian, evm::OpcodeId};
use halo2::{arithmetic::FieldExt, circuit::Region, plonk::Error};

/// Gadget that implements the ExecutionGadget trait to handle the Opcodes SLT
/// and SGT.
#[derive(Clone, Debug)]
pub(crate) struct SignedComparatorGadget<F> {
    same_context: SameContextGadget<F>,

    a: Word<F>,
    b: Word<F>,

    sign_check_a: LtGadget<F, 1>,
    sign_check_b: LtGadget<F, 1>,
    lt_lo: LtGadget<F, 16>,
    comparison_hi: ComparisonGadget<F, 16>,

    is_sgt: IsEqualGadget<F>,
}

impl<F: FieldExt> ExecutionGadget<F> for SignedComparatorGadget<F> {
    const NAME: &'static str = "SCMP";

    const EXECUTION_STATE: ExecutionState = ExecutionState::SCMP;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        let opcode = cb.query_cell();

        let a = cb.query_word();
        let b = cb.query_word();

        // The Signed Comparator gadget is used for both opcodes [SLT]() and
        // [SGT](). Depending on whether the opcode is SLT or SGT, we
        // swap the order in which the inputs are placed on the stack.
        let is_sgt =
            IsEqualGadget::construct(cb, opcode.expr(), OpcodeId::SGT.expr());

        // Both `a` and `b` are to be treated as two's complement signed 256-bit
        // (32 cells) integers. This means, the first bit denotes the sign
        // of the absolute value in the rest of the 255 bits. This means the
        // number is negative if the most significant cell >= 128
        // (0b10000000). `a` and `b` being in the big-endian notation, the
        // most-significant byte is the first byte.
        let sign_check_a =
            LtGadget::construct(cb, a.cells[0].expr(), 128.expr());
        let sign_check_b =
            LtGadget::construct(cb, b.cells[0].expr(), 128.expr());

        // sign_check_a_lt expression implies a is positive since its MSB < 2**7
        // sign_check_b_lt expression implies b is positive since its MSB < 2**7
        let sign_check_a_lt = sign_check_a.expr();
        let sign_check_b_lt = sign_check_b.expr();

        // We require the comparison check only for the cases where:
        // (a < 0 && b < 0) || (a > 0 && b > 0).
        // We ignore the equality expression since we only care about the LT
        // check.
        // By `lo` we mean the low bytes, and `hi` stands for the more
        // significant bytes. While only considering the absolute
        // values, we have: a < b == 1 iff ((a_hi < b_hi) || ((a_hi ==
        // b_hi) && (a_lo < b_lo)))
        let lt_lo = LtGadget::construct(
            cb,
            from_bytes::expr(&a.cells[16..32]),
            from_bytes::expr(&b.cells[16..32]),
        );
        let comparison_hi = ComparisonGadget::construct(
            cb,
            from_bytes::expr(&a.cells[0..16]),
            from_bytes::expr(&b.cells[0..16]),
        );
        let a_lt_b_lo = lt_lo.expr();
        let (a_lt_b_hi, a_eq_b_hi) = comparison_hi.expr();

        // Add selector only for the cases where both a and b are positive or
        // negative. This selector will be used after handling the cases
        // where either only a or only b are negative.
        //
        // if a > 0 && b > 0:
        //      a < b -> (a_hi < b_hi) ? 1 : (a_hi == b_hi) * (a_lo < b_lo)
        // else if a < 0 && b < 0:
        //      a < b -> (a_hi < b_hi) ? 0 : ~((a_hi == b_hi) * (a_lo < b_lo))
        let a_b_positive =
            and::expr(&[sign_check_a_lt.clone(), sign_check_b_lt.clone()]);
        let a_b_negative = and::expr(&[
            1.expr() - sign_check_a_lt.clone(),
            1.expr() - sign_check_b_lt.clone(),
        ]);
        let a_lt_b = select::expr(
            a_b_positive,
            select::expr(
                a_lt_b_hi.clone(),
                1.expr(),
                a_eq_b_hi.clone() * a_lt_b_lo.clone(),
            ),
            and::expr(&[
                a_b_negative,
                select::expr(
                    a_lt_b_hi,
                    0.expr(),
                    1.expr() - (a_eq_b_hi * a_lt_b_lo),
                ),
            ]),
        );

        // Add a trivial selector: if only a or only b is negative we have the
        // result.
        // result = if a < 0 && b > 0, slt = 1.
        // result = if b < 0 && a > 0, slt = 0.
        let a_negative =
            (1.expr() - sign_check_a_lt.expr()) * sign_check_b_lt.expr();
        let b_negative =
            (1.expr() - sign_check_b_lt.expr()) * sign_check_a_lt.expr();
        let result = select::expr(
            a_negative,
            1.expr(),
            select::expr(b_negative, 0.expr(), a_lt_b),
        );

        // Pop a and b from the stack, push the result on the stack.
        cb.stack_pop(select::expr(is_sgt.expr(), b.expr(), a.expr()));
        cb.stack_pop(select::expr(is_sgt.expr(), a.expr(), b.expr()));
        cb.stack_push(result);

        // The read-write counter changes by three since we're reading two words
        // from stack and writing one. The program counter shifts only by one
        // and the since the stack now has one less word, the stack pointer also
        // shifts by one.
        let step_state_transition = StepStateTransition {
            rw_counter: Transition::Delta(3.expr()),
            program_counter: Transition::Delta(1.expr()),
            stack_pointer: Transition::Delta(1.expr()),
            ..Default::default()
        };
        let same_context = SameContextGadget::construct(
            cb,
            opcode,
            step_state_transition,
            None,
        );

        Self {
            same_context,
            a,
            b,
            sign_check_a,
            sign_check_b,
            lt_lo,
            comparison_hi,
            is_sgt,
        }
    }

    fn assign_exec_step(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        block: &Block<F>,
        _transaction: &Transaction<F>,
        _call: &Call<F>,
        step: &ExecStep,
    ) -> Result<(), Error> {
        self.same_context.assign_exec_step(region, offset, step)?;

        let opcode = step.opcode.unwrap();

        // SLT opcode is the default check in the SCMP gadget. Swap rw for SGT.
        self.is_sgt.assign(
            region,
            offset,
            F::from(opcode.as_u8() as u64),
            F::from(OpcodeId::SGT.as_u8() as u64),
        )?;
        let indices = if opcode == OpcodeId::SGT {
            [step.rw_indices[1], step.rw_indices[0]]
        } else {
            [step.rw_indices[0], step.rw_indices[1]]
        };
        let [a, b] =
            indices.map(|idx| block.rws[idx].stack_value().to_be_bytes());

        // Assign to the sign check gadgets. Since both a and b are in the
        // big-endian form, the most significant byte is the first byte.
        self.sign_check_a.assign(
            region,
            offset,
            F::from(a[0] as u64),
            F::from(128u64),
        )?;
        self.sign_check_b.assign(
            region,
            offset,
            F::from(b[0] as u64),
            F::from(128u64),
        )?;

        // Assign to the comparison gadgets. The first 16 bytes are assigned to
        // the `hi` comparison while the last 16 bytes are assigned to
        // the `lo` less-than gadget.
        self.lt_lo.assign(
            region,
            offset,
            from_bytes::value(&a[16..32]),
            from_bytes::value(&b[16..32]),
        )?;
        self.comparison_hi.assign(
            region,
            offset,
            from_bytes::value(&a[0..16]),
            from_bytes::value(&b[0..16]),
        )?;

        self.a.assign(region, offset, Some(a))?;
        self.b.assign(region, offset, Some(b))?;

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use bus_mapping::{bytecode, eth_types::Word, evm::OpcodeId};

    use crate::evm_circuit::{
        test::{rand_word, run_test_circuit_incomplete_fixed_table},
        witness,
    };

    use std::convert::TryInto;

    fn test_ok(opcode: OpcodeId, a: Word, b: Word) {
        let bytecode = bytecode! {
            PUSH32(b)
            PUSH32(a)
            #[start]
            .write_op(opcode)
            STOP
        };
        let block = witness::build_block_from_trace_code_at_start(&bytecode);
        assert_eq!(run_test_circuit_incomplete_fixed_table(block), Ok(()));
    }

    #[test]
    // TODO(rohit): rename this once lookup error is debugged
    fn alice() {
        let zero = Word::from_big_endian(&[0u8; 32]);
        let minus_1 = Word::from_big_endian(&[255u8; 32]);
        test_ok(OpcodeId::SLT, minus_1, zero);
        test_ok(OpcodeId::SGT, zero, minus_1);
    }

    #[test]
    // TODO(rohit): rename this once lookup error is debugged
    fn bob() {
        let zero = Word::from_big_endian(&[0u8; 32]);
        let plus_1 = {
            let mut bytes = vec![0u8; 32];
            bytes[31] = 1u8;
            Word::from_big_endian(&bytes)
        };
        test_ok(OpcodeId::SLT, zero, plus_1);
        test_ok(OpcodeId::SGT, plus_1, zero);
    }

    #[test]
    // TODO(rohit): rename this once lookup error is debugged
    fn charlie() {
        let minus_1 = Word::from_big_endian(&[255u8; 32]);
        let minus_2 = {
            let mut bytes = vec![255u8; 32];
            bytes[31] = 254u8;
            Word::from_big_endian(&bytes)
        };
        test_ok(OpcodeId::SLT, minus_2, minus_1);
        test_ok(OpcodeId::SGT, minus_1, minus_2);
    }

    #[test]
    // TODO(rohit): rename this once lookup error is debugged
    fn dave() {
        let plus_1 = {
            let mut bytes = vec![0u8; 32];
            bytes[31] = 1u8;
            Word::from_big_endian(&bytes)
        };
        let plus_2 = plus_1 + 1;
        test_ok(OpcodeId::SLT, plus_1, plus_2);
        test_ok(OpcodeId::SGT, plus_2, plus_1);
    }

    #[test]
    #[ignore]
    fn signed_comparator_gadget_simple() {
        let zero = Word::from_big_endian(&[0u8; 32]);
        let minus_1 = Word::from_big_endian(&[255u8; 32]);
        let minus_2 = {
            let mut bytes = vec![255u8; 32];
            bytes[31] = 254u8;
            let bytes: [u8; 32] = bytes.try_into().unwrap();
            Word::from_big_endian(&bytes)
        };
        let plus_1 = {
            let mut bytes = vec![0u8; 32];
            bytes[31] = 1u8;
            let bytes: [u8; 32] = bytes.try_into().unwrap();
            Word::from_big_endian(&bytes)
        };
        let plus_2 = {
            let mut bytes = vec![0u8; 32];
            bytes[31] = 2u8;
            let bytes: [u8; 32] = bytes.try_into().unwrap();
            Word::from_big_endian(&bytes)
        };

        // SLT
        test_ok(OpcodeId::SLT, minus_1, zero);
        test_ok(OpcodeId::SLT, zero, plus_1);
        test_ok(OpcodeId::SLT, plus_1, plus_2);
        test_ok(OpcodeId::SLT, minus_2, zero);
        test_ok(OpcodeId::SLT, minus_2, plus_1);
        test_ok(OpcodeId::SLT, minus_2, minus_1);

        //// SGT
        test_ok(OpcodeId::SGT, minus_1, minus_2);
        test_ok(OpcodeId::SGT, zero, minus_1);
        test_ok(OpcodeId::SGT, plus_1, zero);
        test_ok(OpcodeId::SGT, plus_2, plus_1);
        test_ok(OpcodeId::SGT, plus_1, minus_1);
        test_ok(OpcodeId::SGT, plus_1, minus_2);
    }

    #[test]
    #[ignore]
    fn signed_comparator_gadget_rand() {
        let a = rand_word();
        let b = rand_word();
        test_ok(OpcodeId::SLT, a, b);
        test_ok(OpcodeId::SGT, a, b);
    }
}
