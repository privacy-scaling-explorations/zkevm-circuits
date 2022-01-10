use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        step::ExecutionState,
        util::{
            common_gadget::SameContextGadget,
            constraint_builder::{
                ConstraintBuilder, StepStateTransition, Transition,
            },
            from_bytes,
            math_gadget::{ComparisonGadget, IsEqualGadget},
            select, Word,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    util::Expr,
};

use bus_mapping::{eth_types::ToLittleEndian, evm::OpcodeId};
use halo2::{arithmetic::FieldExt, circuit::Region, plonk::Error};

/// Gadget that implements the ExecutionGadget trait to handle the Opcodes SLT
/// and SGT.
#[derive(Clone, Debug)]
pub(crate) struct SignedComparatorGadget<F> {
    same_context: SameContextGadget<F>,

    a: Word<F>,
    b: Word<F>,

    sign_check_a: ComparisonGadget<F, 1>,
    sign_check_b: ComparisonGadget<F, 1>,
    comparison_lo: ComparisonGadget<F, 16>,
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
        // (0b10000000).
        let sign_check_a = ComparisonGadget::construct(
            cb,
            from_bytes::expr(&a.cells[0..1]),
            128u8.expr(),
        );
        let sign_check_b = ComparisonGadget::construct(
            cb,
            from_bytes::expr(&b.cells[0..1]),
            128u8.expr(),
        );

        // sign_check_a_lt expression implies a is positive since its MSB < 2**7
        // sign_check_b_lt expression implies b is positive since its MSB < 2**7
        let (sign_check_a_lt, _sign_check_a_eq) = sign_check_a.expr();
        let (sign_check_b_lt, _sign_check_b_eq) = sign_check_b.expr();

        // We require the comparison check only for the cases where:
        // (a < 0 && b < 0) || (a > 0 && b > 0).
        // We ignore the equality expression since we only care about the LT
        // check.
        let comparison_lo = ComparisonGadget::construct(
            cb,
            from_bytes::expr(&a.cells[0..16]),
            from_bytes::expr(&b.cells[0..16]),
        );
        let comparison_hi = ComparisonGadget::construct(
            cb,
            from_bytes::expr(&a.cells[16..32]),
            from_bytes::expr(&b.cells[16..32]),
        );
        let (lt_lo, _eq_lo) = comparison_lo.expr();
        let (lt_hi, eq_hi) = comparison_hi.expr();

        // If a and b both are positive, we do a standard comparison check. If
        // both a and b are negative, we invert those outcomes.
        let a_b_positive = sign_check_a_lt.clone() * sign_check_b_lt.clone();
        let a_lt_b = select::expr(
            a_b_positive,
            select::expr(
                lt_hi.clone(),
                1u8.expr(),
                eq_hi.clone() * lt_lo.clone(),
            ),
            select::expr(lt_hi, 0u8.expr(), 1u8.expr() - (eq_hi * lt_lo)),
        );

        // Add a trivial selector: if only a or only b is negative we have the
        // result. result = if a < 0 && b > 0, slt = 1.
        // result = if b < 0 && a < 0, slt = 0.
        let a_negative =
            (1u8.expr() - sign_check_a_lt.expr()) * sign_check_b_lt.expr();
        let b_negative =
            (1u8.expr() - sign_check_b_lt.expr()) * sign_check_a_lt.expr();
        let result = select::expr(
            a_negative,
            0u8.expr(),
            select::expr(b_negative, 1u8.expr(), a_lt_b),
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
            rw_counter: Transition::Delta(3u8.expr()),
            program_counter: Transition::Delta(1u8.expr()),
            stack_pointer: Transition::Delta(1u8.expr()),
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
            comparison_lo,
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
        let is_sgt = self.is_sgt.assign(
            region,
            offset,
            F::from(opcode.as_u8() as u64),
            F::from(OpcodeId::SGT.as_u8() as u64),
        )?;
        let indices = if is_sgt == F::one() {
            [step.rw_indices[1], step.rw_indices[0]]
        } else {
            [step.rw_indices[0], step.rw_indices[1]]
        };
        let [a, b] =
            indices.map(|idx| block.rws[idx].stack_value().to_le_bytes());

        self.sign_check_a.assign(
            region,
            offset,
            from_bytes::value(&a[0..1]),
            F::from(128u64),
        )?;
        self.sign_check_b.assign(
            region,
            offset,
            from_bytes::value(&b[0..1]),
            F::from(128u64),
        )?;

        self.comparison_lo.assign(
            region,
            offset,
            from_bytes::value(&a[0..16]),
            from_bytes::value(&b[0..16]),
        )?;
        self.comparison_hi.assign(
            region,
            offset,
            from_bytes::value(&a[16..32]),
            from_bytes::value(&b[16..32]),
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
    fn signed_comparator_gadget_simple() {
        let zero = Word::from_big_endian(&[0u8; 32]);
        let minus_1 = Word::from_big_endian(&[255u8; 16]);
        let minus_2 = {
            let mut bytes = vec![255u8; 15];
            bytes.push(254u8);
            let bytes: [u8; 16] = bytes.try_into().unwrap();
            Word::from_big_endian(&bytes)
        };
        let plus_1 = {
            let mut bytes = vec![0u8; 15];
            bytes.push(1u8);
            let bytes: [u8; 16] = bytes.try_into().unwrap();
            Word::from_big_endian(&bytes)
        };

        // SLT
        test_ok(OpcodeId::SLT, minus_1, zero);
        test_ok(OpcodeId::SLT, zero, plus_1);
        test_ok(OpcodeId::SLT, minus_1, zero);
        test_ok(OpcodeId::SLT, minus_2, plus_1);
        test_ok(OpcodeId::SLT, minus_2, minus_1);

        // SGT
        test_ok(OpcodeId::SGT, zero, minus_1);
        test_ok(OpcodeId::SGT, minus_1, minus_2);
        test_ok(OpcodeId::SGT, plus_1, zero);
        test_ok(OpcodeId::SGT, plus_1, minus_1);
        test_ok(OpcodeId::SGT, plus_1, minus_2);
    }

    #[test]
    fn signed_comparator_gadget_rand() {
        let a = rand_word();
        let b = rand_word();
        test_ok(OpcodeId::SLT, a, b);
        test_ok(OpcodeId::SGT, a, b);
    }
}
