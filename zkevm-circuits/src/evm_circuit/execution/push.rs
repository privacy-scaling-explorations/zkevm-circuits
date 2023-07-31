use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        param::N_BYTES_PROGRAM_COUNTER,
        step::ExecutionState,
        util::{
            common_gadget::SameContextGadget,
            constraint_builder::{
                ConstrainBuilderCommon, EVMConstraintBuilder, StepStateTransition,
                Transition::Delta,
            },
            math_gadget::LtGadget,
            sum, CachedRegion, Cell,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    util::{
        word::{Word32Cell, WordExpr},
        Expr,
    },
};
use array_init::array_init;
use eth_types::{evm_types::OpcodeId, Field};
use halo2_proofs::{circuit::Value, plonk::Error};

#[derive(Clone, Debug)]
pub(crate) struct PushGadget<F> {
    same_context: SameContextGadget<F>,
    value: Word32Cell<F>,
    is_pushed: [Cell<F>; 32],
    is_padding: [Cell<F>; 32],
    code_length: Cell<F>,
    is_out_of_bound: LtGadget<F, N_BYTES_PROGRAM_COUNTER>,
}

impl<F: Field> ExecutionGadget<F> for PushGadget<F> {
    const NAME: &'static str = "PUSH";

    const EXECUTION_STATE: ExecutionState = ExecutionState::PUSH;

    fn configure(cb: &mut EVMConstraintBuilder<F>) -> Self {
        let opcode = cb.query_cell();
        let code_length = cb.query_cell();
        let code_length_left = code_length.expr() - cb.curr.state.program_counter.expr() - 1.expr();

        let value = cb.query_word32();
        // Query selectors for each opcode_lookup to know whether the current byte needs to be
        // pushed
        let is_pushed = array_init(|_| cb.query_bool());

        // Query selectors for each opcode_lookup to know whether the current byte is actually
        // padding
        let is_padding = array_init(|_| cb.query_bool());

        // Fetch the bytecode length from the bytecode table.
        let code_hash = cb.curr.state.code_hash.clone();
        cb.bytecode_length(code_hash.to_word(), code_length.expr());

        // Deduce the number of bytes to push.
        let num_pushed = opcode.expr() - OpcodeId::PUSH1.as_u64().expr() + 1.expr();

        // If the number of bytes that needs to be pushed is greater
        // than the size of the bytecode left, then we are out of range.
        let is_out_of_bound: LtGadget<F, N_BYTES_PROGRAM_COUNTER> =
            LtGadget::construct(cb, code_length_left.clone(), num_pushed.clone());

        // Expected number of padding
        let num_padding: halo2_proofs::plonk::Expression<F> =
            is_out_of_bound.expr() * (num_pushed.clone() - code_length_left);

        // The pushed bytes are viewed as left-padded big-endian, but our random
        // linear combination uses little-endian, so we lookup from the LSB
        // which has index (program_counter + num_pushed), and then move left
        // (program_counter + num_pushed - idx) to lookup all 32 bytes
        // conditionally by selectors.
        // For PUSH2 as an example, we lookup from byte0, byte1, ..., byte31,
        // where the byte2 is actually the PUSH2 itself, and lookup are only
        // enabled for byte0 and byte1.
        //
        //                    program_counter    program_counter + num_pushed(2)
        //                           ▼                     ▼
        //   [byte31,     ...,     byte2,     byte1,     byte0]
        //
        // First is_pushed (resp. is_padding) will always be 1 (resp. 1)
        let mut pu_prev = 1.expr();
        let mut pa_prev = 1.expr();
        for (idx, (pu, pa)) in is_pushed.iter().zip(is_padding.iter()).enumerate() {
            let byte = &value.limbs[idx];
            let index: halo2_proofs::plonk::Expression<F> =
                cb.curr.state.program_counter.expr() + num_pushed.clone() - idx.expr();

            // is_pushed can transit from 1 to 0 only once
            // as 1 - [1, 1, 1, ..., 1, 0, 0, 0]
            cb.require_boolean(
                "Constrain is_pushed can only transit from 1 to 0",
                pu_prev - pu.expr(),
            );

            // is_padding can transit from 1 to 0 only once
            // as 1 - [1, 1, 0, ..., 0, 0, 0, 0] (out of bound)
            // as 1 - [0, 0, 0, ..., 0, 0, 0, 0] (not out of bound)
            cb.require_boolean(
                "Constrain is_padding can only transit from 1 to 0",
                pa_prev - pa.expr(),
            );

            // byte is 0 if it is either not pushed or padding
            cb.require_zero(
                "Constrain byte == 0 when is_pushed == 0 OR is_padding == 1",
                byte.expr() * (pa.expr() + (1.expr() - pu.expr())),
            );

            // if byte is pushed and not padding, we check consistency with bytecode table
            cb.condition(pu.expr() * (1.expr() - pa.expr()), |cb| {
                cb.opcode_lookup_at(index, byte.expr(), 0.expr())
            });

            pu_prev = pu.expr();
            pa_prev = pa.expr();
        }

        // Sum of selectors is_pushed needs to be exactly the number of bytes
        // that needs to be pushed
        cb.require_equal(
            "Constrain sum of is_pushed equal to num_pushed",
            sum::expr(&is_pushed),
            num_pushed.expr(),
        );

        // Sum of selectors is_padding needs to be exactly the number of padded bytes
        cb.require_equal(
            "Constrain sum of is_padding equal to num_padding",
            sum::expr(&is_padding),
            num_padding.expr(),
        );

        // Push the value on the stack
        cb.stack_push(value.to_word());

        // State transition
        // `program_counter` needs to be increased by number of bytes pushed + 1
        let step_state_transition = StepStateTransition {
            rw_counter: Delta(1.expr()),
            program_counter: Delta(opcode.expr() - (OpcodeId::PUSH1.as_u64() - 2).expr()),
            stack_pointer: Delta((-1).expr()),
            gas_left: Delta(-OpcodeId::PUSH1.constant_gas_cost().expr()),
            ..Default::default()
        };
        let same_context = SameContextGadget::construct(cb, opcode, step_state_transition);

        Self {
            same_context,
            value,
            is_pushed,
            is_padding,
            code_length,
            is_out_of_bound,
        }
    }

    fn assign_exec_step(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        block: &Block<F>,
        _: &Transaction,
        call: &Call,
        step: &ExecStep,
    ) -> Result<(), Error> {
        self.same_context.assign_exec_step(region, offset, step)?;

        let opcode = step.opcode().unwrap();
        let num_pushed = opcode.postfix().expect("opcode with postfix");
        let npushed = num_pushed as usize;

        let bytecode = block
            .bytecodes
            .get_from_h256(&call.code_hash)
            .expect("could not find current environment's bytecode");

        let code_length = bytecode.codesize() as u64;
        self.code_length
            .assign(region, offset, Value::known(F::from(code_length)))?;

        let code_length_left = (code_length - step.pc - 1) as usize;
        self.is_out_of_bound.assign(
            region,
            offset,
            F::from(code_length_left as u64),
            F::from(num_pushed as u64),
        )?;

        let value = block.get_rws(step, 0).stack_value();
        self.value.assign_u256(region, offset, value)?;

        let is_out_of_bound = code_length_left < npushed;
        let out_of_bound_padding = if is_out_of_bound {
            npushed - code_length_left
        } else {
            0
        };
        for (i, (pu, pa)) in self
            .is_pushed
            .iter()
            .zip(self.is_padding.iter())
            .enumerate()
        {
            let pushed = i < npushed;
            let padding = i < out_of_bound_padding;
            pu.assign(region, offset, Value::known(F::from(pushed as u64)))?;
            pa.assign(region, offset, Value::known(F::from(padding as u64)))?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::{evm_circuit::test::rand_bytes, test_util::CircuitTestBuilder};
    use eth_types::{bytecode, evm_types::OpcodeId};
    use mock::TestContext;

    fn test_ok(opcode: OpcodeId, bytes: &[u8]) {
        assert!(bytes.len() <= opcode.data_len());

        let mut bytecode = bytecode! {
            .write_op(opcode)
        };
        for b in bytes {
            bytecode.write(*b, false);
        }
        if bytes.len() == opcode.data_len() {
            bytecode.op_stop();
        }

        CircuitTestBuilder::new_from_test_ctx(
            TestContext::<2, 1>::simple_ctx_with_bytecode(bytecode).unwrap(),
        )
        .run();
    }

    #[test]
    fn push_gadget_simple() {
        test_ok(OpcodeId::PUSH1, &[1]);
        test_ok(OpcodeId::PUSH2, &[1, 2]);
        test_ok(OpcodeId::PUSH5, &[1, 2, 3, 4, 5]);
        test_ok(
            OpcodeId::PUSH31,
            &[
                1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
                24, 25, 26, 27, 28, 29, 30, 31,
            ],
        );
        test_ok(
            OpcodeId::PUSH32,
            &[
                1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
                24, 25, 26, 27, 28, 29, 30, 31, 32,
            ],
        );
        test_ok(OpcodeId::PUSH16, &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
    }

    #[test]
    #[ignore]
    fn push_gadget_rand() {
        for (idx, opcode) in vec![
            OpcodeId::PUSH1,
            OpcodeId::PUSH2,
            OpcodeId::PUSH3,
            OpcodeId::PUSH4,
            OpcodeId::PUSH5,
            OpcodeId::PUSH6,
            OpcodeId::PUSH7,
            OpcodeId::PUSH8,
            OpcodeId::PUSH9,
            OpcodeId::PUSH10,
            OpcodeId::PUSH11,
            OpcodeId::PUSH12,
            OpcodeId::PUSH13,
            OpcodeId::PUSH14,
            OpcodeId::PUSH15,
            OpcodeId::PUSH16,
            OpcodeId::PUSH17,
            OpcodeId::PUSH18,
            OpcodeId::PUSH19,
            OpcodeId::PUSH20,
            OpcodeId::PUSH21,
            OpcodeId::PUSH22,
            OpcodeId::PUSH23,
            OpcodeId::PUSH24,
            OpcodeId::PUSH25,
            OpcodeId::PUSH26,
            OpcodeId::PUSH27,
            OpcodeId::PUSH28,
            OpcodeId::PUSH29,
            OpcodeId::PUSH30,
            OpcodeId::PUSH31,
            OpcodeId::PUSH32,
        ]
        .into_iter()
        .enumerate()
        {
            test_ok(opcode, &rand_bytes(idx + 1));
        }
    }
}
