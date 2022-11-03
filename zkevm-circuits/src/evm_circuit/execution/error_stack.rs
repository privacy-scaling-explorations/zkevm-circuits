use crate::evm_circuit::{
    execution::ExecutionGadget,
    param::N_BYTES_STACK,
    step::ExecutionState,
    util::{
        common_gadget::RestoreContextGadget,
        constraint_builder::{
            ConstraintBuilder, StepStateTransition,
            Transition::{Delta, Same},
        },
        math_gadget::LtGadget,
        CachedRegion, Cell,
    },
    witness::{Block, Call, ExecStep, Transaction},
};
use crate::table::CallContextFieldTag;
use crate::util::Expr;
use eth_types::Field;
use halo2_proofs::{circuit::Value, plonk::Error};
use itertools::min;

#[derive(Clone, Debug)]
pub(crate) struct ErrorStackGadget<F> {
    opcode: Cell<F>,
    min_stack_pointer: Cell<F>,
    max_stack_pointer: Cell<F>,
    is_overflow: LtGadget<F, N_BYTES_STACK>,
    is_underflow: LtGadget<F, N_BYTES_STACK>,
    restore_context: RestoreContextGadget<F>,
}

impl<F: Field> ExecutionGadget<F> for ErrorStackGadget<F> {
    const NAME: &'static str = "ErrorStack";

    const EXECUTION_STATE: ExecutionState = ExecutionState::ErrorStack;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        let opcode = cb.query_cell();
        cb.opcode_lookup(opcode.expr(), 1.expr());

        let min_stack_pointer = cb.query_cell();
        let max_stack_pointer = cb.query_cell();

        cb.opcode_stack_lookup(
            opcode.expr(),
            min_stack_pointer.expr(),
            max_stack_pointer.expr(),
        );
        // Check current stack pointer is underflow or overflow

        let is_overflow = LtGadget::construct(
            cb,
            cb.curr.state.stack_pointer.expr(),
            min_stack_pointer.expr(),
        );
        let is_underflow = LtGadget::construct(
            cb,
            max_stack_pointer.expr(),
            cb.curr.state.stack_pointer.expr(),
        );

        cb.require_boolean("is_overflow is bool", is_overflow.expr());
        cb.require_boolean("is_underflow is bool", is_underflow.expr());

        // constrain one of [is_underflow, is_overflow] must be true when stack error
        // happens
        cb.require_equal(
            "is_underflow + is_overflow = 1",
            is_underflow.expr() + is_overflow.expr(),
            1.expr(),
        );

        // current call must be failed.
        cb.call_context_lookup(false.expr(), None, CallContextFieldTag::IsSuccess, 0.expr());
        cb.call_context_lookup(
            false.expr(),
            None,
            CallContextFieldTag::IsPersistent,
            0.expr(),
        );

        // Go to EndTx only when is_root
        let is_to_end_tx = cb.next.execution_state_selector([ExecutionState::EndTx]);
        cb.require_equal(
            "Go to EndTx only when is_root",
            cb.curr.state.is_root.expr(),
            is_to_end_tx,
        );

        // When it's a root call
        cb.condition(cb.curr.state.is_root.expr(), |cb| {
            // Do step state transition
            cb.require_step_state_transition(StepStateTransition {
                call_id: Same,
                rw_counter: Delta(2.expr() + cb.curr.state.reversible_write_counter.expr()),
                ..StepStateTransition::any()
            });
        });

        // When it's an internal call, need to restore caller's state as finishing this
        // call. Restore caller state to next StepState
        let restore_context = cb.condition(1.expr() - cb.curr.state.is_root.expr(), |cb| {
            RestoreContextGadget::construct(
                cb,
                0.expr(),
                // rw_offset is handled in construct internally
                0.expr(),
                0.expr(),
                0.expr(),
                0.expr(),
            )
        });

        Self {
            opcode,
            min_stack_pointer,
            max_stack_pointer,
            is_overflow,
            is_underflow,
            restore_context,
        }
    }

    fn assign_exec_step(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        block: &Block<F>,
        _tx: &Transaction,
        call: &Call,
        step: &ExecStep,
    ) -> Result<(), Error> {
        let opcode = step.opcode.unwrap();
        let min_stack = opcode.stack_pair().0 as u64;
        let max_stack = opcode.stack_pair().1 as u64;

        self.opcode
            .assign(region, offset, Value::known(F::from(opcode.as_u64())))?;
        // Inputs/Outputs
        self.min_stack_pointer
            .assign(region, offset, Value::known(F::from(min_stack)))?;
        self.max_stack_pointer
            .assign(region, offset, Value::known(F::from(max_stack)))?;

        self.is_overflow.assign(
            region,
            offset,
            F::from(step.stack_pointer as u64),
            F::from(min_stack),
        )?;
        self.is_underflow.assign(
            region,
            offset,
            F::from(max_stack),
            F::from(step.stack_pointer as u64),
        )?;

        self.restore_context
            .assign(region, offset, block, call, step, 2)?;

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::evm_circuit::{test::run_test_circuit_geth_data_default, witness::block_convert};
    use crate::{evm_circuit::test::rand_word, test_util::{run_test_circuits_with_params, run_test_circuits}};

    use bus_mapping::evm::OpcodeId;
    use eth_types::{
        self, address, bytecode, bytecode::Bytecode, evm_types::GasCost, geth_types::Account,
        geth_types::GethData, Address, ToWord, Word,
    };
    use halo2_proofs::halo2curves::bn256::Fr;
    use bus_mapping::circuit_input_builder::CircuitsParams;

    use mock::{
        eth, gwei, test_ctx::helpers::account_0_code_account_1_no_code, TestContext, MOCK_ACCOUNTS,
    };

    fn test_stack_underflow(value: Word) {
        let bytecode = bytecode! {
            PUSH32(value)
            POP
            POP
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
    fn pop_gadget_underflow() {
        test_stack_underflow(Word::from(0x030201));
        test_stack_underflow(Word::from(0xab));
    }

    #[test]
    fn stack_overflow_simple() {
        test_stack_overflow(OpcodeId::PUSH1, &[1]);
    }

    fn test_stack_overflow(opcode: OpcodeId, bytes: &[u8]) {
        assert!(bytes.len() == opcode.data_len());

        let mut bytecode = bytecode! {
            .write_op(opcode)
        };
        for b in bytes {
            bytecode.write(*b, false);
        }
        // still add 1024 causes stack overflow
        for _ in 0..1025 {
            bytecode.write_op(opcode);
            for b in bytes {
                bytecode.write(*b, false);
            }
        }
        // append final stop op code
        bytecode.write_op(OpcodeId::STOP);

        assert_eq!(
            run_test_circuits_with_params(
                TestContext::<2, 1>::simple_ctx_with_bytecode(bytecode).unwrap(),
                None,
                CircuitsParams {
                    max_rws: 2048,
                    ..Default::default()
                }
            ),
            Ok(())
        );
    }

}
