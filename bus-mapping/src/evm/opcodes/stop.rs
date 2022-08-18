use super::Opcode;
use crate::{
    circuit_input_builder::{CircuitInputStateRef, ExecStep},
    operation::CallContextField,
    Error,
};
use eth_types::{GethExecStep, ToWord, Word};

/// Placeholder structure used to implement [`Opcode`] trait over it
/// corresponding to the [`OpcodeId::STOP`](crate::evm::OpcodeId::STOP)
/// `OpcodeId`. This is responsible of generating all of the associated
/// operations and place them inside the trace's
/// [`OperationContainer`](crate::operation::OperationContainer). In the case of
/// STOP, it simply does not add anything.
#[derive(Debug, Copy, Clone)]
pub(crate) struct Stop;

impl Opcode for Stop {
    fn gen_associated_ops(
        state: &mut CircuitInputStateRef,
        geth_steps: &[GethExecStep],
    ) -> Result<Vec<ExecStep>, Error> {
        let geth_step = &geth_steps[0];

        let mut exec_step = state.new_step(geth_step)?;

        let call = state.call()?.clone();

        state.call_context_read(
            &mut exec_step,
            call.call_id,
            CallContextField::IsSuccess,
            1.into(),
        );
        // need to move this into handle_restore_context.
        state.call_context_read(
            &mut exec_step,
            call.call_id,
            CallContextField::IsSuccess,
            call.is_success.to_word(),
        );

        if !call.is_root {
            let caller = state.caller()?.clone();
            state.call_context_read(
                &mut exec_step,
                call.call_id,
                CallContextField::CallerId,
                caller.call_id.into(),
            );

            let geth_step_next = &geth_steps[1];
            let caller_gas_left = geth_step_next.gas.0 - geth_step.gas.0;
            for (field, value) in [
                (CallContextField::IsRoot, (caller.is_root as u64).into()),
                (
                    CallContextField::IsCreate,
                    (caller.is_create() as u64).into(),
                ),
                (CallContextField::CodeHash, caller.code_hash.to_word()),
                (CallContextField::ProgramCounter, geth_step_next.pc.0.into()),
                (
                    CallContextField::StackPointer,
                    geth_step_next.stack.stack_pointer().0.into(),
                ),
                (CallContextField::GasLeft, caller_gas_left.into()),
                (
                    CallContextField::MemorySize,
                    geth_step_next.memory.word_size().into(),
                ),
                (
                    CallContextField::ReversibleWriteCounter,
                    state.caller_ctx()?.reversible_write_counter.into(),
                ),
            ] {
                state.call_context_read(&mut exec_step, caller.call_id, field, value);
            }

            // let [last_callee_return_data_offset, last_callee_return_data_length] =
            //     match geth_step.op {
            //         OpcodeId::STOP => [Word::zero(); 2],
            //         OpcodeId::REVERT | OpcodeId::RETURN => {
            //             // TODO: move this back into the return bus mapping.
            //             let offset = geth_step.stack.nth_last(0)?;
            //             let length = geth_step.stack.nth_last(1)?;
            //             [offset, length]
            //         }
            //         _ => unreachable!(),
            //     };
            //
            // dbg!(
            //     last_callee_return_data_offset,
            //     last_callee_return_data_length
            // );
            for (field, value) in [
                (CallContextField::LastCalleeId, call.call_id.into()),
                (CallContextField::LastCalleeReturnDataOffset, Word::zero()),
                (CallContextField::LastCalleeReturnDataLength, Word::zero()),
            ] {
                state.call_context_write(&mut exec_step, caller.call_id, field, value);
            }
        }

        state.handle_return(&geth_steps[0])?;

        Ok(vec![exec_step])
    }
}
