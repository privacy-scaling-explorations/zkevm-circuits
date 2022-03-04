use super::Opcode;
use crate::circuit_input_builder::{CircuitInputStateRef, ExecStep};
use crate::operation::{CallContextField, CallContextOp, RW};
use crate::Error;
use eth_types::GethExecStep;

#[derive(Clone, Copy, Debug)]
pub(crate) struct Calldatacopy;

impl Opcode for Calldatacopy {
    fn gen_associated_ops(
        state: &mut CircuitInputStateRef,
        exec_step: &mut ExecStep,
        steps: &[GethExecStep],
    ) -> Result<(), Error> {
        let step = &steps[0];
        state.push_stack_op(
            exec_step,
            RW::READ,
            step.stack.nth_last_filled(0),
            step.stack.nth_last(0)?,
        );
        state.push_stack_op(
            exec_step,
            RW::READ,
            step.stack.nth_last_filled(1),
            step.stack.nth_last(1)?,
        );
        state.push_stack_op(
            exec_step,
            RW::READ,
            step.stack.nth_last_filled(2),
            step.stack.nth_last(2)?,
        );
        state.push_op(
            exec_step,
            RW::READ,
            CallContextOp {
                call_id: state.call().call_id,
                field: CallContextField::TxId,
                value: state.tx_ctx.id().into(),
            },
        );

        Ok(())
    }

    fn gen_associated_ops_multi(
        state: &mut CircuitInputStateRef,
        next_steps: &[GethExecStep],
    ) -> Result<(), Error> {
        // Generate an ExecStep of state CALLDATACOPY.
        let mut step = state.new_step(&next_steps[0]);
        Self::gen_associated_ops(state, &mut step, next_steps)?;
        state.push_step_to_tx(step);

        gen_memory_copy_steps(state, next_steps)?;

        Ok(())
    }
}

fn gen_memory_copy_steps(
    _state: &mut CircuitInputStateRef,
    next_steps: &[GethExecStep],
) -> Result<(), Error> {
    let length = next_steps[0].stack.nth_last(0)?;
    if !length.is_zero() {
        // TODO
    }

    Ok(())
}
