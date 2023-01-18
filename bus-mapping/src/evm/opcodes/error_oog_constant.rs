use crate::circuit_input_builder::{CircuitInputStateRef, ExecStep};
use crate::evm::Opcode;
use crate::operation::CallContextField;
use crate::Error;
use eth_types::GethExecStep;

#[derive(Debug, Copy, Clone)]
pub(crate) struct ErrorOogConstant;

impl Opcode for ErrorOogConstant {
    fn gen_associated_ops(
        state: &mut CircuitInputStateRef,
        geth_steps: &[GethExecStep],
    ) -> Result<Vec<ExecStep>, Error> {
        let geth_step = &geth_steps[0];
        let mut exec_step = state.new_step(geth_step)?;
        let next_step = geth_steps.get(1);
        exec_step.error = state.get_step_err(geth_step, next_step).unwrap();

        let call = state.call()?.clone();
        // call failed
        state.call_context_write(
            &mut exec_step,
            call.call_id,
            CallContextField::IsSuccess,
            0.into(),
        );
        // remove all available gas for this call or root context
        state.call_context_write(
            &mut exec_step,
            call.call_id,
            CallContextField::GasLeft,
            0.into(),
        );
        // XXX: any more to do?

        if !call.is_root {
            state.gen_restore_context_ops(&mut exec_step, geth_steps)?;
        }

        state.handle_return(geth_step)?;
        Ok(vec![exec_step])
    }
}
