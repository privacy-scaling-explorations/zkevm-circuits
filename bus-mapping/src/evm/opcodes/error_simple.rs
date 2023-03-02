use crate::circuit_input_builder::{CircuitInputStateRef, ExecStep};
use crate::evm::Opcode;
use crate::Error;
use eth_types::GethExecStep;

#[derive(Debug, Copy, Clone)]
pub(crate) struct ErrorSimple;

// ErrorSimple is for stack error, oog constant, invalid op code buss mapping.
// in the future may refactor more simple error buss mapping into it.
impl Opcode for ErrorSimple {
    fn gen_associated_ops(
        state: &mut CircuitInputStateRef,
        geth_steps: &[GethExecStep],
    ) -> Result<Vec<ExecStep>, Error> {
        let geth_step = &geth_steps[0];
        let mut exec_step = state.new_step(geth_step)?;
        let next_step = geth_steps.get(1);
        exec_step.error = state.get_step_err(geth_step, next_step).unwrap();

        // handles all required steps
        state.gen_restore_context_ops(&mut exec_step, geth_steps)?;
        state.handle_return(geth_step)?;

        Ok(vec![exec_step])
    }
}
