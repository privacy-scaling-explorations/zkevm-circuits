use crate::circuit_input_builder::{CircuitInputStateRef, ExecStep};
use crate::evm::{Opcode, OpcodeId};
use crate::Error;
use eth_types::{GethExecStep, ToAddress, ToWord};

#[derive(Debug, Copy, Clone)]
pub(crate) struct ErrorInvalidJump;

impl Opcode for ErrorInvalidJump {
    fn gen_associated_ops(
        state: &mut CircuitInputStateRef,
        geth_steps: &[GethExecStep],
    ) -> Result<Vec<ExecStep>, Error> {
        let geth_step = &geth_steps[0];
        let mut exec_step = state.new_step(geth_step)?;
        let next_step = if geth_steps.len() > 1 {
            Some(&geth_steps[1])
        } else {
            None
        };
        exec_step.error = state.get_step_err(geth_step, next_step).unwrap();
        // assert op code can only be JUMP or JUMPI
        assert!(geth_step.op == OpcodeId::JUMP || geth_step.op == OpcodeId::JUMPI);
        let dest = geth_steps[0].stack.last()?.to_address();
        state.stack_read(
            &mut exec_step,
            geth_step.stack.last_filled(),
            dest.to_word(),
        )?;

        // `IsSuccess` call context operation is added in gen_restore_context_ops

        state.gen_restore_context_ops(&mut exec_step, geth_steps)?;
        state.handle_return(geth_step)?;
        Ok(vec![exec_step])
    }
}
