use crate::{
    circuit_input_builder::{CircuitInputStateRef, ExecStep},
    error::ExecError,
    evm::Opcode,
    Error,
};
use eth_types::{evm_types::INVALID_INIT_CODE_FIRST_BYTE, GethExecStep};

#[derive(Clone, Copy, Debug)]
pub struct ErrorCreationCode;

impl Opcode for ErrorCreationCode {
    fn gen_associated_ops(
        state: &mut CircuitInputStateRef,
        geth_steps: &[GethExecStep],
    ) -> Result<Vec<ExecStep>, Error> {
        let geth_step = &geth_steps[0];
        let mut exec_step = state.new_step(geth_step)?;
        exec_step.error = Some(ExecError::InvalidCreationCode);

        let offset = geth_step.stack.nth_last(0)?;
        let length = geth_step.stack.nth_last(1)?;
        state.stack_read(&mut exec_step, geth_step.stack.nth_last_filled(0), offset)?;
        state.stack_read(&mut exec_step, geth_step.stack.nth_last_filled(1), length)?;

        let call = state.call()?;
        assert!(call.is_create() && !length.is_zero());

        // Read the first byte of init code and check it must be 0xef for this error.
        let init_code_first_byte = state.call_ctx()?.memory.0[offset.as_usize()];
        state.memory_read(&mut exec_step, offset.try_into()?)?;
        assert_eq!(init_code_first_byte, INVALID_INIT_CODE_FIRST_BYTE);

        state.handle_return(&mut [&mut exec_step], geth_steps, true)?;
        Ok(vec![exec_step])
    }
}
