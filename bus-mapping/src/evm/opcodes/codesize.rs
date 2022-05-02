use crate::{
    circuit_input_builder::{CircuitInputStateRef, ExecStep},
    operation::RW,
    Error,
};

use eth_types::GethExecStep;

use super::Opcode;

#[derive(Clone, Copy, Debug)]
pub(crate) struct Codesize;

impl Opcode for Codesize {
    fn gen_associated_ops(
        state: &mut CircuitInputStateRef,
        geth_steps: &[GethExecStep],
    ) -> Result<Vec<ExecStep>, Error> {
        let geth_step = &geth_steps[0];
        let mut exec_step = state.new_step(geth_step)?;

        let code_source = state.call()?.code_hash;
        let code = state.code(code_source)?;
        let codesize = code.len();

        assert_eq!(codesize, geth_steps[1].stack.last()?.as_usize());

        state.push_stack_op(
            &mut exec_step,
            RW::WRITE,
            geth_step.stack.last_filled().map(|a| a - 1),
            codesize.into(),
        )?;

        Ok(vec![exec_step])
    }
}
