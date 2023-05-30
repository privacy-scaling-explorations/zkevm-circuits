use super::{Opcode, OpcodeId};
use crate::{
    circuit_input_builder::{CircuitInputStateRef, ExecStep, MaybeParams},
    error::{ExecError, OogError},
    Error,
};
use eth_types::GethExecStep;

/// Placeholder structure used to implement [`Opcode`] trait over it
/// corresponding to the [`OogError::Exp`](crate::error::OogError::Exp).
#[derive(Clone, Copy, Debug)]
pub(crate) struct OOGExp;

impl Opcode for OOGExp {
    fn gen_associated_ops<M: MaybeParams>(
        state: &mut CircuitInputStateRef<M>,
        geth_steps: &[GethExecStep],
    ) -> Result<Vec<ExecStep>, Error> {
        let geth_step = &geth_steps[0];
        debug_assert_eq!(geth_step.op, OpcodeId::EXP);

        let mut exec_step = state.new_step(geth_step)?;
        exec_step.error = Some(ExecError::OutOfGas(OogError::Exp));

        for i in 0..2 {
            state.stack_read(
                &mut exec_step,
                geth_step.stack.nth_last_filled(i),
                geth_step.stack.nth_last(i)?,
            )?;
        }

        state.handle_return(&mut exec_step, geth_steps, true)?;
        Ok(vec![exec_step])
    }
}
