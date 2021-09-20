use super::Opcode;
use crate::{exec_trace::ExecutionStep, operation::OperationContainer, Error};

/// Number of ops that STOP adds to the container & busmapping
const STOP_OP_NUM: usize = 0;

/// Structure used to implement [`Opcode`] trait over it corresponding to the
/// `STOP` [`Instruction`](crate::evm::instruction::Instruction).
#[derive(Debug, Copy, Clone)]
pub(crate) struct Stop;

impl Opcode for Stop {
    #[allow(unused_variables)]
    fn gen_associated_ops(
        &self,
        exec_step: &mut ExecutionStep,
        container: &mut OperationContainer,
        next_steps: &[ExecutionStep],
    ) -> Result<usize, Error> {
        // Stop does not generate any operations
        Ok(STOP_OP_NUM)
    }
}
