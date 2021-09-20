use super::Opcode;
use crate::{exec_trace::ExecutionStep, operation::OperationContainer, Error};

/// Number of ops that STOP adds to the container & busmapping
const STOP_OP_NUM: usize = 0;

/// Placeholder structure used to implement [`Opcode`] trait over it corresponding to the
/// [`OpcodeId::STOP`](crate::evm::OpcodeId::STOP) `OpcodeId`.
/// This is responsible of generating all of the associated operations and place them
/// inside the trace's [`OperationContainer`].
/// In the case of STOP, it simply does not add anything.
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
