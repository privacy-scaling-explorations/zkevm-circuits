use super::Opcode;
use crate::{
    exec_trace::{Context, ExecutionStep},
    Error,
};

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
        ctx: &mut Context,
        exec_step: &mut ExecutionStep,
        next_steps: &[ExecutionStep],
    ) -> Result<(), Error> {
        // Stop does not generate any operations
        Ok(())
    }
}
