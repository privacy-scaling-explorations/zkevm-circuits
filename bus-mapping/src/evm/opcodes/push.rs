use core::ops::Deref;
// Port this to a macro if possible to avoid defining all the PushN
use super::Opcode;
use crate::{
    evm::GlobalCounter,
    exec_trace::ExecutionStep,
    operation::{container::OperationContainer, StackOp, RW},
    Error,
};

/// Number of ops that PUSH1 adds to the container & busmapping
const PUSH1_OP_NUM: usize = 1;

/// Placeholder structure used to implement [`Opcode`] trait over it corresponding to the
/// [`OpcodeId::PUSH1`](crate::evm::OpcodeId::PUSH1) `OpcodeId`.
/// This is responsible of generating all of the associated [`StackOp`]s and place them
/// inside the trace's [`OperationContainer`].
#[derive(Debug, Copy, Clone)]
pub(crate) struct Push1;

impl Opcode for Push1 {
    fn gen_associated_ops(
        &self,
        // Contains the PUSH1 instr
        exec_step: &mut ExecutionStep,
        container: &mut OperationContainer,
        // Contains the next step where we can find the value that was pushed.
        next_steps: &[ExecutionStep],
    ) -> Result<usize, Error> {
        let op = StackOp::new(
            RW::WRITE,
            GlobalCounter::from(exec_step.gc().0 + 1),
            // Get the value and addr from the next step. Being the last position filled with an element in the stack
            next_steps[0].stack().last_filled(),
            next_steps[0]
                .stack()
                .deref()
                .last()
                .cloned()
                .ok_or(Error::InvalidStackPointer)?,
        );

        exec_step
            .bus_mapping_instance_mut()
            .push(container.insert(op));

        Ok(PUSH1_OP_NUM)
    }
}
