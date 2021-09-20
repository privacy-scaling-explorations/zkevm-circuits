use super::Opcode;
use crate::{
    evm::GlobalCounter,
    exec_trace::ExecutionStep,
    operation::{container::OperationContainer, MemoryOp, StackOp, RW},
    Error,
};
use core::ops::Deref;

/// Number of ops that MLOAD adds to the container & busmapping
const MLOAD_OP_NUM: usize = 3;

/// Structure used to implement [`Opcode`] trait over it corresponding to the
/// `MLOAD` [`Instruction`](crate::evm::instruction::Instruction).
#[derive(Debug, Copy, Clone)]
pub(crate) struct Mload;

impl Opcode for Mload {
    #[allow(unused_variables)]
    fn gen_associated_ops(
        &self,
        exec_step: &mut ExecutionStep,
        container: &mut OperationContainer,
        next_steps: &[ExecutionStep],
    ) -> Result<usize, Error> {
        //
        // First stack read
        //
        let stack_value_read = exec_step
            .stack()
            .deref()
            .last()
            .cloned()
            .ok_or_else(|| Error::InvalidStackPointer)?;
        let stack_position = exec_step.stack().last_filled();

        // Manage first stack read at latest stack position
        let stack_read = StackOp::new(
            RW::READ,
            GlobalCounter::from(exec_step.gc().0 + 1),
            stack_position,
            stack_value_read.clone(),
        );

        exec_step
            .bus_mapping_instance_mut()
            .push(container.insert(stack_read));

        //
        // First mem read
        //
        let last_mem_item = exec_step
            .memory()
            .deref()
            .last()
            .cloned()
            .ok_or_else(|| Error::InvalidMemoryPointer)?;

        // Read operation at memory address: stack_read.value
        let mem_read = MemoryOp::new(
            RW::READ,
            GlobalCounter::from(exec_step.gc().0 + 2),
            last_mem_item.0,
            last_mem_item.1.clone(),
        );

        exec_step
            .bus_mapping_instance_mut()
            .push(container.insert(mem_read));

        //
        // First stack write
        //
        let stack_write = StackOp::new(
            RW::WRITE,
            GlobalCounter::from(exec_step.gc().0 + 3),
            stack_position,
            last_mem_item.1,
        );
        exec_step
            .bus_mapping_instance_mut()
            .push(container.insert(stack_write));

        Ok(MLOAD_OP_NUM)
    }
}
