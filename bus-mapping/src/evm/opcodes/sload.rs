use super::Opcode;
use crate::{
    exec_trace::ExecutionStep,
    operation::{
        container::OperationContainer, EthAddress, StackOp, StorageOp, RW,
    },
    Error,
};

/// Placeholder structure used to implement [`Opcode`] trait over it corresponding to the
/// [`OpcodeId::SLOAD`](crate::evm::OpcodeId::SLOAD) `OpcodeId`.
#[derive(Debug, Copy, Clone)]
pub(crate) struct Sload;

impl Opcode for Sload {
    #[allow(unused_variables)]
    fn gen_associated_ops(
        &self,
        exec_step: &mut ExecutionStep,
        container: &mut OperationContainer,
        next_steps: &[ExecutionStep],
    ) -> Result<usize, Error> {
        let gc_idx_start = exec_step.gc().0;
        let mut gc_idx = gc_idx_start;

        // First stack read
        let stack_value_read = exec_step
            .stack()
            .last()
            .cloned()
            .ok_or(Error::InvalidStackPointer)?;
        let stack_position = exec_step.stack().last_filled();

        // Manage first stack read at latest stack position
        gc_idx += 1;
        exec_step.bus_mapping_instance_mut().push(container.insert(
            StackOp::new(
                RW::READ,
                gc_idx.into(),
                stack_position,
                stack_value_read,
            ),
        ));

        // Storage read
        let storage_value_read =
            *exec_step.storage().get_or_err(&stack_value_read)?;
        gc_idx += 1;
        exec_step.bus_mapping_instance_mut().push(container.insert(
            StorageOp::new(
                RW::READ,
                gc_idx.into(),
                EthAddress([0u8; 20]), // TODO: Fill with the correct value
                stack_value_read,
                storage_value_read,
                storage_value_read,
            ),
        ));

        // First stack write
        gc_idx += 1;
        exec_step.bus_mapping_instance_mut().push(container.insert(
            StackOp::new(
                RW::WRITE,
                gc_idx.into(),
                stack_position,
                storage_value_read,
            ),
        ));

        Ok(gc_idx - gc_idx_start)
    }
}

#[cfg(test)]
mod sload_tests {
    use super::*;
    use crate::{
        bytecode,
        evm::{
            EvmWord, GasCost, GasInfo, GlobalCounter, Memory, OpcodeId,
            ProgramCounter, Stack, StackAddress, Storage,
        },
        external_tracer, BlockConstants, ExecutionTrace,
    };
    use pasta_curves::pallas::Scalar;
    use std::collections::HashMap;
    use std::iter::FromIterator;

    #[test]
    fn sload_opcode_impl() -> Result<(), Error> {
        let code = bytecode! {
            // Write 0x6f to storage slot 0
            PUSH1(0x6fu64)
            PUSH1(0x00u64)
            SSTORE

            // Load storage slot 0
            PUSH1(0x00u64)
            #[start]
            SLOAD
            STOP
        };

        let block_ctants = BlockConstants::default();

        // Get the execution steps from the external tracer
        let obtained_steps = &external_tracer::trace(&block_ctants, &code)?
            [code.get_pos("start")..];

        // Obtained trace computation
        let obtained_exec_trace = ExecutionTrace::<Scalar>::new(
            obtained_steps.to_vec(),
            block_ctants,
        )?;

        let mut container = OperationContainer::new();
        let mut gc = GlobalCounter(0);

        // Start from the same pc and gas limit
        let mut pc = obtained_steps[0].pc();
        let mut gas = obtained_steps[0].gas_info().gas;

        // Generate Step1 corresponding to SLOAD
        let mut step_1 = ExecutionStep {
            memory: Memory::empty(),
            stack: Stack(vec![EvmWord::from(0x0u32)]),
            storage: Storage::new(HashMap::from_iter([(
                EvmWord::from(0x0u32),
                EvmWord::from(0x6fu32),
            )])),
            instruction: OpcodeId::SLOAD,
            gas_info: gas_info!(gas, WARM_STORAGE_READ_COST),
            depth: 1u8,
            pc: advance_pc!(pc),
            gc: advance_gc!(gc),
            bus_mapping_instance: vec![],
        };

        // Add StackOp associated to the stack pop.
        step_1
            .bus_mapping_instance_mut()
            .push(container.insert(StackOp::new(
                RW::READ,
                advance_gc!(gc),
                StackAddress::from(1023),
                EvmWord::from(0x0u32),
            )));
        // Add StorageOp associated to the storage read.
        step_1.bus_mapping_instance_mut().push(container.insert(
            StorageOp::new(
                RW::READ,
                advance_gc!(gc),
                EthAddress([0u8; 20]), // TODO: Fill with the correct value
                EvmWord::from(0x0u32),
                EvmWord::from(0x6fu32),
                EvmWord::from(0x6fu32),
            ),
        ));
        // Add StackOp associated to the stack push.
        step_1
            .bus_mapping_instance_mut()
            .push(container.insert(StackOp::new(
                RW::WRITE,
                advance_gc!(gc),
                StackAddress::from(1023),
                EvmWord::from(0x6fu32),
            )));

        assert_eq!(
            obtained_exec_trace[0].bus_mapping_instance(),
            step_1.bus_mapping_instance()
        );
        assert_eq!(obtained_exec_trace[0], step_1);
        assert_eq!(obtained_exec_trace.container, container);

        Ok(())
    }
}
