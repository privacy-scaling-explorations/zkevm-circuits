use super::Opcode;
use crate::{
    evm::{GlobalCounter, MemoryAddress},
    exec_trace::ExecutionStep,
    operation::{container::OperationContainer, MemoryOp, StackOp, RW},
    Error,
};
use core::convert::TryInto;

/// Number of ops that MLOAD adds to the container & busmapping
const MLOAD_OP_NUM: usize = 34;

/// Placeholder structure used to implement [`Opcode`] trait over it corresponding to the
/// [`OpcodeId::MLOAD`](crate::evm::OpcodeId::MLOAD) `OpcodeId`.
/// This is responsible of generating all of the associated [`StackOp`]s and [`MemoryOp`]s and place them
/// inside the trace's [`OperationContainer`].
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
        let mut gc_idx = exec_step.gc().0;
        //
        // First stack read
        //
        let stack_value_read = exec_step
            .stack()
            .last()
            .cloned()
            .ok_or(Error::InvalidStackPointer)?;
        let stack_position = exec_step.stack().last_filled();

        // Manage first stack read at latest stack position
        gc_idx += 1;
        let stack_read = StackOp::new(
            RW::READ,
            GlobalCounter::from(gc_idx),
            stack_position,
            stack_value_read,
        );

        exec_step
            .bus_mapping_instance_mut()
            .push(container.insert(stack_read));

        //
        // First mem read -> 32 MemoryOp generated.
        //
        let mut mem_read_addr: MemoryAddress = stack_value_read.try_into()?;
        let mem_read_value = next_steps[0].memory().read_word(mem_read_addr)?;

        mem_read_value.inner().iter().for_each(|value_byte| {
            // Update next GC index
            gc_idx += 1;

            // / Read operation at memory address: `stack_read.value + n`
            let mem_read_op = MemoryOp::new(
                RW::READ,
                gc_idx.into(),
                mem_read_addr,
                *value_byte,
            );

            // Push op inside the container and bus_mapping_instance of the step.
            exec_step
                .bus_mapping_instance_mut()
                .push(container.insert(mem_read_op));
            // Update mem_read_addr to next byte's one
            mem_read_addr += MemoryAddress::from(1);
        });

        //
        // First stack write
        //
        gc_idx += 1;
        let stack_write = StackOp::new(
            RW::WRITE,
            gc_idx.into(),
            stack_position,
            mem_read_value,
        );
        exec_step
            .bus_mapping_instance_mut()
            .push(container.insert(stack_write));

        Ok(MLOAD_OP_NUM)
    }
}

#[cfg(test)]
mod mload_tests {
    use super::*;
    use crate::{
        bytecode,
        evm::{
            EvmWord, GasCost, GasInfo, OpcodeId, ProgramCounter, Stack,
            StackAddress, Storage,
        },
        external_tracer, BlockConstants, ExecutionTrace,
    };
    use pasta_curves::pallas::Scalar;

    #[test]
    fn mload_opcode_impl() -> Result<(), Error> {
        let code = bytecode! {
            .setup_state()

            PUSH1(0x40u64)
            #[start]
            MLOAD
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

        // The memory is the same in both steps as none of them edits the
        // memory of the EVM.
        let mem_map = obtained_steps[0].memory.clone();

        // Generate Step1 corresponding to PUSH1 40
        let mut step_1 = ExecutionStep {
            memory: mem_map.clone(),
            stack: Stack(vec![EvmWord::from(0x40u8)]),
            storage: Storage::empty(),
            instruction: OpcodeId::MLOAD,
            gas_info: gas_info!(gas, FASTEST),
            depth: 1u8,
            pc: advance_pc!(pc),
            gc: advance_gc!(gc),
            bus_mapping_instance: vec![],
        };

        // Add StackOp associated to the 0x40 read from the latest Stack pos.
        step_1
            .bus_mapping_instance_mut()
            .push(container.insert(StackOp::new(
                RW::READ,
                advance_gc!(gc),
                StackAddress::from(1023),
                EvmWord::from(0x40u8),
            )));

        // Add the 32 MemoryOp generated from the Memory read at addr 0x40<->0x80 for each byte.
        EvmWord::from(0x80u8)
            .inner()
            .iter()
            .enumerate()
            .map(|(idx, byte)| (idx + 0x40, byte))
            .for_each(|(idx, byte)| {
                step_1.bus_mapping_instance_mut().push(container.insert(
                    MemoryOp::new(RW::READ, advance_gc!(gc), idx.into(), *byte),
                ));
            });

        // Add the last Stack write
        step_1
            .bus_mapping_instance_mut()
            .push(container.insert(StackOp::new(
                RW::WRITE,
                advance_gc!(gc),
                StackAddress::from(1023),
                EvmWord::from(0x80u8),
            )));

        // Generate Step1 corresponding to PUSH1 40
        let step_2 = ExecutionStep {
            memory: mem_map,
            stack: Stack(vec![EvmWord::from(0x80u8)]),
            storage: Storage::empty(),
            instruction: OpcodeId::STOP,
            gas_info: gas_info!(gas, ZERO),
            depth: 1u8,
            pc: advance_pc!(pc),
            gc: advance_gc!(gc),
            bus_mapping_instance: vec![],
        };

        // Compare first step bus mapping instance
        assert_eq!(
            obtained_exec_trace[0].bus_mapping_instance,
            step_1.bus_mapping_instance
        );
        // Compare first step entirely
        assert_eq!(obtained_exec_trace[0], step_1);

        // Compare second step bus mapping instance
        assert_eq!(
            obtained_exec_trace[1].bus_mapping_instance,
            step_2.bus_mapping_instance
        );
        // Compare second step entirely
        assert_eq!(obtained_exec_trace[1], step_2);

        // Compare containers
        assert_eq!(obtained_exec_trace.container, container);

        Ok(())
    }
}
