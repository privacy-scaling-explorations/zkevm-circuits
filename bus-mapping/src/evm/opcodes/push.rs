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

#[cfg(test)]
mod push_tests {
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
    fn push1_opcode_impl() -> Result<(), Error> {
        let code = bytecode! {
            #[start]
            PUSH1(0x80u64)
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

        // Generate Step1 corresponding to PUSH1 80
        let mut step_1 = ExecutionStep {
            memory: mem_map,
            stack: Stack::empty(),
            storage: Storage::empty(),
            instruction: OpcodeId::PUSH1,
            gas_info: gas_info!(gas, FASTEST),
            depth: 1u8,
            pc: advance_pc!(pc),
            gc: advance_gc!(gc),
            bus_mapping_instance: vec![],
        };

        // Add StackOp associated to the 0x80 push at the latest Stack pos.
        step_1
            .bus_mapping_instance_mut()
            .push(container.insert(StackOp::new(
                RW::WRITE,
                advance_gc!(gc),
                StackAddress::from(1023),
                EvmWord::from(0x80u8),
            )));

        // Compare first step bus mapping instance
        assert_eq!(
            obtained_exec_trace[0].bus_mapping_instance(),
            step_1.bus_mapping_instance()
        );
        // Compare first step entirely
        assert_eq!(obtained_exec_trace[0], step_1);

        // Compare containers
        assert_eq!(obtained_exec_trace.container, container);

        Ok(())
    }
}
