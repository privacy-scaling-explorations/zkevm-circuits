use core::ops::Deref;
use super::Opcode;
use crate::{
    exec_trace::{ExecutionStep, TraceContext},
    operation::{StackOp, RW},
    Error,
};

/// Placeholder structure used to implement [`Opcode`] trait over it corresponding to the
/// [`OpcodeId::POP`](crate::evm::OpcodeId::POP) `OpcodeId`.
/// This is responsible of generating all of the associated [`StackOp`]s and place them
/// inside the trace's [`OperationContainer`](crate::operation::OperationContainer).
#[derive(Debug, Copy, Clone)]
pub(crate) struct Pop;

impl Opcode for Pop {
    fn gen_associated_ops(
        &self,
        ctx: &mut TraceContext,
        // Contains the POP instr and the value which is last placed in the stack.
        exec_step: &mut ExecutionStep,
        // Contains the next step.
        next_steps: &[ExecutionStep],
    ) -> Result<(), Error> {
        ctx.pop_op(
            exec_step,
            StackOp::new(
                RW::READ,
                // Get the value and addr from the execution step and reads the value of the last filled stack element
                exec_step.stack().last_filled(),
                exec_step.
                    .stack()
                    .deref()
                    .last()
                    .cloned()
                    .ok_or(Error::InvalidStackPointer)?,
            ),
        );

        Ok(())
    }
}

#[cfg(test)]
mod pop_tests {
    use super::*;
    use crate::{
        bytecode,
        evm::{
            EvmWord, GasCost, GasInfo, OpcodeId, Stack, StackAddress, Storage,
        },
        external_tracer, BlockConstants, ExecutionTrace,
    };
    use pasta_curves::pallas::Scalar;

    #[test]
    fn pop_opcode_impl() -> Result<(), Error> {
        let code = bytecode! {
            #[start]
            POP
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

        let mut ctx = TraceContext::new();

        // Start from the same pc and gas limit
        let mut pc = obtained_steps[0].pc();
        let mut gas = obtained_steps[0].gas_info().gas;

        // The memory is the same in both steps as none of them edits the
        // memory of the EVM.
        let mem_map = obtained_steps[0].memory.clone();

        // Generate Step1 corresponding to POP
        let mut step_1 = ExecutionStep {
            memory: mem_map,
            stack: Stack(vec![EvmWord::from(0x80u8)]),,
            storage: Storage::empty(),
            instruction: OpcodeId::POP,
            gas_info: gas_info!(gas, FASTEST),
            depth: 1u8,
            pc: pc.inc_pre(),
            gc: ctx.gc,
            bus_mapping_instance: vec![],
        };

        // Add StackOp associated to the pop at the latest Stack pos.
        ctx.pop_op(
            &mut step_1,
            StackOp::new(
                RW::READ,
                StackAddress::from(1023),
                EvmWord::from(0x80u8),
            ),
        );

        // Compare first step bus mapping instance
        assert_eq!(
            obtained_exec_trace[0].bus_mapping_instance(),
            step_1.bus_mapping_instance()
        );
        // Compare first step entirely
        assert_eq!(obtained_exec_trace[0], step_1);

        // Compare containers
        assert_eq!(obtained_exec_trace.ctx.container, ctx.container);

        Ok(())
    }
}
