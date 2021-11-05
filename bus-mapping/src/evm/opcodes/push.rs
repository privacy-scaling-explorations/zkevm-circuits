use core::ops::Deref;
// Port this to a macro if possible to avoid defining all the PushN
use super::Opcode;
use crate::{
    exec_trace::{ExecutionStep, TraceContext},
    operation::{StackOp, RW},
    Error,
};

/// Placeholder structure used to implement [`Opcode`] trait over it corresponding to the
/// [`OpcodeId::PUSH1`](crate::evm::OpcodeId::PUSH1) `OpcodeId`.
/// This is responsible of generating all of the associated [`StackOp`]s and place them
/// inside the trace's [`OperationContainer`](crate::operation::OperationContainer).
#[derive(Debug, Copy, Clone)]
pub(crate) struct Push1;

impl Opcode for Push1 {
    fn gen_associated_ops(
        &self,
        ctx: &mut TraceContext,
        // Contains the PUSH1 instr
        exec_step: &mut ExecutionStep,
        // Contains the next step where we can find the value that was pushed.
        next_steps: &[ExecutionStep],
    ) -> Result<(), Error> {
        ctx.push_op(
            exec_step,
            StackOp::new(
                RW::WRITE,
                // Get the value and addr from the next step. Being the last position filled with an element in the stack
                next_steps[0].stack().last_filled(),
                next_steps[0]
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
mod push_tests {
    use super::*;
    use crate::{
        bytecode,
        evm::{EvmWord, GasCost, OpcodeId, Stack, StackAddress, Storage},
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

        let mut ctx = TraceContext::new();

        // Start from the same pc and gas limit
        let mut pc = obtained_steps[0].pc();
        let gas = obtained_steps[0].gas();

        // The memory is the same in both steps as none of them edits the
        // memory of the EVM.
        let mem_map = obtained_steps[0].memory.clone();

        // Generate Step1 corresponding to PUSH1 80
        let mut step_1 = ExecutionStep {
            memory: mem_map,
            stack: Stack::new(),
            storage: Storage::empty(),
            instruction: OpcodeId::PUSH1,
            gas,
            gas_cost: GasCost::FASTEST,
            depth: 1u8,
            pc: pc.inc_pre(),
            gc: ctx.gc,
            bus_mapping_instance: vec![],
        };

        // Add StackOp associated to the 0x80 push at the latest Stack pos.
        ctx.push_op(
            &mut step_1,
            StackOp::new(
                RW::WRITE,
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
