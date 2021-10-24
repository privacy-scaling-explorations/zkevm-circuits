use super::Opcode;
use crate::{
    exec_trace::{ExecutionStep, TraceContext},
    operation::{EthAddress, StackOp, StorageOp, RW},
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
        ctx: &mut TraceContext,
        exec_step: &mut ExecutionStep,
        next_steps: &[ExecutionStep],
    ) -> Result<(), Error> {
        let gc_start = ctx.gc;

        // First stack read
        let stack_value_read = exec_step
            .stack()
            .last()
            .cloned()
            .ok_or(Error::InvalidStackPointer)?;
        let stack_position = exec_step.stack().last_filled();

        // Manage first stack read at latest stack position
        ctx.push_op(
            exec_step,
            StackOp::new(RW::READ, stack_position, stack_value_read),
        );

        // Storage read
        let storage_value_read =
            *exec_step.storage().get_or_err(&stack_value_read)?;
        ctx.push_op(
            exec_step,
            StorageOp::new(
                RW::READ,
                EthAddress([0u8; 20]), // TODO: Fill with the correct value
                stack_value_read,
                storage_value_read,
                storage_value_read,
            ),
        );

        // First stack write
        ctx.push_op(
            exec_step,
            StackOp::new(RW::WRITE, stack_position, storage_value_read),
        );

        Ok(())
    }
}

#[cfg(test)]
mod sload_tests {
    use super::*;
    use crate::{
        bytecode,
        evm::{
            EvmWord, GasCost, GasInfo, Memory, OpcodeId, Stack, StackAddress,
            Storage,
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

        let mut ctx = TraceContext::new();

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
            pc: pc.inc_pre(),
            gc: ctx.gc,
            bus_mapping_instance: vec![],
        };

        // Add StackOp associated to the stack pop.
        ctx.push_op(
            &mut step_1,
            StackOp::new(
                RW::READ,
                StackAddress::from(1023),
                EvmWord::from(0x0u32),
            ),
        );
        // Add StorageOp associated to the storage read.
        ctx.push_op(
            &mut step_1,
            StorageOp::new(
                RW::READ,
                EthAddress([0u8; 20]), // TODO: Fill with the correct value
                EvmWord::from(0x0u32),
                EvmWord::from(0x6fu32),
                EvmWord::from(0x6fu32),
            ),
        );
        // Add StackOp associated to the stack push.
        ctx.push_op(
            &mut step_1,
            StackOp::new(
                RW::WRITE,
                StackAddress::from(1023),
                EvmWord::from(0x6fu32),
            ),
        );

        assert_eq!(
            obtained_exec_trace[0].bus_mapping_instance(),
            step_1.bus_mapping_instance()
        );
        assert_eq!(obtained_exec_trace[0], step_1);
        assert_eq!(obtained_exec_trace.ctx.container, ctx.container);

        Ok(())
    }
}
