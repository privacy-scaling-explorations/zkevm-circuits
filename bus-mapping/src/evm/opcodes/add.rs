use super::Opcode;
use crate::{
    exec_trace::{ExecutionStep, TraceContext},
    operation::{StackOp, RW},
    Error,
};

#[derive(Debug, Copy, Clone)]
pub(crate) struct Add;

impl Opcode for Add {
    fn gen_associated_ops(
        &self,
        ctx: &mut TraceContext,
        exec_step: &mut ExecutionStep,
        _next_steps: &[ExecutionStep],
    ) -> Result<(), Error> {
        //
        // First stack read
        //
        let stack_last_value_read = exec_step
            .stack()
            .last()
            .cloned()
            .ok_or(Error::InvalidStackPointer)?;
        let stack_last_position = exec_step.stack().last_filled();

        // Manage first stack read at latest stack position
        ctx.push_op(
            exec_step,
            StackOp::new(RW::READ, stack_last_position, stack_last_value_read),
        );

        //
        // Second stack read
        //
        let stack_second_last_value_read = exec_step
            .stack()
            .second_last()
            .cloned()
            .ok_or(Error::InvalidStackPointer)?;
        let stack_second_last_position = exec_step.stack().second_last_filled();

        // Manage second stack read at second latest stack position
        ctx.push_op(
            exec_step,
            StackOp::new(
                RW::READ,
                stack_second_last_position,
                stack_second_last_value_read,
            ),
        );

        //
        // First plus second stack value write
        //

        let sum = stack_last_value_read
            .add(stack_second_last_value_read)
            .unwrap();

        exec_step.mut_stack().add();

        // Manage second stack read at second latest stack position
        ctx.push_op(
            exec_step,
            StackOp::new(RW::WRITE, stack_second_last_position, sum),
        );

        Ok(())
    }
}

#[cfg(test)]
mod add_tests {
    use super::*;
    use crate::{
        bytecode,
        evm::{EvmWord, GasCost, OpcodeId, Stack, StackAddress, Storage},
        external_tracer, BlockConstants, ExecutionTrace,
    };
    use pasta_curves::pallas::Scalar;

    #[test]
    fn add_opcode_impl() -> Result<(), Error> {
        let code = bytecode! {
            #[start]
            PUSH1(0x80u64)
            PUSH1(0x80u64)
            ADD
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

        // The memory is the same in both steps as none of them edits the
        // memory of the EVM.
        let mem_map = obtained_steps[0].memory.clone();

        // Generate Step1 corresponding to PUSH1 80
        let mut step_1 = ExecutionStep {
            memory: mem_map.clone(),
            stack: Stack::empty(),
            storage: Storage::empty(),
            instruction: OpcodeId::PUSH1,
            gas: obtained_steps[0].gas(),
            gas_cost: GasCost::FASTEST,
            depth: 1u8,
            pc: obtained_steps[0].pc(),
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

        // Generate Step2 corresponding to PUSH1 80
        let mut step_2 = ExecutionStep {
            memory: mem_map.clone(),
            stack: Stack(vec![EvmWord::from(0x80u8)]),
            storage: Storage::empty(),
            instruction: OpcodeId::PUSH1,
            gas: obtained_steps[1].gas(),
            gas_cost: GasCost::FASTEST,
            depth: 1u8,
            pc: obtained_steps[1].pc(),
            gc: ctx.gc,
            bus_mapping_instance: vec![],
        };

        // Add StackOp associated to the 0x80 push at the latest Stack pos.
        ctx.push_op(
            &mut step_2,
            StackOp::new(
                RW::WRITE,
                StackAddress::from(1022),
                EvmWord::from(0x80u8),
            ),
        );

        // Generate Step3 corresponding to ADD
        let mut step_3 = ExecutionStep {
            memory: mem_map.clone(),
            stack: Stack(vec![EvmWord([
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
            ])]),
            storage: Storage::empty(),
            instruction: OpcodeId::ADD,
            gas: obtained_steps[2].gas(),
            gas_cost: GasCost::FASTEST,
            depth: 1u8,
            pc: obtained_steps[2].pc(),
            gc: ctx.gc,
            bus_mapping_instance: vec![],
        };

        // Add StackOp associated to the 0x80 push at the latest Stack pos.
        ctx.push_op(
            &mut step_3,
            StackOp::new(
                RW::WRITE,
                StackAddress::from(1023),
                EvmWord([
                    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
                ]),
            ),
        );

        // Compare first step bus mapping instance
        assert_eq!(
            obtained_exec_trace[0].bus_mapping_instance(),
            step_1.bus_mapping_instance()
        );
        // println!("{:?}", obtained_exec_trace);
        // Compare first step entirely
        assert_eq!(obtained_exec_trace[0], step_1);
        assert_eq!(obtained_exec_trace[1], step_2);
        assert_eq!(obtained_exec_trace[2], step_3);

        // Compare containers
        // assert_eq!(obtained_exec_trace.ctx.container, ctx.container);

        Ok(())
    }
}
