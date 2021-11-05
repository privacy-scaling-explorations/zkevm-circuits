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
        next_steps: &[ExecutionStep],
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
            .nth_last(1)
            .cloned()
            .ok_or(Error::InvalidStackPointer)?;
        let stack_second_last_position = exec_step.stack().nth_last_filled(1);

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
        let added_value = next_steps[0]
            .stack()
            .last()
            .cloned()
            .ok_or(Error::InvalidStackPointer)?;

        // Manage second stack read at second latest stack position
        ctx.push_op(
            exec_step,
            StackOp::new(RW::WRITE, stack_second_last_position, added_value),
        );

        Ok(())
    }
}

#[cfg(test)]
mod add_tests {
    use super::*;
    use crate::{
        bytecode,
        evm::{
            EvmWord, GasCost, GlobalCounter, Memory, OpcodeId, OpcodeId::ADD,
            Stack, StackAddress, Storage,
        },
        external_tracer,
        operation::RW::{READ, WRITE},
        BlockConstants, ExecutionTrace,
    };
    use pasta_curves::pallas::Scalar;

    fn step_setup(
        stack: Stack,
        instruction: OpcodeId,
        obtained_steps: ExecutionStep,
        gc: GlobalCounter,
    ) -> ExecutionStep {
        ExecutionStep {
            memory: Memory::empty(),
            stack,
            storage: Storage::empty(),
            instruction,
            gas: obtained_steps.gas(),
            gas_cost: GasCost::FASTEST,
            depth: 1u8,
            pc: obtained_steps.pc(),
            gc,
            bus_mapping_instance: vec![],
        }
    }

    #[test]
    fn add_opcode_impl() -> Result<(), Error> {
        let code = bytecode! {
            PUSH1(0x80u64)
            PUSH1(0x80u64)
            #[start]
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
        let last_stack_pointer = StackAddress::from(1022);
        let second_last_stack_pointer = StackAddress::from(1023);
        let stack_value_a = EvmWord::from(0x80u8);
        let stack_value_b = EvmWord::from(0x80u8);
        let sum = EvmWord([
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
        ]);

        // Generate Step1 corresponding to ADD
        let mut step_1 = step_setup(
            Stack(vec![stack_value_a, stack_value_b]),
            ADD,
            obtained_steps[0].clone(),
            ctx.gc,
        );

        // Manage first stack read at latest stack position
        ctx.push_op(
            &mut step_1,
            StackOp::new(READ, last_stack_pointer, stack_value_a),
        );

        // Manage second stack read at second latest stack position
        ctx.push_op(
            &mut step_1,
            StackOp::new(READ, second_last_stack_pointer, stack_value_b),
        );

        // Add StackOp associated to the 0x80 push at the latest Stack pos.
        ctx.push_op(
            &mut step_1,
            StackOp::new(WRITE, second_last_stack_pointer, sum),
        );

        // Compare each step bus mapping instance
        assert_eq!(
            obtained_exec_trace[0].bus_mapping_instance(),
            step_1.bus_mapping_instance()
        );

        // Compare each step entirely
        assert_eq!(obtained_exec_trace[0], step_1);

        // Compare containers
        assert_eq!(obtained_exec_trace.ctx.container, ctx.container);

        Ok(())
    }
}
