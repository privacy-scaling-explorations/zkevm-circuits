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
            .adc(stack_second_last_value_read)
            .unwrap();

        // Manage second stack read at second latest stack position
        ctx.push_op(
            exec_step,
            StackOp::new(RW::WRITE, stack_second_last_position, sum),
        );

        exec_step.mut_stack().add();

        Ok(())
    }
}

#[cfg(test)]
mod add_tests {
    use super::*;
    use crate::{
        bytecode,
        evm::{
            EvmWord, GasCost, Memory,
            OpcodeId::{ADD, PUSH1},
            Stack, StackAddress, Storage,
        },
        external_tracer,
        operation::RW::{READ, WRITE},
        BlockConstants, ExecutionTrace,
    };
    use pasta_curves::pallas::Scalar;

    macro_rules! push_opcode_to_ctx {
        ($ctx:ident, $step:ident, $rw:path, $address:expr, $word:expr) => {
            $ctx.push_op(&mut $step, StackOp::new($rw, $address, $word))
        };
    }

    macro_rules! step_setup {
        ($stack:expr, $instruction:path, $obtained_steps:expr, $gc:expr) => {
            ExecutionStep {
                memory: Memory::empty(),
                stack: $stack,
                storage: Storage::empty(),
                instruction: $instruction,
                gas: $obtained_steps.gas(),
                gas_cost: GasCost::FASTEST,
                depth: 1u8,
                pc: $obtained_steps.pc(),
                gc: $gc,
                bus_mapping_instance: vec![],
            }
        };
    }

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
        let last_stack_pointer = StackAddress::from(1022);
        let second_last_stack_pointer = StackAddress::from(1023);
        let stack_value_a = EvmWord::from(0x80u8);
        let stack_value_b = EvmWord::from(0x80u8);
        let sum = stack_value_a.adc(stack_value_b).unwrap();

        // Generate Step1 corresponding to PUSH1 80
        let mut step_1 =
            step_setup!(Stack::empty(), PUSH1, obtained_steps[0], ctx.gc);

        // Add StackOp associated to the 0x80 push at the latest Stack pos.
        push_opcode_to_ctx!(
            ctx,
            step_1,
            WRITE,
            second_last_stack_pointer,
            stack_value_a
        );

        // Generate Step2 corresponding to PUSH1 80
        let mut step_2 = step_setup!(
            Stack(vec![stack_value_a]),
            PUSH1,
            obtained_steps[1],
            ctx.gc
        );

        // Add StackOp associated to the 0x80 push at the second latest Stack pos.
        push_opcode_to_ctx!(
            ctx,
            step_2,
            WRITE,
            last_stack_pointer,
            stack_value_b
        );

        // Generate Step3 corresponding to ADD
        let mut step_3 =
            step_setup!(Stack(vec![sum]), ADD, obtained_steps[2], ctx.gc);

        // Manage first stack read at latest stack position
        push_opcode_to_ctx!(
            ctx,
            step_3,
            READ,
            last_stack_pointer,
            stack_value_a
        );

        // Manage second stack read at second latest stack position
        push_opcode_to_ctx!(
            ctx,
            step_3,
            READ,
            second_last_stack_pointer,
            stack_value_b
        );

        // Add StackOp associated to the 0x80 push at the latest Stack pos.
        push_opcode_to_ctx!(ctx, step_3, WRITE, second_last_stack_pointer, sum);

        // Compare each step bus mapping instance
        assert_eq!(
            obtained_exec_trace[0].bus_mapping_instance(),
            step_1.bus_mapping_instance()
        );
        assert_eq!(
            obtained_exec_trace[1].bus_mapping_instance(),
            step_2.bus_mapping_instance()
        );
        assert_eq!(
            obtained_exec_trace[2].bus_mapping_instance(),
            step_3.bus_mapping_instance()
        );

        // Compare each step entirely
        assert_eq!(obtained_exec_trace[0], step_1);
        assert_eq!(obtained_exec_trace[1], step_2);
        assert_eq!(obtained_exec_trace[2], step_3);

        // Compare containers
        assert_eq!(obtained_exec_trace.ctx.container, ctx.container);

        Ok(())
    }
}
