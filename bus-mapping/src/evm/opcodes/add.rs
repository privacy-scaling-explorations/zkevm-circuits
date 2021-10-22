use super::Opcode;
use crate::circuit_input_builder::CircuitInputStateRef;
use crate::eth_types::GethExecStep;
use crate::{
    operation::{StackOp, RW},
    Error,
};

#[derive(Debug, Copy, Clone)]
pub(crate) struct Add;

impl Opcode for Add {
    fn gen_associated_ops(
        state: &mut CircuitInputStateRef,
        steps: &[GethExecStep],
    ) -> Result<(), Error> {
        let step = &steps[0];
        //
        // First stack read
        //
        let stack_last_value_read = step.stack.last()?;
        let stack_last_position = step.stack.last_filled();

        // Manage first stack read at latest stack position
        state.push_op(StackOp::new(
            RW::READ,
            stack_last_position,
            stack_last_value_read,
        ));

        //
        // Second stack read
        //
        let stack_second_last_value_read = step.stack.nth_last(1)?;
        let stack_second_last_position = step.stack.nth_last_filled(1);

        // Manage second stack read at second latest stack position
        state.push_op(StackOp::new(
            RW::READ,
            stack_second_last_position,
            stack_second_last_value_read,
        ));

        //
        // First plus second stack value write
        //
        let added_value = steps[1].stack.last()?;

        // Manage second stack read at second latest stack position
        state.push_op(StackOp::new(
            RW::WRITE,
            stack_second_last_position,
            added_value,
        ));

        Ok(())
    }
}

#[cfg(test)]
mod add_tests {
    use super::*;
    use crate::{
        bytecode,
        circuit_input_builder::{
            CircuitInputBuilder, ExecStep, Transaction, TransactionContext,
        },
        eth_types::Word,
        evm::StackAddress,
        mock,
    };

    #[test]
    fn add_opcode_impl() -> Result<(), Error> {
        let code = bytecode! {
            PUSH1(0x80u64)
            PUSH1(0x80u64)
            #[start]
            ADD
            STOP
        };

        // Get the execution steps from the external tracer
        let block =
            mock::BlockData::new_single_tx_trace_code_at_start(&code).unwrap();

        let mut builder = CircuitInputBuilder::new(
            block.eth_block.clone(),
            block.block_ctants.clone(),
        );
        builder.handle_tx(&block.eth_tx, &block.geth_trace).unwrap();

        let mut test_builder = CircuitInputBuilder::new(
            block.eth_block,
            block.block_ctants.clone(),
        );
        let mut tx = Transaction::new(&block.eth_tx);
        let mut tx_ctx = TransactionContext::new(&block.eth_tx);

        // Generate step corresponding to ADD
        let mut step = ExecStep::new(
            &block.geth_trace.struct_logs[0],
            test_builder.block_ctx.gc,
        );
        let mut state_ref =
            test_builder.state_ref(&mut tx, &mut tx_ctx, &mut step);

        let last_stack_pointer = StackAddress(1022);
        let second_last_stack_pointer = StackAddress(1023);
        let stack_value_a = Word::from(0x80);
        let stack_value_b = Word::from(0x80);
        let sum = Word::from(0x100);

        // Manage first stack read at latest stack position
        state_ref.push_op(StackOp::new(
            RW::READ,
            last_stack_pointer,
            stack_value_a,
        ));

        // Manage second stack read at second latest stack position
        state_ref.push_op(StackOp::new(
            RW::READ,
            second_last_stack_pointer,
            stack_value_b,
        ));

        // Add StackOp associated to the 0x80 push at the latest Stack pos.
        state_ref.push_op(StackOp::new(
            RW::WRITE,
            second_last_stack_pointer,
            sum,
        ));

        tx.steps_mut().push(step);
        test_builder.block.txs_mut().push(tx);

        // Compare first step bus mapping instance
        assert_eq!(
            builder.block.txs()[0].steps()[0].bus_mapping_instance,
            test_builder.block.txs()[0].steps()[0].bus_mapping_instance,
        );

        // Compare containers
        assert_eq!(builder.block.container, test_builder.block.container);

        Ok(())
    }
}
