use crate::circuit_input_builder::CircuitInputStateRef;
use crate::eth_types::GethExecStep;
// Port this to a macro if possible to avoid defining all the PushN
use super::Opcode;
use crate::{
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
        state: &mut CircuitInputStateRef,
        steps: &[GethExecStep],
    ) -> Result<(), Error> {
        state.push_op(StackOp::new(
            RW::WRITE,
            // Get the value and addr from the next step. Being the last position filled with an element in the stack
            steps[1].stack.last_filled(),
            steps[1].stack.last()?,
        ));

        Ok(())
    }
}

#[cfg(test)]
mod push_tests {
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
    fn push1_opcode_impl() -> Result<(), Error> {
        let code = bytecode! {
            #[start]
            PUSH1(0x80u64)
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

        // Generate step corresponding to PUSH1 80
        let mut step = ExecStep::new(
            &block.geth_trace.struct_logs[0],
            test_builder.block_ctx.gc,
        );
        let mut state_ref =
            test_builder.state_ref(&mut tx, &mut tx_ctx, &mut step);

        // Add StackOp associated to the 0x80 push at the latest Stack pos.
        state_ref.push_op(StackOp::new(
            RW::WRITE,
            StackAddress::from(1023),
            Word::from(0x80),
        ));
        tx.steps_mut().push(step);
        test_builder.block.txs_mut().push(tx);

        // Compare first step bus mapping instance
        assert_eq!(
            builder.block.txs()[0].steps()[0].bus_mapping_instance,
            test_builder.block.txs()[0].steps()[0].bus_mapping_instance
        );
        // Compare containers
        assert_eq!(builder.block.container, test_builder.block.container);

        Ok(())
    }
}
