use super::Opcode;
use crate::circuit_input_builder::CircuitInputStateRef;
use crate::operation::{CallContextField, CallContextOp, RW};
use crate::Error;
use eth_types::GethExecStep;

#[derive(Debug, Copy, Clone)]
pub(crate) struct Origin;

impl Opcode for Origin {
    fn gen_associated_ops(
        state: &mut CircuitInputStateRef,
        steps: &[GethExecStep],
    ) -> Result<(), Error> {
        let step = &steps[0];
        // Get origin address result from next step
        let value = steps[1].stack.last()?;
        // CallContext read of the tx_id
        state.push_op(
            RW::READ,
            CallContextOp {
                call_id: state.call().call_id,
                field: CallContextField::TxId,
                value: state.tx_ctx.id().try_into().unwrap(),
            },
        );
        // Stack write of the origin address
        state.push_stack_op(RW::WRITE, step.stack.last_filled().map(|a| a - 1), value);

        Ok(())
    }
}

#[cfg(test)]
mod origin_tests {
    use super::*;
    use crate::circuit_input_builder::{ExecStep, TransactionContext};
    use eth_types::{bytecode, evm_types::StackAddress, ToWord};
    use pretty_assertions::assert_eq;

    #[test]
    fn origin_opcode_impl() -> Result<(), Error> {
        let code = bytecode! {
            #[start]
            ORIGIN
            STOP
        };

        // Get the execution steps from the external tracer
        let block = crate::mock::BlockData::new_from_geth_data(
            mock::new_single_tx_trace_code_at_start(&code).unwrap(),
        );

        let mut builder = block.new_circuit_input_builder();
        builder.handle_tx(&block.eth_tx, &block.geth_trace).unwrap();

        let mut test_builder = block.new_circuit_input_builder();
        let mut tx = test_builder
            .new_tx(&block.eth_tx, !block.geth_trace.failed)
            .unwrap();
        let mut tx_ctx = TransactionContext::new(&block.eth_tx, &block.geth_trace).unwrap();

        // Generate step corresponding to ORIGIN
        let mut step = ExecStep::new(
            &block.geth_trace.struct_logs[0],
            0,
            test_builder.block_ctx.rwc,
            0,
        );
        let mut state_ref = test_builder.state_ref(&mut tx, &mut tx_ctx, &mut step);

        let origin = block.eth_tx.from.to_word();
        let tx_id = block.eth_tx.hash.to_word();

        // Add the CallContext read
        state_ref.push_op(
            RW::READ,
            CallContextOp {
                call_id: state_ref.call().call_id,
                field: CallContextField::TxId,
                value: tx_id,
            },
        );
        // Add the Stack write
        state_ref.push_stack_op(RW::WRITE, StackAddress::from(1024 - 1), origin);

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
