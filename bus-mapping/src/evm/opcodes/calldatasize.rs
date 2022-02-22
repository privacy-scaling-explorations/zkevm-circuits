use crate::{
    circuit_input_builder::CircuitInputStateRef,
    operation::{CallContextField, CallContextOp, RW},
    Error,
};

use eth_types::GethExecStep;

use super::Opcode;

#[derive(Clone, Copy, Debug)]
pub(crate) struct Calldatasize;

impl Opcode for Calldatasize {
    fn gen_associated_ops(
        state: &mut CircuitInputStateRef,
        steps: &[GethExecStep],
    ) -> Result<(), Error> {
        let step = &steps[0];
        let value = steps[1].stack.last()?;
        state.push_op(
            RW::READ,
            CallContextOp {
                call_id: state.call().call_id,
                field: CallContextField::CallDataLength,
                value,
            },
        );
        state.push_stack_op(RW::WRITE, step.stack.last_filled().map(|a| a - 1), value);
        Ok(())
    }
}

#[cfg(test)]
mod calldatasize_tests {
    use crate::{
        circuit_input_builder::{ExecStep, TransactionContext},
        mock::BlockData,
        operation::{CallContextField, CallContextOp, RW},
        Error,
    };
    use eth_types::bytecode;
    use eth_types::evm_types::StackAddress;
    use mock::new_single_tx_trace_code_at_start;
    use pretty_assertions::assert_eq;

    #[test]
    fn calldatasize_opcode_impl() -> Result<(), Error> {
        let code = bytecode! {
            #[start]
            CALLDATASIZE
            STOP
        };

        // Get the execution steps from the external tracer
        let block =
            BlockData::new_from_geth_data(new_single_tx_trace_code_at_start(&code).unwrap());

        let mut builder = block.new_circuit_input_builder();
        builder.handle_tx(&block.eth_tx, &block.geth_trace).unwrap();

        let mut test_builder = block.new_circuit_input_builder();
        let mut tx = test_builder
            .new_tx(&block.eth_tx, !block.geth_trace.failed)
            .unwrap();
        let mut tx_ctx = TransactionContext::new(&block.eth_tx, &block.geth_trace).unwrap();

        // Generate step corresponding to CALLDATASIZE
        let mut step = ExecStep::new(
            &block.geth_trace.struct_logs[0],
            0,
            test_builder.block_ctx.rwc,
            0,
        );
        let mut state_ref = test_builder.state_ref(&mut tx, &mut tx_ctx, &mut step);

        // Get calldatasize from eth tx.
        let call_data_size = block.eth_tx.input.to_vec().len();

        // Add the read operation.
        state_ref.push_op(
            RW::READ,
            CallContextOp {
                call_id: state_ref.call().call_id,
                field: CallContextField::CallDataLength,
                value: eth_types::U256::from(call_data_size),
            },
        );

        // Add the stack write.
        state_ref.push_stack_op(
            RW::WRITE,
            StackAddress::from(1024 - 1),
            eth_types::U256::from(call_data_size),
        );

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
