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
                call_id: state.call()?.call_id,
                field: CallContextField::CallDataLength,
                value,
            },
        );
        state.push_stack_op(RW::WRITE, step.stack.last_filled().map(|a| a - 1), value)?;
        Ok(())
    }
}

#[cfg(test)]
mod calldatasize_tests {
    use crate::operation::{CallContextField, CallContextOp, StackOp, RW};
    use eth_types::{bytecode, evm_types::OpcodeId, evm_types::StackAddress};
    use pretty_assertions::assert_eq;

    #[test]
    fn calldatasize_opcode_impl() {
        let code = bytecode! {
            CALLDATASIZE
            STOP
        };

        // Get the execution steps from the external tracer
        let block = crate::mock::BlockData::new_from_geth_data(
            mock::new_single_tx_trace_code(&code).unwrap(),
        );

        let mut builder = block.new_circuit_input_builder();
        builder
            .handle_block(&block.eth_block, &block.geth_traces)
            .unwrap();

        let step = builder.block.txs()[0]
            .steps()
            .iter()
            .find(|step| step.op == OpcodeId::CALLDATASIZE)
            .unwrap();

        let call_id = builder.block.txs()[0].calls()[0].call_id;
        let call_data_size = block.eth_block.transactions[0].input.as_ref().len().into();
        assert_eq!(
            {
                let operation =
                    &builder.block.container.call_context[step.bus_mapping_instance[0].as_usize()];
                (operation.rw(), operation.op())
            },
            (
                RW::READ,
                &CallContextOp {
                    call_id,
                    field: CallContextField::CallDataLength,
                    value: call_data_size,
                }
            )
        );
        assert_eq!(
            {
                let operation =
                    &builder.block.container.stack[step.bus_mapping_instance[1].as_usize()];
                (operation.rw(), operation.op())
            },
            (
                RW::WRITE,
                &StackOp::new(1, StackAddress::from(1023), call_data_size)
            )
        );
    }
}
