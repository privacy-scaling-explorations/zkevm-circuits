use super::Opcode;
use crate::circuit_input_builder::CircuitInputStateRef;
use crate::operation::{AccountField, AccountOp, CallContextField, CallContextOp, RW};
use crate::Error;
use eth_types::{GethExecStep, ToWord};

#[derive(Debug, Copy, Clone)]
pub(crate) struct Selfbalance;

impl Opcode for Selfbalance {
    fn gen_associated_ops(
        state: &mut CircuitInputStateRef,
        steps: &[GethExecStep],
    ) -> Result<(), Error> {
        let step = &steps[0];
        let self_balance = steps[1].stack.last()?;
        let callee_address = state.call()?.address;

        // CallContext read of the callee_address
        state.push_op(
            RW::READ,
            CallContextOp {
                call_id: state.call()?.call_id,
                field: CallContextField::CalleeAddress,
                value: callee_address.to_word(),
            },
        );

        // Account read for the balance of the callee_address
        state.push_op(
            RW::READ,
            AccountOp {
                address: callee_address,
                field: AccountField::Balance,
                value: self_balance,
                value_prev: self_balance,
            },
        );

        // Stack write of self_balance
        state.push_stack_op(
            RW::WRITE,
            step.stack.last_filled().map(|a| a - 1),
            self_balance,
        )?;

        Ok(())
    }
}

#[cfg(test)]
mod selfbalance_tests {
    use super::*;
    use crate::operation::{CallContextField, CallContextOp, StackOp, RW};
    use eth_types::{bytecode, evm_types::OpcodeId, evm_types::StackAddress};
    use pretty_assertions::assert_eq;

    #[test]
    fn selfbalance_opcode_impl() {
        let code = bytecode! {
            SELFBALANCE
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
            .find(|step| step.op == OpcodeId::SELFBALANCE)
            .unwrap();

        let call_id = builder.block.txs()[0].calls()[0].call_id;
        let callee_address = builder.block.txs()[0].to;
        let self_balance = builder.sdb.get_account(&callee_address).1.balance;

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
                    field: CallContextField::CalleeAddress,
                    value: callee_address.to_word(),
                }
            )
        );
        assert_eq!(
            {
                let operation =
                    &builder.block.container.account[step.bus_mapping_instance[1].as_usize()];
                (operation.rw(), operation.op())
            },
            (
                RW::READ,
                &AccountOp {
                    address: callee_address,
                    field: AccountField::Balance,
                    value: self_balance,
                    value_prev: self_balance,
                }
            )
        );
        assert_eq!(
            {
                let operation =
                    &builder.block.container.stack[step.bus_mapping_instance[2].as_usize()];
                (operation.rw(), operation.op())
            },
            (
                RW::WRITE,
                &StackOp::new(1, StackAddress::from(1023), self_balance)
            )
        );
    }
}
