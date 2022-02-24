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
        let callee_address = state.call().address;

        // CallContext read of the callee_address
        state.push_op(
            RW::READ,
            CallContextOp {
                call_id: state.call().call_id,
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
        );

        Ok(())
    }
}

#[cfg(test)]
mod selfbalance_tests {
    use super::*;
    use crate::circuit_input_builder::{ExecStep, TransactionContext};
    use eth_types::{bytecode, evm_types::StackAddress, ToWord};
    use pretty_assertions::assert_eq;

    #[test]
    fn selfbalance_opcode_impl() -> Result<(), Error> {
        let code = bytecode! {
            #[start]
            SELFBALANCE
            STOP
        };

        let mut geth_data = mock::new_single_tx_trace_code(&code)?;
        geth_data.geth_trace.struct_logs =
            geth_data.geth_trace.struct_logs[code.get_pos("start")..].to_vec();

        // Get the execution steps from the external tracer
        let block = crate::mock::BlockData::new_from_geth_data(geth_data);

        let mut builder = block.new_circuit_input_builder();
        builder.handle_tx(&block.eth_tx, &block.geth_trace).unwrap();

        let mut test_builder = block.new_circuit_input_builder();
        let mut tx = test_builder
            .new_tx(&block.eth_tx, !block.geth_trace.failed)
            .unwrap();
        let mut tx_ctx = TransactionContext::new(&block.eth_tx, &block.geth_trace).unwrap();

        // Generate step corresponding to SELFBALANCE
        let mut step = ExecStep::new(
            &block.geth_trace.struct_logs[0],
            0,
            test_builder.block_ctx.rwc,
            0,
        );
        let mut state_ref = test_builder.state_ref(&mut tx, &mut tx_ctx, &mut step);

        let callee_address = block.eth_tx.to.unwrap();
        let self_balance = state_ref.sdb.get_account(&callee_address).1.balance;

        // CallContext read for callee_address
        state_ref.push_op(
            RW::READ,
            CallContextOp {
                call_id: state_ref.call().call_id,
                field: CallContextField::CalleeAddress,
                value: callee_address.to_word(),
            },
        );

        // Account read for balance of callee_address
        state_ref.push_op(
            RW::READ,
            AccountOp {
                address: callee_address,
                field: AccountField::Balance,
                value: self_balance,
                value_prev: self_balance,
            },
        );

        // Add the Stack write
        state_ref.push_stack_op(RW::WRITE, StackAddress::from(1024 - 1), self_balance);

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
