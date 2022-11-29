use crate::circuit_input_builder::{CircuitInputStateRef, ExecStep};
use crate::evm::Opcode;
use crate::operation::{TxAccessListAccountOp, RW};
use crate::Error;
use eth_types::{GethExecStep, ToAddress, ToWord};

#[derive(Debug, Copy, Clone)]
pub(crate) struct Balance;

impl Opcode for Balance {
    fn gen_associated_ops(
        state: &mut CircuitInputStateRef,
        geth_steps: &[GethExecStep],
    ) -> Result<Vec<ExecStep>, Error> {
        // TODO: finish this, only access list part is done
        let geth_step = &geth_steps[0];
        let mut exec_step = state.new_step(geth_step)?;

        let address = geth_steps[0].stack.last()?.to_address();
        state.stack_read(
            &mut exec_step,
            geth_step.stack.last_filled(),
            address.to_word(),
        )?;
        let is_warm = state.sdb.check_account_in_access_list(&address);
        state.push_op_reversible(
            &mut exec_step,
            RW::WRITE,
            TxAccessListAccountOp {
                tx_id: state.tx_ctx.id(),
                address,
                is_warm: true,
                is_warm_prev: is_warm,
            },
        )?;

        state.stack_write(
            &mut exec_step,
            geth_steps[1].stack.nth_last_filled(0),
            geth_steps[1].stack.nth_last(0)?,
        )?;

        Ok(vec![exec_step])
    }
}

#[cfg(test)]
mod balance_tests {
    use super::*;
    use crate::{
        circuit_input_builder::ExecState,
        mock::BlockData,
        operation::{StackOp, RW},
    };
    use eth_types::{
        bytecode,
        evm_types::{OpcodeId, StackAddress},
        geth_types::GethData,
    };
    use mock::eth;
    use mock::test_ctx::{helpers::*, TestContext};
    use pretty_assertions::assert_eq;

    // If the given account doesn't exist, it will push 0 onto the stack instead.
    #[test]
    fn test_balance_of_non_exists_address() {
        let code = bytecode! {
            BALANCE
            STOP
        };

        // Get the execution steps from the external tracer
        let block: GethData = TestContext::<2, 1>::new(
            None,
            account_0_code_account_1_no_code(code),
            tx_from_1_to_0,
            |block, _tx| block.number(0xcafeu64),
        )
        .unwrap()
        .into();

        let mut builder = BlockData::new_from_geth_data(block.clone()).new_circuit_input_builder();
        builder
            .handle_block(&block.eth_block, &block.geth_traces)
            .unwrap();

        let _step = builder.block.txs()[0]
            .steps()
            .iter()
            .find(|step| step.exec_state == ExecState::Op(OpcodeId::BALANCE))
            .unwrap();

        assert_eq!(&builder.block.container.stack.len(), &0_usize);
    }

    #[test]
    fn test_balance_of_exists_address() {
        let (addr_a, addr_b) = (mock::MOCK_ACCOUNTS[0], mock::MOCK_ACCOUNTS[1]);

        let code = bytecode! {
            PUSH32(addr_a.to_word())
            BALANCE
            STOP
        };

        // Get the execution steps from the external tracer
        let block: GethData = TestContext::<2, 1>::new(
            None,
            |accs| {
                accs[0].address(addr_a).balance(eth(10)).code(code);
                accs[1].address(addr_b).balance(eth(10));
            },
            |mut txs, accs| {
                txs[0].from(accs[1].address).to(accs[0].address);
            },
            |block, _tx| block,
        )
        .unwrap()
        .into();

        let mut builder = BlockData::new_from_geth_data(block.clone()).new_circuit_input_builder();
        builder
            .handle_block(&block.eth_block, &block.geth_traces)
            .unwrap();

        let step = builder.block.txs()[0]
            .steps()
            .iter()
            .find(|step| step.exec_state == ExecState::Op(OpcodeId::BALANCE))
            .unwrap();

        let call_id = builder.block.txs()[0].calls()[0].call_id;
        let balance_a = builder.sdb.get_account(&addr_a).1.balance;

        assert_eq!(addr_a, block.eth_block.transactions[0].to.unwrap());
        assert_eq!(
            {
                let operation =
                    &builder.block.container.stack[step.bus_mapping_instance[0].as_usize()];
                (operation.rw(), operation.op())
            },
            (
                RW::READ,
                &StackOp::new(call_id, StackAddress::from(1023), addr_a.to_word())
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
                &StackOp::new(call_id, StackAddress::from(1023), balance_a)
            )
        );
    }
}
