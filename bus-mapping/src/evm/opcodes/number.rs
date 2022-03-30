#[cfg(test)]
mod number_tests {
    use crate::{
        circuit_input_builder::{ExecStep, TransactionContext},
        mock::BlockData,
        operation::RW,
        Error,
    };
    use eth_types::{bytecode, evm_types::StackAddress, geth_types::GethData};
    use mock::test_ctx::{helpers::*, TestContext};
    use pretty_assertions::assert_eq;

    #[test]
    fn number_opcode_impl() -> Result<(), Error> {
        let code = bytecode! {
            #[start]
            NUMBER
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

        let mut tx = builder.block.txs()[0].clone();

        let mut tx_ctx = TransactionContext::new(
            &block.eth_block.transactions[0],
            &block.geth_traces[0],
            true,
        )
        .unwrap();

        // Generate step corresponding to NUMBER
        let mut step = ExecStep::new(
            &block.geth_traces[0].struct_logs[0],
            0,
            builder.block_ctx.rwc,
            0,
        );
        let mut state_ref = builder.state_ref(&mut tx, &mut tx_ctx);

        // Add the last Stack write
        let number = block.eth_block.number.unwrap().as_u64();
        state_ref
            .push_stack_op(
                &mut step,
                RW::WRITE,
                StackAddress::from(1024 - 1),
                eth_types::U256::from(number),
            )
            .unwrap();

        tx.steps_mut().push(step);
        builder.block.txs_mut().push(tx);

        // Compare first step bus mapping instance
        assert_eq!(
            builder.block.txs()[0].steps()[0].bus_mapping_instance,
            builder.block.txs()[0].steps()[0].bus_mapping_instance,
        );

        // Compare containers
        assert_eq!(builder.block.container, builder.block.container);

        Ok(())
    }
}
