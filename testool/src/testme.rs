#[cfg(test)]
mod test {
    /*
        use eth_types::bytecode::BytecodeElement;
        use eth_types::geth_types::GethData;
        use eth_types::{address, bytecode, Bytecode, Bytes, Word};
        use mock::TestContext;
        use std::collections::HashMap;
        use zkevm_circuits::evm_circuit::witness::block_convert;
        use zkevm_circuits::test_util::BytecodeTestConfig;

        #[test]
        fn testme() {

            let addr0 = address!("0x00000000000000000000000000000000000cafe0");
            let addr1 = address!("0x00000000000000000000000000000000000cafe1");

            let code1 = Bytecode {
                code: vec![BytecodeElement {
                    value: 0x6f,
                    is_code: true,
                }],
                num_opcodes: 1,
                markers: HashMap::new(),
            };
            let code2 = bytecode! {
                STOP
            };

            let block: GethData = TestContext::<3, 1>::new(
                None,
                |accs| {
                    accs[0].address(addr0).balance(Word::one() << 18);
                    accs[1].address(addr1).code(code1);
                },
                |mut txs, accs| {
                    txs[0]
                        .from(accs[0].address)
                        .to(accs[1].address)
                        .gas(Word::from(200000u64));
                },
                |block, _tx| block.number(0xcafeu64),
            )
            .unwrap()
            .into();
            let block_data = bus_mapping::mock::BlockData::new_from_geth_data(block);
            let mut builder = block_data.new_circuit_input_builder();
            builder
                .handle_block(&block_data.eth_block, &block_data.geth_traces)
                .unwrap();
            let block = block_convert(&builder.block, &builder.code_db);
            let bytecode_test_config = BytecodeTestConfig::default();
            zkevm_circuits::test_util::test_circuits_using_witness_block(block, bytecode_test_config)
                .expect("should work")

        }
    */
}
