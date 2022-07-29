#[cfg(test)]
mod test {
    use eth_types::geth_types::GethData;
    use eth_types::{address, bytecode, Word};
    use mock::TestContext;
    use zkevm_circuits::evm_circuit::test::run_test_circuit_incomplete_fixed_table;
    use zkevm_circuits::evm_circuit::witness::block_convert;

    #[test]
    fn testme(){
        let addr0 = address!("0x00000000000000000000000000000000000cafe0");
        let addr1 = address!("0x00000000000000000000000000000000000cafe1");
        let addr2 = address!("0x00000000000000000000000000000000000cafe2");

        let code1 = bytecode! {
            PUSH32(0)
            PUSH32(0)
            PUSH32(0)
            PUSH32(0)
            PUSH32(0)
            PUSH32(Word::from("0x00000000000000000000000000000000000cafe2"))
            PUSH32(100000)
            CALL
            STOP
        };
        let code2 = bytecode! {
            STOP
        };

        let block: GethData = TestContext::<3, 1>::new(
            None,
            |accs| {
                accs[0].address(addr0).balance(Word::one() << 18);
                accs[1].address(addr1).code(code1);
                accs[2].address(addr2).code(code2);
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
        run_test_circuit_incomplete_fixed_table(block).expect("should work")
    }
}
