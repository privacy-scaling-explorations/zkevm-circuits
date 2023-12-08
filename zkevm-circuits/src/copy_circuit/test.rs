use crate::{
    copy_circuit::*,
    evm_circuit::{test::rand_bytes, witness::block_convert},
    util::unusable_rows,
    witness::{chunk_convert, Block},
};
use bus_mapping::{
    circuit_input_builder::{CircuitInputBuilder, FixedCParams},
    mock::BlockData,
};
use eth_types::{bytecode, geth_types::GethData, ToWord, Word};
use halo2_proofs::{
    dev::{MockProver, VerifyFailure},
    halo2curves::bn256::Fr,
};
use mock::{
    test_ctx::helpers::account_0_code_account_1_no_code, Sha3CodeGen, TestContext, MOCK_ACCOUNTS,
};

#[test]
fn copy_circuit_unusable_rows() {
    assert_eq!(
        CopyCircuit::<Fr>::unusable_rows(),
        unusable_rows::<Fr, CopyCircuit::<Fr>>(()),
    )
}

/// Test copy circuit from copy events and test data
pub fn test_copy_circuit<F: Field>(
    k: u32,
    copy_events: Vec<CopyEvent>,
    max_copy_rows: usize,
    external_data: ExternalData,
) -> Result<(), Vec<VerifyFailure>> {
    let circuit =
        CopyCircuit::<F>::new_with_external_data(copy_events, max_copy_rows, external_data);

    let prover = MockProver::<F>::run(k, &circuit, vec![]).unwrap();
    prover.verify_par()
}

/// Test copy circuit with the provided block witness
pub fn test_copy_circuit_from_block<F: Field>(
    k: u32,
    block: Block<F>,
    chunk: Chunk<F>,
) -> Result<(), Vec<VerifyFailure>> {
    test_copy_circuit::<F>(
        k,
        block.copy_events,
        chunk.fixed_param.max_copy_rows,
        ExternalData {
            max_txs: chunk.fixed_param.max_txs,
            max_calldata: chunk.fixed_param.max_calldata,
            txs: block.txs,
            max_rws: chunk.fixed_param.max_rws,
            rws: block.rws,
            bytecodes: block.bytecodes,
        },
    )
}

fn gen_calldatacopy_data() -> CircuitInputBuilder<FixedCParams> {
    let length = 0x0fffusize;
    let code = bytecode! {
        PUSH32(Word::from(length))
        PUSH32(Word::from(0x00))
        PUSH32(Word::from(0x00))
        CALLDATACOPY
        STOP
    };
    let calldata = rand_bytes(length);
    let test_ctx = TestContext::<2, 1>::new(
        None,
        account_0_code_account_1_no_code(code),
        |mut txs, accs| {
            txs[0]
                .from(accs[1].address)
                .to(accs[0].address)
                .input(calldata.into());
        },
        |block, _txs| block.number(0xcafeu64),
    )
    .unwrap();
    let block: GethData = test_ctx.into();
    let builder = BlockData::new_from_geth_data(block.clone()).new_circuit_input_builder();
    builder
        .handle_block(&block.eth_block, &block.geth_traces)
        .unwrap()
}

fn gen_codecopy_data() -> CircuitInputBuilder<FixedCParams> {
    let code = bytecode! {
        PUSH32(Word::from(0x20))
        PUSH32(Word::from(0x00))
        PUSH32(Word::from(0x00))
        CODECOPY
        STOP
    };
    let test_ctx = TestContext::<2, 1>::simple_ctx_with_bytecode(code).unwrap();
    let block: GethData = test_ctx.into();
    let builder = BlockData::new_from_geth_data(block.clone()).new_circuit_input_builder();
    builder
        .handle_block(&block.eth_block, &block.geth_traces)
        .unwrap()
}

fn gen_extcodecopy_data() -> CircuitInputBuilder<FixedCParams> {
    let external_address = MOCK_ACCOUNTS[0];
    let code = bytecode! {
        PUSH1(0x30usize)
        PUSH1(0x0usize)
        PUSH1(0x0usize)
        PUSH20(external_address.to_word())
        EXTCODECOPY
        STOP
    };
    let code_ext = rand_bytes(0x0fffusize);
    let test_ctx = TestContext::<3, 1>::new(
        None,
        |accs| {
            accs[0].address(MOCK_ACCOUNTS[1]).code(code.clone());

            accs[1].address(external_address).code(code_ext.clone());

            accs[2]
                .address(MOCK_ACCOUNTS[2])
                .balance(Word::from(1u64 << 20));
        },
        |mut txs, accs| {
            txs[0].to(accs[0].address).from(accs[2].address);
        },
        |block, _tx| block.number(0xcafeu64),
    )
    .unwrap();
    let block: GethData = test_ctx.into();
    let builder = BlockData::new_from_geth_data(block.clone()).new_circuit_input_builder();
    builder
        .handle_block(&block.eth_block, &block.geth_traces)
        .unwrap()
}

fn gen_sha3_data() -> CircuitInputBuilder<FixedCParams> {
    let (code, _) = Sha3CodeGen::mem_eq_size(0x20, 0x200).gen_sha3_code();
    let test_ctx = TestContext::<2, 1>::simple_ctx_with_bytecode(code).unwrap();
    let block: GethData = test_ctx.into();
    let builder = BlockData::new_from_geth_data(block.clone()).new_circuit_input_builder();
    builder
        .handle_block(&block.eth_block, &block.geth_traces)
        .unwrap()
}

fn gen_tx_log_data() -> CircuitInputBuilder<FixedCParams> {
    let code = bytecode! {
        PUSH32(200)         // value
        PUSH32(0)           // offset
        MSTORE
        PUSH32(Word::MAX)   // topic
        PUSH1(32)           // length
        PUSH1(0)            // offset
        LOG1
        STOP
    };
    let test_ctx = TestContext::<2, 1>::simple_ctx_with_bytecode(code).unwrap();
    let block: GethData = test_ctx.into();
    // Needs default params for variadic check
    let mut builder =
        BlockData::new_from_geth_data_with_params(block.clone(), FixedCParams::default())
            .new_circuit_input_builder()
            .handle_block(&block.eth_block, &block.geth_traces)
            .unwrap();
    builder
}

#[test]
fn copy_circuit_valid_calldatacopy() {
    let builder = gen_calldatacopy_data();
    let block = block_convert::<Fr>(&builder).unwrap();
    let chunk = chunk_convert::<Fr>(&builder, 0).unwrap();
    assert_eq!(test_copy_circuit_from_block(14, block, chunk), Ok(()));
}

#[test]
fn copy_circuit_valid_codecopy() {
    let builder = gen_codecopy_data();
    let block = block_convert::<Fr>(&builder).unwrap();
    let chunk = chunk_convert::<Fr>(&builder, 0).unwrap();
    assert_eq!(test_copy_circuit_from_block(10, block, chunk), Ok(()));
}

#[test]
fn copy_circuit_valid_extcodecopy() {
    let builder = gen_extcodecopy_data();
    let block = block_convert::<Fr>(&builder).unwrap();
    let chunk = chunk_convert::<Fr>(&builder, 0).unwrap();
    assert_eq!(test_copy_circuit_from_block(14, block, chunk), Ok(()));
}

#[test]
fn copy_circuit_valid_sha3() {
    let builder = gen_sha3_data();
    let block = block_convert::<Fr>(&builder).unwrap();
    let chunk = chunk_convert::<Fr>(&builder, 0).unwrap();
    assert_eq!(test_copy_circuit_from_block(14, block, chunk), Ok(()));
}

#[test]
fn copy_circuit_valid_tx_log() {
    let builder = gen_tx_log_data();
    let block = block_convert::<Fr>(&builder).unwrap();
    let chunk = chunk_convert::<Fr>(&builder, 0).unwrap();
    assert_eq!(test_copy_circuit_from_block(10, block, chunk), Ok(()));
}

#[test]
fn copy_circuit_invalid_calldatacopy() {
    let mut builder = gen_calldatacopy_data();

    // modify first byte of first copy event
    builder.block.copy_events[0].bytes[0].0 =
        builder.block.copy_events[0].bytes[0].0.wrapping_add(1);

    let block = block_convert::<Fr>(&builder).unwrap();
    let chunk = chunk_convert::<Fr>(&builder, 0).unwrap();

    assert_error_matches(
        test_copy_circuit_from_block(14, block, chunk),
        vec!["Memory lookup", "Tx calldata lookup"],
    );
}

#[test]
fn copy_circuit_invalid_codecopy() {
    let mut builder = gen_codecopy_data();

    // modify first byte of first copy event
    builder.block.copy_events[0].bytes[0].0 =
        builder.block.copy_events[0].bytes[0].0.wrapping_add(1);

    let block = block_convert::<Fr>(&builder).unwrap();
    let chunk = chunk_convert::<Fr>(&builder, 0).unwrap();

    assert_error_matches(
        test_copy_circuit_from_block(10, block, chunk),
        vec!["Memory lookup", "Bytecode lookup"],
    );
}

#[test]
fn copy_circuit_invalid_extcodecopy() {
    let mut builder = gen_extcodecopy_data();

    // modify first byte of first copy event
    builder.block.copy_events[0].bytes[0].0 =
        builder.block.copy_events[0].bytes[0].0.wrapping_add(1);

    let block = block_convert::<Fr>(&builder).unwrap();
    let chunk = chunk_convert::<Fr>(&builder, 0).unwrap();

    assert_error_matches(
        test_copy_circuit_from_block(14, block, chunk),
        vec!["Memory lookup", "Bytecode lookup"],
    );
}

#[test]
fn copy_circuit_invalid_sha3() {
    let mut builder = gen_sha3_data();

    // modify first byte of first copy event
    builder.block.copy_events[0].bytes[0].0 =
        builder.block.copy_events[0].bytes[0].0.wrapping_add(1);

    let block = block_convert::<Fr>(&builder).unwrap();
    let chunk = chunk_convert::<Fr>(&builder, 0).unwrap();

    assert_error_matches(
        test_copy_circuit_from_block(14, block, chunk),
        vec!["Memory lookup"],
    );
}

#[test]
fn copy_circuit_invalid_tx_log() {
    let mut builder = gen_tx_log_data();

    // modify first byte of first copy event
    builder.block.copy_events[0].bytes[0].0 =
        builder.block.copy_events[0].bytes[0].0.wrapping_add(1);

    let block = block_convert::<Fr>(&builder).unwrap();
    let chunk = chunk_convert::<Fr>(&builder, 0).unwrap();

    assert_error_matches(
        test_copy_circuit_from_block(10, block, chunk),
        vec!["Memory lookup", "TxLog lookup"],
    );
}

#[test]
fn variadic_size_check() {
    let builder = gen_tx_log_data();
    let block1 = block_convert::<Fr>(&builder).unwrap();

    let block: GethData = TestContext::<0, 0>::new(None, |_| {}, |_, _| {}, |b, _| b)
        .unwrap()
        .into();
    let mut builder =
        BlockData::new_from_geth_data_with_params(block.clone(), FixedCParams::default())
            .new_circuit_input_builder()
            .handle_block(&block.eth_block, &block.geth_traces)
            .unwrap();
    let block2 = block_convert::<Fr>(&builder).unwrap();

    let circuit = CopyCircuit::<Fr>::new(block1.copy_events, block1.circuits_params.max_copy_rows);
    let prover1 = MockProver::<Fr>::run(14, &circuit, vec![]).unwrap();

    let circuit = CopyCircuit::<Fr>::new(
        block2.copy_events.clone(),
        block2.circuits_params.max_copy_rows,
    );
    let prover2 = MockProver::<Fr>::run(14, &circuit, vec![]).unwrap();

    assert_eq!(prover1.fixed(), prover2.fixed());
    assert_eq!(prover1.permutation(), prover2.permutation());
}

fn assert_error_matches(result: Result<(), Vec<VerifyFailure>>, names: Vec<&str>) {
    let errors = result.expect_err("result is not an error");
    assert_eq!(errors.len(), names.len(), "{:?}", errors);
    for i in 0..names.len() {
        match &errors[i] {
            VerifyFailure::Lookup {
                name: lookup_name, ..
            } => {
                assert_eq!(lookup_name, &names[i])
            }
            VerifyFailure::ConstraintNotSatisfied { .. } => panic!(),
            VerifyFailure::CellNotAssigned { .. } => panic!(),
            VerifyFailure::ConstraintPoisoned { .. } => panic!(),
            VerifyFailure::Permutation { .. } => panic!(),
        }
    }
}
