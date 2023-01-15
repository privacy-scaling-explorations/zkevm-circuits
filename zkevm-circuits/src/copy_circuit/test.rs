#![allow(unused_imports)]
pub use super::*;
use crate::witness::block_convert;
use crate::{
    evm_circuit::test::rand_bytes,
    evm_circuit::witness::Block,
    table::{BytecodeTable, RwTable, TxTable},
    util::Challenges,
};
use bus_mapping::{
    circuit_input_builder::{CircuitInputBuilder, CircuitsParams},
    evm::{gen_sha3_code, MemoryKind},
    mock::BlockData,
};
use eth_types::{bytecode, geth_types::GethData, Field, ToWord, Word};
use halo2_proofs::halo2curves::bn256::Fr;
use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner},
    dev::{MockProver, VerifyFailure},
    plonk::{Circuit, ConstraintSystem},
};
use mock::{test_ctx::helpers::account_0_code_account_1_no_code, TestContext, MOCK_ACCOUNTS};

impl<F: Field> Circuit<F> for CopyCircuit<F> {
    type Config = (CopyCircuitConfig<F>, Challenges<Challenge>);
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let tx_table = TxTable::construct(meta);
        let rw_table = RwTable::construct(meta);
        let bytecode_table = BytecodeTable::construct(meta);
        let q_enable = meta.fixed_column();
        let copy_table = CopyTable::construct(meta, q_enable);
        let challenges = Challenges::construct(meta);
        let challenge_exprs = challenges.exprs(meta);

        (
            CopyCircuitConfig::new(
                meta,
                CopyCircuitConfigArgs {
                    tx_table,
                    rw_table,
                    bytecode_table,
                    copy_table,
                    q_enable,
                    challenges: challenge_exprs,
                },
            ),
            challenges,
        )
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), halo2_proofs::plonk::Error> {
        let block = self.block.as_ref().unwrap();
        let challenge_values = config.1.values(&mut layouter);

        config
            .0
            .tx_table
            .load(&mut layouter, &block.txs, self.max_txs, &challenge_values)?;

        // TODO: RW table can't be passed `Challenges<Value<F>>` until the EVM circuit
        // is not migrated to the challenge API.
        config.0.rw_table.load(
            &mut layouter,
            &block.rws.table_assignments(),
            block.circuits_params.max_rws,
            challenge_values.evm_word(),
        )?;
        config
            .0
            .bytecode_table
            .load(&mut layouter, block.bytecodes.values(), &challenge_values)?;
        self.synthesize_sub(&config.0, &challenge_values, &mut layouter)
    }
}

/// Test copy circuit with the provided block witness
fn test_copy_circuit<F: Field>(k: u32, block: Block<F>) -> Result<(), Vec<VerifyFailure>> {
    let circuit = CopyCircuit::<F>::new(4, block);
    let prover = MockProver::<F>::run(k, &circuit, vec![]).unwrap();
    prover.verify_par()
}

fn gen_calldatacopy_data() -> CircuitInputBuilder {
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
    let mut builder = BlockData::new_from_geth_data_with_params(
        block.clone(),
        CircuitsParams {
            max_rws: 8192,
            ..Default::default()
        },
    )
    .new_circuit_input_builder();
    builder
        .handle_block(&block.eth_block, &block.geth_traces)
        .unwrap();
    builder
}

fn gen_codecopy_data() -> CircuitInputBuilder {
    let code = bytecode! {
        PUSH32(Word::from(0x20))
        PUSH32(Word::from(0x00))
        PUSH32(Word::from(0x00))
        CODECOPY
        STOP
    };
    let test_ctx = TestContext::<2, 1>::simple_ctx_with_bytecode(code).unwrap();
    let block: GethData = test_ctx.into();
    let mut builder = BlockData::new_from_geth_data(block.clone()).new_circuit_input_builder();
    builder
        .handle_block(&block.eth_block, &block.geth_traces)
        .unwrap();
    builder
}

fn gen_extcodecopy_data() -> CircuitInputBuilder {
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
    let mut builder = BlockData::new_from_geth_data(block.clone()).new_circuit_input_builder();
    builder
        .handle_block(&block.eth_block, &block.geth_traces)
        .unwrap();
    builder
}

fn gen_sha3_data() -> CircuitInputBuilder {
    let (code, _) = gen_sha3_code(0x20, 0x200, MemoryKind::EqualToSize);
    let test_ctx = TestContext::<2, 1>::simple_ctx_with_bytecode(code).unwrap();
    let block: GethData = test_ctx.into();
    let mut builder = BlockData::new_from_geth_data_with_params(
        block.clone(),
        CircuitsParams {
            max_rws: 2000,
            ..Default::default()
        },
    )
    .new_circuit_input_builder();
    builder
        .handle_block(&block.eth_block, &block.geth_traces)
        .unwrap();
    builder
}

fn gen_tx_log_data() -> CircuitInputBuilder {
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
    let mut builder = BlockData::new_from_geth_data(block.clone()).new_circuit_input_builder();
    builder
        .handle_block(&block.eth_block, &block.geth_traces)
        .unwrap();
    builder
}

#[test]
fn copy_circuit_valid_calldatacopy() {
    let builder = gen_calldatacopy_data();
    let block = block_convert::<Fr>(&builder.block, &builder.code_db).unwrap();
    assert_eq!(test_copy_circuit(14, block), Ok(()));
}

#[test]
fn copy_circuit_valid_codecopy() {
    let builder = gen_codecopy_data();
    let block = block_convert::<Fr>(&builder.block, &builder.code_db).unwrap();
    assert_eq!(test_copy_circuit(10, block), Ok(()));
}

#[test]
fn copy_circuit_valid_extcodecopy() {
    let builder = gen_extcodecopy_data();
    let block = block_convert::<Fr>(&builder.block, &builder.code_db).unwrap();
    assert_eq!(test_copy_circuit(14, block), Ok(()));
}

#[test]
fn copy_circuit_valid_sha3() {
    let builder = gen_sha3_data();
    let block = block_convert::<Fr>(&builder.block, &builder.code_db).unwrap();
    assert_eq!(test_copy_circuit(20, block), Ok(()));
}

#[test]
fn copy_circuit_tx_log() {
    let builder = gen_tx_log_data();
    let block = block_convert::<Fr>(&builder.block, &builder.code_db).unwrap();
    assert_eq!(test_copy_circuit(10, block), Ok(()));
}

// TODO: replace these with deterministic failure tests
// see more: https://github.com/privacy-scaling-explorations/zkevm-circuits/issues/1065

// fn perturb_tag(block: &mut bus_mapping::circuit_input_builder::Block) {
//     debug_assert!(!block.copy_events.is_empty());
//     debug_assert!(!block.copy_events[0].steps.is_empty());
//
//     let copy_event = &mut block.copy_events[0];
//     let mut rng = rand::thread_rng();
//     let rand_idx = (0..copy_event.steps.len()).choose(&mut rng).unwrap();
//     let (is_read_step, mut perturbed_step) = match rng.gen::<f32>() {
//         f if f < 0.5 => (true, copy_event.steps[rand_idx].0.clone()),
//         _ => (false, copy_event.steps[rand_idx].1.clone()),
//     };
//     match rng.gen::<f32>() {
//         _ => perturbed_step.value = rng.gen(),
//     }
//
//         copy_event.bytes[rand_idx] = perturbed_step;
// }

// #[test]
// fn copy_circuit_invalid_calldatacopy() {
//     let mut builder = gen_calldatacopy_data();
//     perturb_tag(&mut builder.block);
//     let block = block_convert(&builder.block, &builder.code_db);
//     assert!(test_copy_circuit(10, block).is_err());
// }

// #[test]
// fn copy_circuit_invalid_codecopy() {
//     let mut builder = gen_codecopy_data();
//     perturb_tag(&mut builder.block);
//     let block = block_convert(&builder.block, &builder.code_db);
//     assert!(test_copy_circuit(10, block).is_err());
// }

// #[test]
// fn copy_circuit_invalid_sha3() {
//     let mut builder = gen_sha3_data();
//     perturb_tag(&mut builder.block);
//     let block = block_convert(&builder.block, &builder.code_db);
//     assert!(test_copy_circuit(20, block).is_err());
// }
