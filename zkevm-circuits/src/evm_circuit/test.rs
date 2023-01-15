#![allow(unused_imports)]
use crate::evm_circuit::step::ExecutionState;
pub use crate::evm_circuit::*;
use crate::exp_circuit::param::OFFSET_INCREMENT;
use crate::witness::block_convert;
use bus_mapping::{circuit_input_builder::CircuitsParams, mock::BlockData};
use eth_types::{bytecode, geth_types::GethData, Field, Word};
use halo2_proofs::{
    dev::{MockProver, VerifyFailure},
    halo2curves::bn256::Fr,
    plonk::{Circuit, ConstraintSystem},
};
use mock::test_ctx::{helpers::*, TestContext};
use rand::{
    distributions::uniform::{SampleRange, SampleUniform},
    random, thread_rng, Rng,
};

pub(crate) fn rand_range<T, R>(range: R) -> T
where
    T: SampleUniform,
    R: SampleRange<T>,
{
    thread_rng().gen_range(range)
}

pub(crate) fn rand_bytes(n: usize) -> Vec<u8> {
    (0..n).map(|_| random()).collect()
}

pub(crate) fn rand_bytes_array<const N: usize>() -> [u8; N] {
    [(); N].map(|_| random())
}

pub(crate) fn rand_word() -> Word {
    Word::from_big_endian(&rand_bytes_array::<32>())
}

impl<F: Field> EvmCircuit<F> {
    pub fn new_dev(block: Block<F>, fixed_table_tags: Vec<FixedTableTag>) -> Self {
        Self {
            block: Some(block),
            fixed_table_tags,
        }
    }

    pub fn get_active_rows(block: &Block<F>) -> (Vec<usize>, Vec<usize>) {
        let mut cs = ConstraintSystem::default();
        let config = EvmCircuit::<F>::configure(&mut cs);
        config.0.get_active_rows(block)
    }
}

pub(crate) fn run_test_circuit_geth_data_default<F: Field>(
    block: GethData,
) -> Result<(), Vec<VerifyFailure>> {
    let mut builder =
        BlockData::new_from_geth_data_with_params(block.clone(), CircuitsParams::default())
            .new_circuit_input_builder();
    builder
        .handle_block(&block.eth_block, &block.geth_traces)
        .unwrap();
    let block = block_convert::<Fr>(&builder.block, &builder.code_db).unwrap();
    run_test_circuit(block)
}

pub(crate) fn run_test_circuit_geth_data<F: Field>(
    block: GethData,
    circuits_params: CircuitsParams,
) -> Result<(), Vec<VerifyFailure>> {
    let mut builder = BlockData::new_from_geth_data_with_params(block.clone(), circuits_params)
        .new_circuit_input_builder();
    builder
        .handle_block(&block.eth_block, &block.geth_traces)
        .unwrap();
    let block = block_convert::<Fr>(&builder.block, &builder.code_db).unwrap();
    run_test_circuit(block)
}

pub fn get_test_degree<F: Field>(block: &Block<F>) -> u32 {
    let num_rows_required_for_execution_steps: usize =
        EvmCircuit::<F>::get_num_rows_required(block);
    let num_rows_required_for_rw_table: usize = block.circuits_params.max_rws;
    let num_rows_required_for_fixed_table: usize = detect_fixed_table_tags(block)
        .iter()
        .map(|tag| tag.build::<F>().count())
        .sum();
    let num_rows_required_for_bytecode_table: usize = block
        .bytecodes
        .values()
        .map(|bytecode| bytecode.bytes.len() + 1)
        .sum();
    let num_rows_required_for_copy_table: usize =
        block.copy_events.iter().map(|c| c.bytes.len() * 2).sum();
    let num_rows_required_for_keccak_table: usize = block.keccak_inputs.len();
    let num_rows_required_for_tx_table: usize =
        block.txs.iter().map(|tx| 9 + tx.call_data.len()).sum();
    let num_rows_required_for_exp_table: usize = block
        .exp_events
        .iter()
        .map(|e| e.steps.len() * OFFSET_INCREMENT)
        .sum();

    const NUM_BLINDING_ROWS: usize = 64;

    let rows_needed: usize = itertools::max([
        num_rows_required_for_execution_steps,
        num_rows_required_for_rw_table,
        num_rows_required_for_fixed_table,
        num_rows_required_for_bytecode_table,
        num_rows_required_for_copy_table,
        num_rows_required_for_keccak_table,
        num_rows_required_for_tx_table,
        num_rows_required_for_exp_table,
    ])
    .unwrap();

    let k = log2_ceil(NUM_BLINDING_ROWS + rows_needed);
    log::debug!(
        "num_rows_requred_for rw_table={}, fixed_table={}, bytecode_table={}, \
            copy_table={}, keccak_table={}, tx_table={}, exp_table={}",
        num_rows_required_for_rw_table,
        num_rows_required_for_fixed_table,
        num_rows_required_for_bytecode_table,
        num_rows_required_for_copy_table,
        num_rows_required_for_keccak_table,
        num_rows_required_for_tx_table,
        num_rows_required_for_exp_table
    );
    log::debug!("evm circuit uses k = {}, rows = {}", k, rows_needed);
    k
}

pub fn get_test_cicuit_from_block<F: Field>(block: Block<F>) -> EvmCircuit<F> {
    let fixed_table_tags = detect_fixed_table_tags(&block);

    EvmCircuit::<F>::new_dev(block, fixed_table_tags)
}

pub(crate) fn run_test_circuit<F: Field>(block: Block<F>) -> Result<(), Vec<VerifyFailure>> {
    let k = get_test_degree(&block);

    let (active_gate_rows, active_lookup_rows) = EvmCircuit::<F>::get_active_rows(&block);

    let circuit = get_test_cicuit_from_block(block);
    let prover = MockProver::<F>::run(k, &circuit, vec![]).unwrap();
    prover.verify_at_rows_par(active_gate_rows.into_iter(), active_lookup_rows.into_iter())
}

fn get_empty_witness_block() -> Block<Fr> {
    let block: GethData = TestContext::<0, 0>::new(None, |_| {}, |_, _| {}, |b, _| b)
        .unwrap()
        .into();
    let mut builder =
        BlockData::new_from_geth_data_with_params(block.clone(), CircuitsParams::default())
            .new_circuit_input_builder();
    builder
        .handle_block(&block.eth_block, &block.geth_traces)
        .unwrap();

    block_convert(&builder.block, &builder.code_db).unwrap()
}

#[test]
pub(crate) fn empty_evm_circuit_no_padding() {
    let block = get_empty_witness_block();
    run_test_circuit(block).unwrap();
}

#[test]
pub(crate) fn empty_evm_circuit_with_padding() {
    let mut block = get_empty_witness_block();
    block.evm_circuit_pad_to = (1 << 18) - 100;
    run_test_circuit(block).unwrap();
}

/// This function prints to stdout a table with all the implemented states
/// and their responsible opcodes with the following stats:
/// - height: number of rows in the EVM circuit used by the execution state
/// - gas: gas value used for the opcode execution
/// - height/gas: ratio between circuit cost and gas cost
///
/// Run with:
/// `cargo test -p zkevm-circuits --release get_evm_states_stats --
/// --nocapture --ignored`
#[ignore]
#[test]
pub(crate) fn get_evm_states_stats() {
    let mut meta = ConstraintSystem::<Fr>::default();
    let circuit = EvmCircuit::configure(&mut meta);

    let mut implemented_states = Vec::new();
    for state in ExecutionState::iter() {
        let height = circuit.0.execution.get_step_height_option(state);
        if let Some(h) = height {
            implemented_states.push((state, h));
        }
    }

    let mut stats = Vec::new();
    for (state, h) in implemented_states {
        for opcode in state.responsible_opcodes() {
            let mut code = bytecode! {
                PUSH2(0x8000)
                PUSH2(0x00)
                PUSH2(0x10)
                PUSH2(0x20)
                PUSH2(0x30)
                PUSH2(0x40)
                PUSH2(0x50)
            };
            code.write_op(opcode);
            code.write_op(OpcodeId::STOP);
            let block: GethData = TestContext::<2, 1>::new(
                None,
                account_0_code_account_1_no_code(code),
                tx_from_1_to_0,
                |block, _tx| block.number(0xcafeu64),
            )
            .unwrap()
            .into();
            let gas_cost = block.geth_traces[0].struct_logs[7].gas_cost.0;
            stats.push((state, opcode, h, gas_cost));
        }
    }

    println!(
        "| {: <14} | {: <14} | {: <2} | {: >6} | {: <5} |",
        "state", "opcode", "h", "g", "h/g"
    );
    println!("| ---            | ---            | ---|    --- | ---   |");
    for (state, opcode, height, gas_cost) in stats {
        println!(
            "| {: <14?} | {: <14?} | {: >2} | {: >6} | {: >1.3} |",
            state,
            opcode,
            height,
            gas_cost,
            height as f64 / gas_cost as f64
        );
    }
}
