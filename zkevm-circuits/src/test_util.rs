use eth_types::evm_types::Gas;
use halo2_proofs::{
    arithmetic::BaseExt,
    dev::{
        metadata::Region,
        FailureLocation::InRegion,
        MockProver,
        VerifyFailure::{self, ConstraintNotSatisfied, Lookup},
    },
};
use pairing::bn256::Fr;

use crate::{evm_circuit::table::FixedTableTag, state_circuit::StateCircuit};

pub enum FixedTableConfig {
    Incomplete,
    Complete,
}

pub fn get_fixed_table(conf: FixedTableConfig) -> Vec<FixedTableTag> {
    match conf {
        FixedTableConfig::Incomplete => {
            vec![
                FixedTableTag::Range16,
                FixedTableTag::Range32,
                FixedTableTag::Range256,
                FixedTableTag::Range512,
                FixedTableTag::SignByte,
                FixedTableTag::ResponsibleOpcode,
            ]
        }
        FixedTableConfig::Complete => FixedTableTag::iterator().collect(),
    }
}

pub struct BytecodeTestConfig {
    pub randomness: Fr,
    pub enable_evm_circuit_test: bool,
    pub evm_circuit_lookup_tags: Vec<FixedTableTag>,
    pub enable_state_circuit_test: bool,
    pub gas_limit: u64,
}

impl Default for BytecodeTestConfig {
    fn default() -> Self {
        Self {
            gas_limit: 1_000_000u64,
            enable_evm_circuit_test: true,
            enable_state_circuit_test: true,
            randomness: Fr::rand(),
            evm_circuit_lookup_tags: get_fixed_table(FixedTableConfig::Incomplete),
        }
    }
}

pub fn run_test_circuits(bytecode: eth_types::Bytecode) -> Result<(), Vec<VerifyFailure>> {
    run_test_circuits_with_config(bytecode, BytecodeTestConfig::default())
}

pub fn run_test_circuits_with_config(
    bytecode: eth_types::Bytecode,
    config: BytecodeTestConfig,
) -> Result<(), Vec<VerifyFailure>> {
    // Step 1: execute the bytecode and get trace
    let block_trace = bus_mapping::mock::BlockData::new_from_geth_data(
        mock::new_single_tx_trace_code_gas(&bytecode, Gas(config.gas_limit)).unwrap(),
    );
    let mut builder = block_trace.new_circuit_input_builder();
    builder
        .handle_tx(&block_trace.eth_tx, &block_trace.geth_trace)
        .unwrap();

    // Step 2: run evm circuit test
    if config.enable_evm_circuit_test {
        let block_for_evm_circuit = crate::evm_circuit::witness::block_convert(
            config.randomness,
            bytecode.code(),
            &builder.block,
        );
        crate::evm_circuit::test::run_test_circuit(
            block_for_evm_circuit,
            config.evm_circuit_lookup_tags,
        )?;
    }

    // Step 3: run state circuit test
    // TODO:
    //     (1) calculate circuit size(like MEMORY_ROWS_MAX etc) from block
    // rather than hard code  (2) use randomness as one of the circuit
    // public input, since randomness in state circuit and evm
    // circuit must be same
    if config.enable_state_circuit_test {
        let block_for_state_circuit = builder.block;
        let state_circuit = StateCircuit::<Fr, true, 2000, 100, 100, 100, 1023, 100> {
            randomness: config.randomness,
            memory_ops: block_for_state_circuit.container.sorted_memory(),
            stack_ops: block_for_state_circuit.container.sorted_stack(),
            storage_ops: block_for_state_circuit.container.sorted_storage(),
        };

        let prover = MockProver::<Fr>::run(12, &state_circuit, vec![]).unwrap();
        prover.verify()?;
    }

    Ok(())
}

pub fn constraint_not_satisfied(
    gate_index: usize,
    gate_name: &'static str,
    index: usize,
) -> VerifyFailure {
    let region = Region::from((0, "test".to_string()));
    let location = InRegion { region, offset: 0 };
    ConstraintNotSatisfied {
        constraint: ((gate_index, gate_name).into(), index, "").into(),
        location,
        cell_values: vec![],
    }
}

pub fn lookup_fail(
    index: usize,
    name: String,
    offset: usize,
    lookup_index: usize,
) -> VerifyFailure {
    Lookup {
        lookup_index,
        location: InRegion {
            region: Region::from((index, name)),
            offset,
        },
    }
}
