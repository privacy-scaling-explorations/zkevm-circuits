//! Evm circuit benchmarks

use halo2::{
    arithmetic::FieldExt,
    circuit::{Layouter, SimpleFloorPlanner},
    plonk::{Circuit, ConstraintSystem, Error},
};
use zkevm_circuits::evm_circuit::{EvmCircuit, ExecutionStep, Operation};

use bus_mapping::evm::OpcodeId;

#[derive(Clone)]
pub(crate) struct TestCircuitConfig<F> {
    evm_circuit: EvmCircuit<F>,
}

// contruct bytecode table from ExecutionSteps of test
pub(crate) fn assgin_byte_table_step(
    execution_steps: &[ExecutionStep],
) -> Vec<[u32; 4]> {
    // TODO: add keccak hash (byte_codes)
    let code_hash = 0_u32;
    let mut i = 0;
    let mut bytecode_table = Vec::<[u32; 4]>::new();

    for curr_step in execution_steps.iter() {
        let byte = curr_step.opcode.as_u8();
        if OpcodeId::PUSH1.as_u8() <= byte && byte <= OpcodeId::PUSH32.as_u8() {
            bytecode_table.push([code_hash, i, 1, byte as u32]);
            i += 1;
            // loading data segement
            for data in curr_step.values[0].to_bytes_le() {
                bytecode_table.push([code_hash, i, 0, data as u32]);

                i += 1; // next byte
            }
        } else {
            bytecode_table.push([code_hash, i, 1, byte as u32]);
            i += 1
        }
    }

    bytecode_table
}

#[derive(Default)]
pub(crate) struct TestCircuit<F> {
    execution_steps: Vec<ExecutionStep>,
    operations: Vec<Operation<F>>,
    including_large_tables: bool,
}

impl<F: FieldExt> Circuit<F> for TestCircuit<F> {
    type Config = TestCircuitConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        Self::Config {
            // TODO: use a random r instead of 1
            evm_circuit: EvmCircuit::configure(meta, F::one()),
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        config
            .evm_circuit
            .load_fixed_tables(&mut layouter, self.including_large_tables)?;
        config
            .evm_circuit
            .load_rw_tables(&mut layouter, &self.operations)?;

        // load bytecode source from test sequence
        let bytecode_table = assgin_byte_table_step(&self.execution_steps);

        config
            .evm_circuit
            .load_bytecode_tables(&mut layouter, bytecode_table)?;

        config
            .evm_circuit
            .assign(&mut layouter, &self.execution_steps)
    }
}

#[cfg(test)]
mod evm_circ_benches {
    use super::*;
    use halo2::circuit::SimpleFloorPlanner;
    use halo2::plonk::{create_proof, keygen_pk, keygen_vk};
    use std::env::var;

    #[derive(Clone)]
    pub(crate) struct TestCircuitConfig<F> {
        evm_circuit: EvmCircuit<F>,
    }

    // contruct bytecode table from ExecutionSteps of test
    pub(crate) fn assgin_byte_table_step(
        execution_steps: &[ExecutionStep],
    ) -> Vec<[u32; 4]> {
        // TODO: add keccak hash (byte_codes)
        let code_hash = 0_u32;
        let mut i = 0;
        let mut bytecode_table = Vec::<[u32; 4]>::new();

        for curr_step in execution_steps.iter() {
            let byte = curr_step.opcode.as_u8();
            if OpcodeId::PUSH1.as_u8() <= byte
                && byte <= OpcodeId::PUSH32.as_u8()
            {
                bytecode_table.push([code_hash, i, 1, byte as u32]);
                i += 1;
                // loading data segement
                for data in curr_step.values[0].to_bytes_le() {
                    bytecode_table.push([code_hash, i, 0, data as u32]);

                    i += 1; // next byte
                }
            } else {
                bytecode_table.push([code_hash, i, 1, byte as u32]);
                i += 1
            }
        }

        bytecode_table
    }

    #[derive(Default)]
    pub(crate) struct TestCircuit<F> {
        execution_steps: Vec<ExecutionStep>,
        operations: Vec<Operation<F>>,
        including_large_tables: bool,
    }

    impl<F> TestCircuit<F> {
        pub fn new(
            execution_steps: Vec<ExecutionStep>,
            operations: Vec<Operation<F>>,
            including_large_tables: bool,
        ) -> Self {
            Self {
                execution_steps,
                operations,
                including_large_tables,
            }
        }
    }

    impl<F: FieldExt> Circuit<F> for TestCircuit<F> {
        type Config = TestCircuitConfig<F>;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            Self::Config {
                // TODO: use a random r instead of 1
                evm_circuit: EvmCircuit::configure(meta, F::one()),
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            config.evm_circuit.load_fixed_tables(
                &mut layouter,
                self.including_large_tables,
            )?;
            config
                .evm_circuit
                .load_rw_tables(&mut layouter, &self.operations)?;

            // load bytecode source from test sequence
            let bytecode_table = assgin_byte_table_step(&self.execution_steps);

            config
                .evm_circuit
                .load_bytecode_tables(&mut layouter, bytecode_table)?;

            config
                .evm_circuit
                .assign(&mut layouter, &self.execution_steps)
        }
    }

    #[cfg_attr(not(feature = "benches"), ignore)]
    #[test]
    fn bench_evm_circuit_prover() {
        use ark_std::{end_timer, start_timer};
        use halo2::{
            plonk::verify_proof,
            poly::commitment::Setup,
            transcript::{Blake2bRead, Blake2bWrite, Challenge255},
        };
        use pairing::bn256::Bn256;
        use rand::SeedableRng;
        use rand_xorshift::XorShiftRng;

        let degree: usize = var("DEGREE")
            .expect("No DEGREE env var was provided")
            .parse()
            .unwrap("Cannot parse DEGREE env var as usize");

        let public_inputs_size = 0;
        let empty_circuit = TestCircuit::default();

        let circuit = TestCircuit::new(vec![], vec![], true);

        // Initialize the polynomial commitment parameters
        let rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37,
            0x32, 0x54, 0x06, 0xbc, 0xe5,
        ]);

        // Bench setup generation
        let setup_message =
            format!("Setup generation with degree = {}", degree);
        let start1 = start_timer!(|| setup_message);
        let params = Setup::<Bn256>::new(degree as u32, rng);
        let verifier_params =
            Setup::<Bn256>::verifier_params(&params, public_inputs_size)
                .unwrap();
        end_timer!(start1);

        // Initialize the proving key
        let vk = keygen_vk(&params, &empty_circuit)
            .expect("keygen_vk should not fail");
        let pk = keygen_pk(&params, vk, &empty_circuit)
            .expect("keygen_pk should not fail");
        // Create a proof
        let mut transcript =
            Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);

        // Bench proof generation time
        let proof_message =
            format!("EVM Proof generation with {} rows", degree);
        let start2 = start_timer!(|| proof_message);

        create_proof(&params, &pk, &[circuit], &[&[]], &mut transcript)
            .expect("proof generation should not fail");
        let proof = transcript.finalize();
        end_timer!(start2);

        // Bench verification time
        let start3 = start_timer!(|| "EVM Proof verification");
        let mut transcript =
            Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);

        verify_proof(&verifier_params, pk.get_vk(), &[&[]], &mut transcript)
            .expect("failed to verify bench circuit");
        end_timer!(start3);
    }
}
