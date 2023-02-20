use super::bytecode_unroller::{unroll, UnrolledBytecode};
use super::circuit::BytecodeCircuit;
#[cfg(feature = "poseidon-codehash")]
use super::circuit::to_poseidon_hash::{
    ToHashBlockBytecodeCircuitConfigArgs, ToHashBlockCircuitConfig, HASHBLOCK_BYTES_IN_FIELD,
};
#[cfg(not(feature = "poseidon-codehash"))]
use super::circuit::BytecodeCircuitConfig;
use super::circuit::{BytecodeCircuit, BytecodeCircuitConfigArgs};
#[cfg(feature = "poseidon-codehash")]
use crate::table::PoseidonTable;
#[cfg(feature = "poseidon-codehash")]
///alias for circuit config
pub type CircuitConfig<F> = ToHashBlockCircuitConfig<F, HASHBLOCK_BYTES_IN_FIELD>;
#[cfg(not(feature = "poseidon-codehash"))]
///alias for circuit config
pub type CircuitConfig<F> = BytecodeCircuitConfig<F>;

        #[cfg(feature = "poseidon-codehash")]
        let poseidon_table = PoseidonTable::construct(meta);
            let args = ToHashBlockBytecodeCircuitConfigArgs {
                base_args: args,
                poseidon_table,
            };

            CircuitConfig::new(meta, args)

use eth_types::Field;

use halo2_proofs::dev::MockProver;
use log::error;
        #[cfg(feature = "poseidon-codehash")]
        config.poseidon_table.dev_load(
            &mut layouter,
            self.bytecodes.iter().map(|b| &b.bytes),
            &challenges,
        )?;


impl<F: Field> BytecodeCircuit<F> {
    /// Verify that the selected bytecode fulfills the circuit
    pub fn verify_raw(k: u32, bytecodes: Vec<Vec<u8>>) {
        let unrolled: Vec<_> = bytecodes.iter().map(|b| unroll(b.clone())).collect();
        Self::verify(k, unrolled, true);
    }

    pub(crate) fn verify(k: u32, bytecodes: Vec<UnrolledBytecode<F>>, success: bool) {
        let circuit = BytecodeCircuit::<F>::new(bytecodes, 2usize.pow(k));

        let prover = MockProver::<F>::run(k, &circuit, Vec::new()).unwrap();
        let result = prover.verify();
        if let Err(failures) = &result {
            for failure in failures.iter() {
                error!("{}", failure);
            }
        }
        assert_eq!(result.is_ok(), success);
    }
}

/// Test bytecode circuit with unrolled bytecode
pub fn test_bytecode_circuit_unrolled<F: Field>(
    k: u32,
    bytecodes: Vec<UnrolledBytecode<F>>,
    success: bool,
) {
    let circuit = BytecodeCircuit::<F>::new(bytecodes, 2usize.pow(k));

    let prover = MockProver::<F>::run(k, &circuit, Vec::new()).unwrap();
    let result = prover.verify_par();
    if let Err(failures) = &result {
        for failure in failures.iter() {
            error!("{}", failure);
        }
    }
    let error_msg = if success { "valid" } else { "invalid" };
    assert_eq!(result.is_ok(), success, "proof must be {}", error_msg);
}
