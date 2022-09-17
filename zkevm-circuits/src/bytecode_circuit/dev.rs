use super::bytecode_unroller::{unroll, Config, UnrolledBytecode};
use crate::table::{BytecodeTable, KeccakTable};
use crate::util::power_of_randomness_from_instance;
use eth_types::Field;
use halo2_proofs::{
    circuit::Layouter,
    plonk::{ConstraintSystem, Error},
};
use halo2_proofs::{circuit::SimpleFloorPlanner, dev::MockProver, plonk::Circuit};
use std::vec;

#[derive(Default)]
pub(crate) struct BytecodeCircuitTester<F: Field> {
    bytecodes: Vec<UnrolledBytecode<F>>,
    size: usize,
    randomness: F,
}

fn get_randomness<F: Field>() -> F {
    F::from(123456)
}

impl<F: Field> Circuit<F> for BytecodeCircuitTester<F> {
    type Config = Config<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let bytecode_table = BytecodeTable::construct(meta);

        let randomness = power_of_randomness_from_instance::<_, 1>(meta);
        let keccak_table = KeccakTable::construct(meta);

        Config::configure(meta, randomness[0].clone(), bytecode_table, keccak_table)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        config.load(&mut layouter)?;
        config.keccak_table.dev_load(
            &mut layouter,
            self.bytecodes.iter().map(|b| &b.bytes),
            self.randomness,
        )?;
        config.assign_internal(
            &mut layouter,
            self.size,
            &self.bytecodes,
            self.randomness,
            false,
        )?;
        Ok(())
    }
}

impl<F: Field> BytecodeCircuitTester<F> {
    /// Verify that the selected bytecode fulfills the circuit
    pub fn verify_raw(k: u32, bytecodes: Vec<Vec<u8>>, randomness: F) {
        let unrolled: Vec<_> = bytecodes
            .iter()
            .map(|b| unroll(b.clone(), randomness))
            .collect();
        Self::verify(k, unrolled, randomness, true);
    }

    pub(crate) fn verify(
        k: u32,
        bytecodes: Vec<UnrolledBytecode<F>>,
        randomness: F,
        success: bool,
    ) {
        let circuit = BytecodeCircuitTester::<F> {
            bytecodes,
            size: 2usize.pow(k),
            randomness,
        };

        let num_rows = 1 << k;
        const NUM_BLINDING_ROWS: usize = 7 - 1;
        let instance = vec![vec![randomness; num_rows - NUM_BLINDING_ROWS]];
        let prover = MockProver::<F>::run(k, &circuit, instance).unwrap();
        let result = prover.verify();
        if let Err(failures) = &result {
            for failure in failures.iter() {
                println!("{}", failure);
            }
        }
        assert_eq!(result.is_ok(), success);
    }
}

/// Test bytecode circuit with raw bytecode
pub fn test_bytecode_circuit<F: Field>(k: u32, bytecodes: Vec<Vec<u8>>, randomness: F) {
    let unrolled: Vec<_> = bytecodes
        .iter()
        .map(|b| unroll(b.clone(), randomness))
        .collect();
    test_bytecode_circuit_unrolled(k, unrolled, randomness, true);
}

/// Test bytecode circuit with unrolled bytecode
pub fn test_bytecode_circuit_unrolled<F: Field>(
    k: u32,
    bytecodes: Vec<UnrolledBytecode<F>>,
    randomness: F,
    success: bool,
) {
    let circuit = BytecodeCircuitTester::<F> {
        bytecodes,
        size: 2usize.pow(k),
        randomness,
    };

    let num_rows = 1 << k;
    const NUM_BLINDING_ROWS: usize = 7 - 1;
    let instance = vec![vec![randomness; num_rows - NUM_BLINDING_ROWS]];
    let prover = MockProver::<F>::run(k, &circuit, instance).unwrap();
    let result = prover.verify();
    if let Err(failures) = &result {
        for failure in failures.iter() {
            println!("{}", failure);
        }
    }
    assert_eq!(result.is_ok(), success);
}
