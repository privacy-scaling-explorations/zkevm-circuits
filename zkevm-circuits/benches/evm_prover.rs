use criterion::criterion_main;
use halo2::{
    arithmetic::FieldExt,
    circuit::{Layouter, SimpleFloorPlanner},
    dev::MockProver,
    pairing::bn256::Fr as Fp,
    plonk::*,
};
use zkevm_circuits::evm_circuit::{EvmCircuit, ExecutionStep, Operation};

fn evm_circuit_prover() {
    let k = 14;
    let circuit = get_circuit();
    let prover = MockProver::<Fp>::run(k, &circuit, vec![]).unwrap();
    assert_eq!(prover.verify(), Ok(()));
}

criterion_main!(evm_circuit_prover);

fn get_circuit() -> TestCircuit<Fp> {
    TestCircuit::default()
}

#[derive(Clone)]
pub(crate) struct TestCircuitConfig<F: FieldExt> {
    evm_circuit: EvmCircuit<F>,
}

#[derive(Default)]
pub(crate) struct TestCircuit<F: FieldExt> {
    execution_steps: Vec<ExecutionStep>,
    operations: Vec<Operation<F>>,
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
        config.evm_circuit.load_fixed_tables(&mut layouter)?;
        config
            .evm_circuit
            .load_rw_tables(&mut layouter, &self.operations)?;
        config
            .evm_circuit
            .assign(&mut layouter, &self.execution_steps)
    }
}
