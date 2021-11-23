use criterion::{criterion_group, criterion_main, Criterion};
use halo2::{
    arithmetic::FieldExt,
    circuit::{Layouter, SimpleFloorPlanner},
    dev::MockProver,
    pairing::bn256::Fr as Fp,
    plonk::*,
};
use zkevm_circuits::evm_circuit::{EvmCircuit, ExecutionStep, Operation};

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

fn evm_circuit_benchmark(c: &mut Criterion) {
    let k = 14;
    let circuit = TestCircuit::default();
    let description = format!("prove evm circuit k = {}", k);
    let prover = MockProver::<Fp>::run(k, &circuit, vec![]).unwrap();
    c.bench_function(description.as_str(), |b| {
        b.iter(|| prover.verify().expect("failed to verify bench circuit"))
    });
}

criterion_group! {
    name = evm_prover;
    config = Criterion::default().sample_size(10);
    targets = evm_circuit_benchmark
}

criterion_main!(evm_prover);
