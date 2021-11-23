use criterion::{black_box, criterion_group, criterion_main, Criterion};
use halo2::transcript::{Blake2bRead, Blake2bWrite, Challenge255};
use halo2::{
    arithmetic::FieldExt,
    circuit::{Layouter, SimpleFloorPlanner},
    plonk::*,
    poly::commitment::Setup,
};
use pairing::bn256::Bn256;
use rand::SeedableRng;
use rand_xorshift::XorShiftRng;
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
    let public_inputs_size = 0;
    let circuit = TestCircuit::default();

    // Initialize the polynomial commitment parameters
    let rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32,
        0x54, 0x06, 0xbc, 0xe5,
    ]);
    let params = Setup::<Bn256>::new(k, rng);
    let verifier_params =
        Setup::<Bn256>::verifier_params(&params, public_inputs_size).unwrap();

    // Initialize the proving key
    let vk = keygen_vk(&params, &circuit).expect("keygen_vk should not fail");
    let pk =
        keygen_pk(&params, vk, &circuit).expect("keygen_pk should not fail");

    // Create a proof
    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
    create_proof(&params, &pk, &[circuit], &[&[]], &mut transcript)
        .expect("proof generation should not fail");
    let proof = transcript.finalize();
    let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);

    // Bench
    let description = format!("prove evm circuit k = {}", k);
    c.bench_function(description.as_str(), |b| {
        b.iter(|| {
            verify_proof(
                &verifier_params,
                pk.get_vk(),
                &[&[]],
                black_box(&mut transcript),
            )
            .expect("failed to verify bench circuit")
        })
    });
}

criterion_group! {
    name = evm_prover;
    config = Criterion::default().sample_size(10);
    targets = evm_circuit_benchmark
}

criterion_main!(evm_prover);
