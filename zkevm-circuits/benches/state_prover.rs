use bus_mapping::{
    circuit_input_builder::CircuitInputBuilder,
    eth_types::GethExecStep,
    mock::BlockData,
    operation::{MemoryOp, Operation, StackOp, StorageOp},
};
use criterion::{criterion_group, criterion_main, Criterion};
use halo2::transcript::{Blake2bRead, Blake2bWrite, Challenge255};
use halo2::{
    arithmetic::FieldExt,
    circuit::{Layouter, SimpleFloorPlanner},
    dev::MockProver,
    pairing::bn256::Fr as Fp,
    plonk::*,
    poly::commitment::Setup,
};
use pairing::bn256::Bn256;
use rand::SeedableRng;
use rand_xorshift::XorShiftRng;
use zkevm_circuits::state_circuit::state::Config;

#[derive(Default)]
struct StateCircuit<
    const GLOBAL_COUNTER_MAX: usize,
    const MEMORY_ROWS_MAX: usize,
    const MEMORY_ADDRESS_MAX: usize,
    const STACK_ROWS_MAX: usize,
    const STACK_ADDRESS_MAX: usize,
    const STORAGE_ROWS_MAX: usize,
> {
    memory_ops: Vec<Operation<MemoryOp>>,
    stack_ops: Vec<Operation<StackOp>>,
    storage_ops: Vec<Operation<StorageOp>>,
}

impl<
        F: FieldExt,
        const GLOBAL_COUNTER_MAX: usize,
        const MEMORY_ROWS_MAX: usize,
        const MEMORY_ADDRESS_MAX: usize,
        const STACK_ROWS_MAX: usize,
        const STACK_ADDRESS_MAX: usize,
        const STORAGE_ROWS_MAX: usize,
    > Circuit<F>
    for StateCircuit<
        GLOBAL_COUNTER_MAX,
        MEMORY_ROWS_MAX,
        MEMORY_ADDRESS_MAX,
        STACK_ROWS_MAX,
        STACK_ADDRESS_MAX,
        STORAGE_ROWS_MAX,
    >
{
    type Config = Config<
        F,
        GLOBAL_COUNTER_MAX,
        MEMORY_ROWS_MAX,
        MEMORY_ADDRESS_MAX,
        STACK_ROWS_MAX,
        STACK_ADDRESS_MAX,
        STORAGE_ROWS_MAX,
    >;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        Config::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        config.load(&mut layouter)?;
        config.assign(
            layouter,
            self.memory_ops.clone(),
            self.stack_ops.clone(),
            self.storage_ops.clone(),
        )?;

        Ok(())
    }
}

fn bus_mapping_benchmark(c: &mut Criterion) {
    let k = 14;
    let public_inputs_size = 0;
    let empty_circuit =
        StateCircuit::<2000, 100, 2, 100, 1023, 1000>::default();

    // Initialize the polynomial commitment parameters
    let rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32,
        0x54, 0x06, 0xbc, 0xe5,
    ]);
    let params = Setup::<Bn256>::new(k, rng);
    let verifier_params =
        Setup::<Bn256>::verifier_params(&params, public_inputs_size).unwrap();

    // Initialize the proving key
    let vk =
        keygen_vk(&params, &empty_circuit).expect("keygen_vk should not fail");
    let pk = keygen_pk(&params, vk, &empty_circuit)
        .expect("keygen_pk should not fail");

    let input_trace = r#"
        [
            {
                "pc": 5,
                "op": "PUSH1",
                "gas": 82,
                "gasCost": 3,
                "depth": 1,
                "stack": [],
                "memory": [
                  "0000000000000000000000000000000000000000000000000000000000000000",
                  "0000000000000000000000000000000000000000000000000000000000000000",
                  "0000000000000000000000000000000000000000000000000000000000000080"
                ]
              },
              {
                "pc": 7,
                "op": "MLOAD",
                "gas": 79,
                "gasCost": 3,
                "depth": 1,
                "stack": [
                  "40"
                ],
                "memory": [
                  "0000000000000000000000000000000000000000000000000000000000000000",
                  "0000000000000000000000000000000000000000000000000000000000000000",
                  "0000000000000000000000000000000000000000000000000000000000000080"
                ]
              },
              {
                "pc": 8,
                "op": "STOP",
                "gas": 76,
                "gasCost": 0,
                "depth": 1,
                "stack": [
                  "80"
                ],
                "memory": [
                  "0000000000000000000000000000000000000000000000000000000000000000",
                  "0000000000000000000000000000000000000000000000000000000000000000",
                  "0000000000000000000000000000000000000000000000000000000000000080"
                ]
              }
        ]
        "#;
    let geth_steps: Vec<GethExecStep> =
        serde_json::from_str(input_trace).expect("Error on trace parsing");
    let block = BlockData::new_single_tx_geth_steps(geth_steps);
    let mut builder = CircuitInputBuilder::new(
        block.eth_block.clone(),
        block.block_ctants.clone(),
    );
    builder.handle_tx(&block.eth_tx, &block.geth_trace).unwrap();

    let circuit = StateCircuit::<2000, 100, 2, 100, 1023, 1000> {
        memory_ops: builder.block.container.sorted_memory(),
        stack_ops: builder.block.container.sorted_stack(),
        storage_ops: builder.block.container.sorted_storage(),
    };

    // Create a proof
    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
    create_proof(&params, &pk, &[circuit], &[&[]], &mut transcript)
        .expect("proof generation should not fail");
    let proof = transcript.finalize();
    let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);

    let description = format!("prove state circuit k = {}", k);
    c.bench_function(description.as_str(), |b| {
        b.iter(|| {
            verify_proof(&verifier_params, pk.get_vk(), &[&[]], &mut transcript)
                .expect("failed to verify bench circuit")
        })
    });
}

criterion_group! {
    name = state_prover;
    config = Criterion::default().sample_size(10);
    targets = bus_mapping_benchmark
}

criterion_main!(state_prover);
