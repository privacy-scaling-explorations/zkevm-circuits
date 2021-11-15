use bus_mapping::{
    operation::{MemoryOp, Operation, StackOp, StorageOp},
    BlockConstants, ExecutionTrace,
};
use criterion::criterion_main;
use halo2::{
    arithmetic::FieldExt,
    circuit::{Layouter, SimpleFloorPlanner},
    pairing::bn256::{Bn256, Fr as Fp},
    plonk::*,
    poly::commitment::Setup,
    transcript::{Blake2bRead, Blake2bWrite, Challenge255},
};
use zkevm_circuits::state_circuit::state::Config;

fn bus_mapping_prover() {
    use rand::SeedableRng;
    use rand_xorshift::XorShiftRng;

    let k = 8;
    let public_inputs_size = 0;

    let empty_circuit: StateCircuit<2000, 100, 2, 100, 1023, 1000> =
        StateCircuit {
            memory_ops: Vec::new(),
            stack_ops: Vec::new(),
            storage_ops: Vec::new(),
        };

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

    let circuit = get_circuit();

    // Create a proof
    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);

    use std::time::Instant;
    let _dur = Instant::now();

    create_proof(&params, &pk, &[circuit], &[&[]], &mut transcript)
        .expect("proof generation should not fail");

    println!("proving period: {:?}", _dur.elapsed());

    let proof = transcript.finalize();

    let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
    verify_proof(&verifier_params, pk.get_vk(), &[&[]], &mut transcript)
        .unwrap();
}

fn get_circuit() -> StateCircuit<2000, 100, 2, 100, 1023, 1000> {
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
    let block_ctants = BlockConstants::<Fp>::default();
    let obtained_exec_trace =
        ExecutionTrace::from_trace_bytes(input_trace.as_bytes(), block_ctants)
            .unwrap();
    StateCircuit {
        memory_ops: obtained_exec_trace.sorted_memory_ops(),
        stack_ops: obtained_exec_trace.sorted_stack_ops(),
        storage_ops: obtained_exec_trace.sorted_storage_ops(),
    }
}

criterion_main!(bus_mapping_prover);

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
