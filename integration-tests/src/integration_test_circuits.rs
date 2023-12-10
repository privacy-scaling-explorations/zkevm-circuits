use crate::{get_client, GenDataOutput};
use bus_mapping::{
    circuit_input_builder::{BuilderClient, CircuitInputBuilder, FixedCParams},
    mock::BlockData,
};
use eth_types::geth_types::GethData;
use halo2_proofs::{
    self,
    circuit::Value,
    dev::{CellValue, MockProver},
    halo2curves::{
        bn256::{Bn256, Fr, G1Affine},
        pairing::Engine,
    },
    plonk::{
        create_proof, keygen_pk, keygen_vk, permutation::Assembly, verify_proof, Circuit,
        ConstraintSystem, ProvingKey,
    },
    poly::{
        commitment::ParamsProver,
        kzg::{
            commitment::{KZGCommitmentScheme, ParamsKZG, ParamsVerifierKZG},
            multiopen::{ProverSHPLONK, VerifierSHPLONK},
            strategy::SingleStrategy,
        },
    },
};
use lazy_static::lazy_static;
use mock::TestContext;
use rand_chacha::rand_core::SeedableRng;
use rand_xorshift::XorShiftRng;
use std::{collections::HashMap, marker::PhantomData, sync::Mutex};
use tokio::sync::Mutex as TokioMutex;
use zkevm_circuits::{
    bytecode_circuit::TestBytecodeCircuit,
    copy_circuit::TestCopyCircuit,
    evm_circuit::TestEvmCircuit,
    exp_circuit::TestExpCircuit,
    keccak_circuit::TestKeccakCircuit,
    pi_circuit::TestPiCircuit,
    root_circuit::{
        compile, Config, EvmTranscript, NativeLoader, PoseidonTranscript, RootCircuit, Shplonk,
        UserChallenge,
    },
    state_circuit::TestStateCircuit,
    super_circuit::SuperCircuit,
    tx_circuit::TestTxCircuit,
    util::SubCircuit,
    witness::{block_convert, chunk_convert, Block, Chunk},
};

/// TEST_MOCK_RANDOMNESS
const TEST_MOCK_RANDOMNESS: u64 = 0x100;
///
const TOTAL_CHUNKS: usize = 1;
/// MAX_TXS
const MAX_TXS: usize = 4;
/// MAX_CALLDATA
const MAX_CALLDATA: usize = 512;
/// MAX_RWS
const MAX_RWS: usize = 5888;
/// MAX_BYTECODE
const MAX_BYTECODE: usize = 5000;
/// MAX_COPY_ROWS
const MAX_COPY_ROWS: usize = 5888;
/// MAX_EVM_ROWS
const MAX_EVM_ROWS: usize = 10000;
/// MAX_EXP_STEPS
const MAX_EXP_STEPS: usize = 1000;

const MAX_KECCAK_ROWS: usize = 38000;

const CIRCUITS_PARAMS: FixedCParams = FixedCParams {
    total_chunks: TOTAL_CHUNKS,
    max_rws: MAX_RWS,
    max_txs: MAX_TXS,
    max_calldata: MAX_CALLDATA,
    max_bytecode: MAX_BYTECODE,
    max_copy_rows: MAX_COPY_ROWS,
    max_evm_rows: MAX_EVM_ROWS,
    max_exp_steps: MAX_EXP_STEPS,
    max_keccak_rows: MAX_KECCAK_ROWS,
};

const EVM_CIRCUIT_DEGREE: u32 = 18;
const STATE_CIRCUIT_DEGREE: u32 = 17;
const TX_CIRCUIT_DEGREE: u32 = 20;
const BYTECODE_CIRCUIT_DEGREE: u32 = 16;
const COPY_CIRCUIT_DEGREE: u32 = 16;
const KECCAK_CIRCUIT_DEGREE: u32 = 16;
const SUPER_CIRCUIT_DEGREE: u32 = 20;
const EXP_CIRCUIT_DEGREE: u32 = 16;
const PI_CIRCUIT_DEGREE: u32 = 17;
const ROOT_CIRCUIT_SMALL_DEGREE: u32 = 24;
// Big is for SuperCircuit only
const ROOT_CIRCUIT_BIG_DEGREE: u32 = 26;

lazy_static! {
    /// Data generation.
    static ref GEN_DATA: GenDataOutput = GenDataOutput::load();
    static ref RNG: XorShiftRng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);
}

lazy_static! {
    static ref GEN_PARAMS: Mutex<HashMap<u32, ParamsKZG<Bn256>>> = Mutex::new(HashMap::new());
}

lazy_static! {
    /// Integration test for EVM circuit
    pub static ref EVM_CIRCUIT_TEST: TokioMutex<IntegrationTest<TestEvmCircuit<Fr>>> =
    TokioMutex::new(IntegrationTest::new("EVM", EVM_CIRCUIT_DEGREE, ROOT_CIRCUIT_SMALL_DEGREE));

    /// Integration test for State circuit
    pub static ref STATE_CIRCUIT_TEST: TokioMutex<IntegrationTest<TestStateCircuit<Fr>>> =
    TokioMutex::new(IntegrationTest::new("State", STATE_CIRCUIT_DEGREE, ROOT_CIRCUIT_SMALL_DEGREE));

    /// Integration test for State circuit
    pub static ref TX_CIRCUIT_TEST: TokioMutex<IntegrationTest<TestTxCircuit<Fr>>> =
    TokioMutex::new(IntegrationTest::new("Tx", TX_CIRCUIT_DEGREE, ROOT_CIRCUIT_SMALL_DEGREE));

    /// Integration test for Bytecode circuit
    pub static ref BYTECODE_CIRCUIT_TEST: TokioMutex<IntegrationTest<TestBytecodeCircuit<Fr>>> =
    TokioMutex::new(IntegrationTest::new("Bytecode", BYTECODE_CIRCUIT_DEGREE, ROOT_CIRCUIT_SMALL_DEGREE));

    /// Integration test for Copy circuit
    pub static ref COPY_CIRCUIT_TEST: TokioMutex<IntegrationTest<TestCopyCircuit<Fr>>> =
    TokioMutex::new(IntegrationTest::new("Copy", COPY_CIRCUIT_DEGREE, ROOT_CIRCUIT_SMALL_DEGREE));

    /// Integration test for Keccak circuit
    pub static ref KECCAK_CIRCUIT_TEST: TokioMutex<IntegrationTest<TestKeccakCircuit<Fr>>> =
    TokioMutex::new(IntegrationTest::new("Keccak", KECCAK_CIRCUIT_DEGREE, ROOT_CIRCUIT_SMALL_DEGREE));

    /// Integration test for Copy circuit
    pub static ref SUPER_CIRCUIT_TEST: TokioMutex<IntegrationTest<SuperCircuit::<Fr>>> =
    TokioMutex::new(IntegrationTest::new("Super", SUPER_CIRCUIT_DEGREE, ROOT_CIRCUIT_BIG_DEGREE));

    /// Integration test for Exp circuit
    pub static ref EXP_CIRCUIT_TEST: TokioMutex<IntegrationTest<TestExpCircuit::<Fr>>> =
    TokioMutex::new(IntegrationTest::new("Exp", EXP_CIRCUIT_DEGREE, ROOT_CIRCUIT_SMALL_DEGREE));

    /// Integration test for Pi circuit
    pub static ref PI_CIRCUIT_TEST: TokioMutex<IntegrationTest<TestPiCircuit::<Fr>>> =
    TokioMutex::new(IntegrationTest::new("Pi", PI_CIRCUIT_DEGREE, ROOT_CIRCUIT_SMALL_DEGREE));
}

lazy_static! {
    /// Cache of real proofs from each block to be reused with the Root circuit tests
    static ref PROOF_CACHE: TokioMutex<HashMap<String, Vec<u8>>> = TokioMutex::new(HashMap::new());
}

/// Generate a real proof of a Circuit with Poseidon transcript and Shplonk accumulation scheme.
/// Verify the proof and return it.  The proof is suitable to be verified by the Root Circuit.
fn test_actual_circuit<C: Circuit<Fr>>(
    circuit: C,
    degree: u32,
    instance: Vec<Vec<Fr>>,
    proving_key: ProvingKey<G1Affine>,
) -> Vec<u8> {
    let general_params = get_general_params(degree);
    let verifier_params: ParamsVerifierKZG<Bn256> = general_params.verifier_params().clone();

    let mut transcript = PoseidonTranscript::new(Vec::new());

    // change instace to slice
    let instance: Vec<&[Fr]> = instance.iter().map(|v| v.as_slice()).collect();

    log::info!("gen circuit proof");
    create_proof::<KZGCommitmentScheme<Bn256>, ProverSHPLONK<'_, Bn256>, _, _, _, _>(
        &general_params,
        &proving_key,
        &[circuit],
        &[&instance],
        RNG.clone(),
        &mut transcript,
    )
    .expect("proof generation should not fail");
    let proof = transcript.finalize();

    log::info!("verify circuit proof");
    let verifying_key = proving_key.get_vk();
    let mut verifier_transcript = PoseidonTranscript::new(proof.as_slice());
    let strategy = SingleStrategy::new(&general_params);

    verify_proof::<KZGCommitmentScheme<Bn256>, VerifierSHPLONK<'_, Bn256>, _, _, _>(
        &verifier_params,
        verifying_key,
        strategy,
        &[&instance],
        &mut verifier_transcript,
    )
    .expect("failed to verify circuit");

    proof
}

/// Generate a real proof of the RootCircuit with Keccak transcript and Shplonk accumulation
/// scheme.  Verify the proof and return it.  By using the Keccak transcript (via EvmTranscript)
/// the resulting proof is suitable for verification by the EVM.
///
/// NOTE: MockProver Root Circuit with 64 GiB RAM (2023-06-12):
/// - degree=26 -> OOM
/// - degree=25 -> OK (peak ~35 GiB)
fn test_actual_root_circuit<C: Circuit<Fr>>(
    circuit: C,
    degree: u32,
    instance: Vec<Vec<Fr>>,
    proving_key: ProvingKey<G1Affine>,
) -> Vec<u8> {
    let general_params = get_general_params(degree);
    let verifier_params: ParamsVerifierKZG<Bn256> = general_params.verifier_params().clone();

    let mut transcript = EvmTranscript::<_, NativeLoader, _, _>::new(vec![]);

    // change instace to slice
    let instance: Vec<&[Fr]> = instance.iter().map(|v| v.as_slice()).collect();

    log::info!("gen root circuit proof");
    create_proof::<KZGCommitmentScheme<Bn256>, ProverSHPLONK<'_, Bn256>, _, _, _, _>(
        &general_params,
        &proving_key,
        &[circuit],
        &[&instance],
        RNG.clone(),
        &mut transcript,
    )
    .expect("proof generation should not fail");
    let proof = transcript.finalize();

    log::info!("verify root circuit proof");
    let verifying_key = proving_key.get_vk();
    let mut verifier_transcript = EvmTranscript::<_, NativeLoader, _, _>::new(proof.as_slice());
    let strategy = SingleStrategy::new(&general_params);

    verify_proof::<KZGCommitmentScheme<Bn256>, VerifierSHPLONK<'_, Bn256>, _, _, _>(
        &verifier_params,
        verifying_key,
        strategy,
        &[&instance],
        &mut verifier_transcript,
    )
    .expect("failed to verify circuit");

    proof
}

/// Generic implementation for integration tests
pub struct IntegrationTest<C: SubCircuit<Fr> + Circuit<Fr>> {
    name: &'static str,
    degree: u32,
    root_degree: u32,
    key: Option<ProvingKey<G1Affine>>,
    root_key: Option<ProvingKey<G1Affine>>,
    fixed: Option<Vec<Vec<CellValue<Fr>>>>,
    permutation: Option<Assembly>,
    // The RootCircuit changes depending on the underlying circuit, so we keep a copy of its fixed
    // columns and permutation here to have a unique version for each SubCircuit.
    root_fixed: Option<Vec<Vec<CellValue<Fr>>>>,
    root_permutation: Option<Assembly>,
    _marker: PhantomData<C>,
}

impl<C: SubCircuit<Fr> + Circuit<Fr>> IntegrationTest<C> {
    fn new(name: &'static str, degree: u32, root_degree: u32) -> Self {
        Self {
            name,
            degree,
            root_degree,
            key: None,
            root_key: None,
            fixed: None,
            permutation: None,
            root_fixed: None,
            root_permutation: None,
            _marker: PhantomData,
        }
    }

    fn proof_name(&self, block_tag: &str) -> String {
        format!("{}_{}", self.name, block_tag)
    }

    fn get_key(&mut self) -> ProvingKey<G1Affine> {
        match self.key.clone() {
            Some(key) => key,
            None => {
                let (block, chunk) = new_empty_block_chunk();
                let circuit = C::new_from_block(&block, &chunk);
                let general_params = get_general_params(self.degree);

                let verifying_key =
                    keygen_vk(&general_params, &circuit).expect("keygen_vk should not fail");
                let key = keygen_pk(&general_params, verifying_key, &circuit)
                    .expect("keygen_pk should not fail");
                self.key = Some(key.clone());
                key
            }
        }
    }

    fn get_root_key(&mut self) -> ProvingKey<G1Affine> {
        match self.root_key.clone() {
            Some(key) => key,
            None => {
                let params = get_general_params(self.degree);
                let pk = self.get_key();

                let (block, chunk) = new_empty_block_chunk();
                let circuit = C::new_from_block(&block, &chunk);
                let instance = circuit.instance();

                let protocol = compile(
                    &params,
                    pk.get_vk(),
                    Config::kzg().with_num_instance(
                        instance.iter().map(|instance| instance.len()).collect(),
                    ),
                );
                let circuit = RootCircuit::<Bn256, Shplonk<_>>::new(
                    &params,
                    &protocol,
                    Value::unknown(),
                    Value::unknown(),
                    None,
                )
                .unwrap();

                let general_params = get_general_params(self.root_degree);
                let verifying_key =
                    keygen_vk(&general_params, &circuit).expect("keygen_vk should not fail");
                let key = keygen_pk(&general_params, verifying_key, &circuit)
                    .expect("keygen_pk should not fail");
                self.root_key = Some(key.clone());
                key
            }
        }
    }

    fn test_mock(&mut self, circuit: &C, instance: Vec<Vec<Fr>>) {
        let mock_prover = MockProver::<Fr>::run(self.degree, circuit, instance).unwrap();

        self.test_variadic(&mock_prover);

        mock_prover
            .verify_par()
            .expect("mock prover verification failed");
    }

    fn test_variadic(&mut self, mock_prover: &MockProver<Fr>) {
        let fixed = mock_prover.fixed();

        if let Some(prev_fixed) = self.fixed.clone() {
            assert!(
                fixed.eq(&prev_fixed),
                "circuit fixed columns are not constant for different witnesses"
            );
        } else {
            self.fixed = Some(fixed.clone());
        }

        let permutation = mock_prover.permutation();

        if let Some(prev_permutation) = self.permutation.clone() {
            assert!(
                permutation.eq(&prev_permutation),
                "circuit permutations are not constant for different witnesses"
            );
        } else {
            self.permutation = Some(permutation.clone());
        }
    }

    fn test_root_variadic(&mut self, mock_prover: &MockProver<Fr>) {
        let fixed = mock_prover.fixed();

        match self.root_fixed.clone() {
            Some(prev_fixed) => {
                assert!(
                    fixed.eq(&prev_fixed),
                    "root circuit fixed columns are not constant for different witnesses"
                );
            }
            None => {
                self.root_fixed = Some(fixed.clone());
            }
        };

        let permutation = mock_prover.permutation();

        if let Some(prev_permutation) = self.root_permutation.clone() {
            assert!(
                permutation.eq(&prev_permutation),
                "root circuit permutations are not constant for different witnesses"
            );
        } else {
            self.root_permutation = Some(permutation.clone());
        }
    }

    /// Run integration test at a block identified by a tag.
    pub async fn test_at_block_tag(&mut self, block_tag: &str, root: bool, actual: bool) {
        let block_num = *GEN_DATA.blocks.get(block_tag).unwrap();
        let proof_name = self.proof_name(block_tag);
        let (builder, _) = gen_inputs(block_num).await;

        log::info!(
            "test {} circuit{}, {} prover, block: #{} - {}",
            self.name,
            if root {
                " with aggregation (root circuit)"
            } else {
                ""
            },
            if actual { "real" } else { "mock" },
            block_num,
            block_tag,
        );
        let mut block = block_convert(&builder).unwrap();
        let chunk = chunk_convert(&builder, 0).unwrap();
        block.randomness = Fr::from(TEST_MOCK_RANDOMNESS);
        let circuit = C::new_from_block(&block, &chunk);
        let instance = circuit.instance();

        #[allow(clippy::collapsible_else_if)]
        if root {
            let params = get_general_params(self.degree);
            let pk = self.get_key();
            let protocol = compile(
                &params,
                pk.get_vk(),
                Config::kzg()
                    .with_num_instance(instance.iter().map(|instance| instance.len()).collect()),
            );

            // get chronological_rwtable and byaddr_rwtable columns index
            let mut cs = ConstraintSystem::<<Bn256 as Engine>::Scalar>::default();
            let config = SuperCircuit::configure(&mut cs);
            let rwtable_columns = config.get_rwtable_columns();

            let proof = {
                let mut proof_cache = PROOF_CACHE.lock().await;
                if let Some(proof) = proof_cache.get(&proof_name) {
                    log::info!("using circuit cached proof");
                    proof.clone()
                } else {
                    let key = self.get_key();
                    log::info!("circuit proof generation (no proof in the cache)");
                    let proof = test_actual_circuit(circuit, self.degree, instance.clone(), key);
                    proof_cache.insert(proof_name, proof.clone());
                    proof
                }
            };

            log::info!("root circuit new");
            let user_challenge = &UserChallenge {
                column_indexes: rwtable_columns,
                num_challenges: 2, // alpha, gamma
            };
            let root_circuit = RootCircuit::<Bn256, Shplonk<_>>::new(
                &params,
                &protocol,
                Value::known(&instance),
                Value::known(&proof),
                Some(user_challenge),
            )
            .unwrap();

            if actual {
                let root_key = self.get_root_key();
                let instance = root_circuit.instance();
                log::info!("root circuit proof generation");
                test_actual_root_circuit(root_circuit, self.root_degree, instance, root_key);
            } else {
                log::info!("root circuit mock prover verification");
                // Mock
                let mock_prover =
                    MockProver::<Fr>::run(self.root_degree, &root_circuit, root_circuit.instance())
                        .unwrap();
                self.test_root_variadic(&mock_prover);
                mock_prover
                    .verify_par()
                    .expect("mock prover verification failed");
            }
        } else {
            if actual {
                let key = self.get_key();
                log::info!("circuit proof generation");
                let proof = test_actual_circuit(circuit, self.degree, instance, key);
                let mut proof_cache = PROOF_CACHE.lock().await;
                proof_cache.insert(proof_name, proof);
            } else {
                log::info!("circuit mock prover verification");
                self.test_mock(&circuit, instance);
            }
        }
    }
}

fn new_empty_block_chunk() -> (Block<Fr>, Chunk<Fr>) {
    let block: GethData = TestContext::<0, 0>::new(None, |_| {}, |_, _| {}, |b, _| b)
        .unwrap()
        .into();
    let builder = BlockData::new_from_geth_data_with_params(block.clone(), CIRCUITS_PARAMS)
        .new_circuit_input_builder()
        .handle_block(&block.eth_block, &block.geth_traces)
        .unwrap();
    (
        block_convert(&builder).unwrap(),
        chunk_convert(&builder, 0).unwrap(),
    )
}

fn get_general_params(degree: u32) -> ParamsKZG<Bn256> {
    let mut map = GEN_PARAMS.lock().unwrap();
    match map.get(&degree) {
        Some(params) => params.clone(),
        None => {
            let params = ParamsKZG::<Bn256>::setup(degree, RNG.clone());
            map.insert(degree, params.clone());
            params
        }
    }
}

/// returns gen_inputs for a block number
async fn gen_inputs(
    block_num: u64,
) -> (
    CircuitInputBuilder<FixedCParams>,
    eth_types::Block<eth_types::Transaction>,
) {
    let cli = get_client();
    let cli = BuilderClient::new(cli, CIRCUITS_PARAMS).await.unwrap();

    cli.gen_inputs(block_num).await.unwrap()
}
