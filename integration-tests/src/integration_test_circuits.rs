use crate::{get_client, GenDataOutput, CHAIN_ID};
use bus_mapping::circuit_input_builder::{BuilderClient, CircuitInputBuilder, CircuitsParams};
use eth_types::geth_types;
use halo2_proofs::plonk::{
    create_proof, keygen_pk, keygen_vk, verify_proof, Circuit, ProvingKey, VerifyingKey,
};
use halo2_proofs::poly::commitment::ParamsProver;
use halo2_proofs::poly::kzg::commitment::{KZGCommitmentScheme, ParamsKZG, ParamsVerifierKZG};
use halo2_proofs::poly::kzg::multiopen::{ProverSHPLONK, VerifierSHPLONK};
use halo2_proofs::poly::kzg::strategy::SingleStrategy;
use halo2_proofs::{
    arithmetic::CurveAffine,
    dev::MockProver,
    halo2curves::{
        bn256::Fr,
        group::{Curve, Group},
    },
};
use halo2_proofs::{
    halo2curves::bn256::{Bn256, G1Affine},
    transcript::{
        Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
    },
};
use lazy_static::lazy_static;
use log::trace;
use rand_chacha::rand_core::SeedableRng;
use rand_chacha::ChaCha20Rng;
use rand_core::RngCore;
use rand_xorshift::XorShiftRng;
use std::collections::HashMap;
use std::marker::PhantomData;
use std::sync::Mutex;
use zkevm_circuits::bytecode_circuit::bytecode_unroller::unroll;
use zkevm_circuits::bytecode_circuit::dev::BytecodeCircuitTester;
use zkevm_circuits::copy_circuit::dev::CopyCircuitTester;
use zkevm_circuits::evm_circuit::test::{get_test_degree, get_test_instance};
use zkevm_circuits::evm_circuit::witness::RwMap;
use zkevm_circuits::evm_circuit::{test::get_test_cicuit_from_block, witness::block_convert};
use zkevm_circuits::state_circuit::StateCircuit;
use zkevm_circuits::super_circuit::SuperCircuit;
use zkevm_circuits::tx_circuit::{sign_verify::SignVerifyChip, Secp256k1Affine, TxCircuit};

const CIRCUITS_PARAMS: CircuitsParams = CircuitsParams {
    max_rws: 16384,
    max_txs: 4,
    keccak_padding: None,
};

const STATE_CIRCUIT_DEGREE: u32 = 17;
const TX_CIRCUIT_DEGREE: u32 = 20;
const BYTECODE_CIRCUIT_DEGREE: u32 = 16;
const COPY_CIRCUIT_DEGREE: u32 = 16;

lazy_static! {
    /// Data generation.
    pub static ref GEN_DATA: GenDataOutput = GenDataOutput::load();
    static ref RNG: XorShiftRng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);
    static ref GEN_PARAMS: Mutex<HashMap<u32, ParamsKZG<Bn256>>> = Mutex::new(HashMap::new());
    static ref STATE_CIRCUIT_KEY: ProvingKey<G1Affine> = {
        let circuit = StateCircuit::<Fr>::default();
        let general_params = get_general_params(STATE_CIRCUIT_DEGREE);

        let verifying_key = keygen_vk(&general_params, &circuit).expect("keygen_vk should not fail");
        keygen_pk(&general_params, verifying_key, &circuit).expect("keygen_pk should not fail")
    };
    static ref TX_CIRCUIT_KEY: ProvingKey<G1Affine> = {
        let circuit = TxCircuit::<Fr, 4, { 4 * (4 + 32 + 32) }>::default();
        let general_params = get_general_params(TX_CIRCUIT_DEGREE);

        let verifying_key = keygen_vk(&general_params, &circuit).expect("keygen_vk should not fail");
        keygen_pk(&general_params, verifying_key, &circuit).expect("keygen_pk should not fail")
    };

    static ref BYTECODE_CIRCUIT_KEY: ProvingKey<G1Affine> = {
        let circuit = BytecodeCircuitTester::<Fr>::default();
        let general_params = get_general_params(BYTECODE_CIRCUIT_DEGREE);

        let verifying_key = keygen_vk(&general_params, &circuit).expect("keygen_vk should not fail");
        keygen_pk(&general_params, verifying_key, &circuit).expect("keygen_pk should not fail")
    };
    static ref COPY_CIRCUIT_KEY: ProvingKey<G1Affine> = {
        let circuit = CopyCircuitTester::<Fr>::default();
        let general_params = get_general_params(COPY_CIRCUIT_DEGREE);

        let verifying_key = keygen_vk(&general_params, &circuit).expect("keygen_vk should not fail");
        keygen_pk(&general_params, verifying_key, &circuit).expect("keygen_pk should not fail")
    };
}

fn get_general_params(degree: u32) -> ParamsKZG<Bn256> {
    match GEN_PARAMS.lock().unwrap().get(&degree) {
        Some(params) => params.clone(),
        None => {
            let params = ParamsKZG::<Bn256>::setup(degree, RNG.clone());
            GEN_PARAMS.lock().unwrap().insert(degree, params.clone());
            params
        }
    }
}

async fn gen_inputs(
    block_num: u64,
) -> (
    CircuitInputBuilder,
    eth_types::Block<eth_types::Transaction>,
) {
    let cli = get_client();
    let cli = BuilderClient::new(cli, CIRCUITS_PARAMS).await.unwrap();

    cli.gen_inputs(block_num).await.unwrap()
}

fn test_actual<C: Circuit<Fr>>(
    degree: u32,
    circuit: C,
    instance: Vec<Vec<Fr>>,
    proving_key: Option<ProvingKey<G1Affine>>,
) {
    fn test_gen_proof<C: Circuit<Fr>, R: RngCore>(
        rng: R,
        circuit: C,
        general_params: &ParamsKZG<Bn256>,
        proving_key: &ProvingKey<G1Affine>,
        mut transcript: Blake2bWrite<Vec<u8>, G1Affine, Challenge255<G1Affine>>,
        instances: &[&[Fr]],
    ) -> Vec<u8> {
        create_proof::<
            KZGCommitmentScheme<Bn256>,
            ProverSHPLONK<'_, Bn256>,
            Challenge255<G1Affine>,
            R,
            Blake2bWrite<Vec<u8>, G1Affine, Challenge255<G1Affine>>,
            C,
        >(
            general_params,
            proving_key,
            &[circuit],
            &[instances],
            rng,
            &mut transcript,
        )
        .expect("proof generation should not fail");

        transcript.finalize()
    }

    fn test_verify(
        general_params: &ParamsKZG<Bn256>,
        verifier_params: &ParamsKZG<Bn256>,
        verifying_key: &VerifyingKey<G1Affine>,
        proof: &[u8],
        instances: &[&[Fr]],
    ) {
        let mut verifier_transcript = Blake2bRead::<_, G1Affine, Challenge255<_>>::init(proof);
        let strategy = SingleStrategy::new(general_params);

        verify_proof::<
            KZGCommitmentScheme<Bn256>,
            VerifierSHPLONK<'_, Bn256>,
            Challenge255<G1Affine>,
            Blake2bRead<&[u8], G1Affine, Challenge255<G1Affine>>,
            SingleStrategy<'_, Bn256>,
        >(
            verifier_params,
            verifying_key,
            strategy,
            &[instances],
            &mut verifier_transcript,
        )
        .expect("failed to verify bench circuit");
    }

    let general_params = get_general_params(degree);
    let verifier_params: ParamsVerifierKZG<Bn256> = general_params.verifier_params().clone();

    let proving_key = match proving_key {
        Some(pk) => pk,
        None => {
            let verifying_key =
                keygen_vk(&general_params, &circuit).expect("keygen_vk should not fail");
            keygen_pk(&general_params, verifying_key, &circuit).expect("keygen_pk should not fail")
        }
    };

    let transcript = Blake2bWrite::<_, G1Affine, Challenge255<_>>::init(vec![]);

    // change instace to slice
    let instance: Vec<&[Fr]> = instance.iter().map(|v| v.as_slice()).collect();

    let proof = test_gen_proof(
        RNG.clone(),
        circuit,
        &general_params,
        &proving_key,
        transcript,
        &instance,
    );

    let verifying_key = proving_key.get_vk();
    test_verify(
        &general_params,
        &verifier_params,
        verifying_key,
        &proof,
        &instance,
    );
}

fn test_mock<C: Circuit<Fr>>(degree: u32, circuit: &C, instance: Vec<Vec<Fr>>) {
    let mock_prover = MockProver::<Fr>::run(degree, circuit, instance).unwrap();
    mock_prover
        .verify_par()
        .expect("mock prover verification failed");
}

/// Integration test for evm circuit.
pub async fn test_evm_circuit_block(block_num: u64, actual: bool) {
    log::info!("test evm circuit, block number: {}", block_num);
    let (builder, _) = gen_inputs(block_num).await;

    let block = block_convert(&builder.block, &builder.code_db);

    let degree = get_test_degree(&block);
    let instance = get_test_instance(&block);
    let circuit = get_test_cicuit_from_block(block);

    test_mock(degree, &circuit, instance.clone());

    if actual {
        test_actual(degree, circuit, instance, None);
    }
}

/// Integration test for state circuit.
pub async fn test_state_circuit_block(block_num: u64, actual: bool) {
    log::info!("test state circuit, block number: {}", block_num);

    let (builder, _) = gen_inputs(block_num).await;

    // Generate state proof
    // log via trace some of the container ops for debugging purposes
    let stack_ops = builder.block.container.sorted_stack();
    trace!("stack_ops: {:#?}", stack_ops);
    let memory_ops = builder.block.container.sorted_memory();
    trace!("memory_ops: {:#?}", memory_ops);
    let storage_ops = builder.block.container.sorted_storage();
    trace!("storage_ops: {:#?}", storage_ops);

    // TODO: use rw_map from block
    // let rw_map = RwMap::from(&builder.block.container);
    let rw_map = RwMap::default();

    let circuit = StateCircuit::<Fr>::new(rw_map, 1 << 16);
    let instance = circuit.instance();

    test_mock(STATE_CIRCUIT_DEGREE, &circuit, instance.clone());

    if actual {
        test_actual(
            STATE_CIRCUIT_DEGREE,
            circuit,
            instance,
            Some((*STATE_CIRCUIT_KEY).clone()),
        );
    }
}

/// Integration test for tx circuit.
pub async fn test_tx_circuit_block(block_num: u64, actual: bool) {
    log::info!("test tx circuit, block number: {}", block_num);

    let (_, eth_block) = gen_inputs(block_num).await;
    let txs: Vec<_> = eth_block
        .transactions
        .iter()
        .map(geth_types::Transaction::from)
        .collect();

    let aux_generator = <Secp256k1Affine as CurveAffine>::CurveExt::random(RNG.clone()).to_affine();

    let circuit = TxCircuit::<Fr, 4, { 4 * (4 + 32 + 32) }> {
        sign_verify: SignVerifyChip {
            aux_generator,
            window_size: 2,
            _marker: PhantomData,
        },
        txs,
        chain_id: CHAIN_ID,
    };

    test_mock(TX_CIRCUIT_DEGREE, &circuit, vec![vec![]]);

    if actual {
        test_actual(
            TX_CIRCUIT_DEGREE,
            circuit,
            vec![vec![]],
            Some((*TX_CIRCUIT_KEY).clone()),
        );
    }
}

/// Integration test for bytecode circuit.
pub async fn test_bytecode_circuit_block(block_num: u64, actual: bool) {
    log::info!("test bytecode circuit, block number: {}", block_num);
    let (builder, _) = gen_inputs(block_num).await;

    let bytecodes: Vec<Vec<u8>> = builder.code_db.0.values().cloned().collect();
    let unrolled: Vec<_> = bytecodes.iter().map(|b| unroll::<Fr>(b.clone())).collect();

    let circuit = BytecodeCircuitTester::<Fr>::new(unrolled, 2usize.pow(BYTECODE_CIRCUIT_DEGREE));

    test_mock(BYTECODE_CIRCUIT_DEGREE, &circuit, Vec::new());

    if actual {
        test_actual(
            BYTECODE_CIRCUIT_DEGREE,
            circuit,
            Vec::new(),
            Some((*BYTECODE_CIRCUIT_KEY).clone()),
        );
    }
}

/// Integration test for copy circuit.
pub async fn test_copy_circuit_block(block_num: u64, actual: bool) {
    log::info!("test copy circuit, block number: {}", block_num);
    let (builder, _) = gen_inputs(block_num).await;
    let block = block_convert(&builder.block, &builder.code_db);

    let randomness = CopyCircuitTester::<Fr>::get_randomness();
    let circuit = CopyCircuitTester::<Fr>::new(block, randomness);

    let num_rows = 1 << COPY_CIRCUIT_DEGREE;
    const NUM_BLINDING_ROWS: usize = 7 - 1;
    let instance = vec![vec![randomness; num_rows - NUM_BLINDING_ROWS]];

    test_mock(COPY_CIRCUIT_DEGREE, &circuit, instance.clone());

    if actual {
        test_actual(
            COPY_CIRCUIT_DEGREE,
            circuit,
            instance,
            Some((*COPY_CIRCUIT_KEY).clone()),
        );
    }
}

/// Integration test for super circuit.
pub async fn test_super_circuit_block(block_num: u64) {
    const MAX_TXS: usize = 4;
    const MAX_CALLDATA: usize = 512;
    const MAX_RWS: usize = 5888;

    log::info!("test super circuit, block number: {}", block_num);
    let cli = get_client();
    let cli = BuilderClient::new(
        cli,
        CircuitsParams {
            max_rws: MAX_RWS,
            max_txs: MAX_TXS,
            keccak_padding: None,
        },
    )
    .await
    .unwrap();
    let (builder, eth_block) = cli.gen_inputs(block_num).await.unwrap();
    let (k, circuit, instance) =
        SuperCircuit::<_, MAX_TXS, MAX_CALLDATA, MAX_RWS>::build_from_circuit_input_builder(
            builder,
            eth_block,
            &mut ChaCha20Rng::seed_from_u64(2),
        )
        .unwrap();
    // TODO: add actual prover
    let prover = MockProver::run(k, &circuit, instance).unwrap();
    let res = prover.verify_par();
    if let Err(err) = res {
        eprintln!("Verification failures:");
        eprintln!("{:#?}", err);
        panic!("Failed verification");
    }
}
