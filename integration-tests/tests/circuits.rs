#![cfg(feature = "circuits")]

use bus_mapping::circuit_input_builder::{BuilderClient, CircuitsParams};
use bus_mapping::operation::OperationContainer;
use eth_types::geth_types;
use halo2_proofs::plonk::{
    create_proof, keygen_pk, keygen_vk, verify_proof, ProvingKey, VerifyingKey,
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
use integration_tests::{get_client, log_init, GenDataOutput, CHAIN_ID};
use lazy_static::lazy_static;
use log::trace;
use paste::paste;
use rand_chacha::rand_core::SeedableRng;
use rand_chacha::ChaCha20Rng;
use rand_xorshift::XorShiftRng;
use std::marker::PhantomData;
use zkevm_circuits::bytecode_circuit::dev::test_bytecode_circuit;
use zkevm_circuits::copy_circuit::dev::test_copy_circuit;
use zkevm_circuits::evm_circuit::witness::RwMap;
use zkevm_circuits::evm_circuit::{test::run_test_circuit, witness::block_convert};
use zkevm_circuits::state_circuit::StateCircuit;
use zkevm_circuits::tx_circuit::{sign_verify::SignVerifyChip, Secp256k1Affine, TxCircuit};

lazy_static! {
    pub static ref GEN_DATA: GenDataOutput = GenDataOutput::load();
}

async fn test_evm_circuit_block(block_num: u64) {
    log::info!("test evm circuit, block number: {}", block_num);
    let cli = get_client();
    let cli = BuilderClient::new(cli, CircuitsParams::default())
        .await
        .unwrap();
    let (builder, _) = cli.gen_inputs(block_num).await.unwrap();

    let block = block_convert(&builder.block, &builder.code_db);
    run_test_circuit(block).expect("evm_circuit verification failed");
}

async fn test_state_circuit_block_gen_circuit(
    block_num: u64,
    rng: &mut XorShiftRng,
    degree: u32,
) -> (
    StateCircuit<Fr>,
    ParamsKZG<Bn256>,
    ParamsVerifierKZG<Bn256>,
    ProvingKey<G1Affine>,
    Blake2bWrite<Vec<u8>, G1Affine, Challenge255<G1Affine>>,
    Vec<Vec<Fr>>,
) {
    let cli = get_client();
    let cli = BuilderClient::new(cli, CircuitsParams::default())
        .await
        .unwrap();
    let (builder, _) = cli.gen_inputs(block_num).await.unwrap();

    // Generate state proof
    let stack_ops = builder.block.container.sorted_stack();
    trace!("stack_ops: {:#?}", stack_ops);
    let memory_ops = builder.block.container.sorted_memory();
    trace!("memory_ops: {:#?}", memory_ops);
    let storage_ops = builder.block.container.sorted_storage();
    trace!("storage_ops: {:#?}", storage_ops);

    let rw_map = RwMap::from(&OperationContainer {
        memory: memory_ops,
        stack: stack_ops,
        storage: storage_ops,
        ..Default::default()
    });

    let randomness = Fr::from(0xcafeu64);
    let circuit = StateCircuit::<Fr>::new(randomness, rw_map, 1 << 16);
    // let power_of_randomness = circuit.instance();

    let general_params = ParamsKZG::<Bn256>::setup(degree, rng);
    let verifier_params: ParamsVerifierKZG<Bn256> = general_params.verifier_params().clone();

    // Initialize the proving key
    let verifying_key = keygen_vk(&general_params, &circuit).expect("keygen_vk should not fail");
    let proving_key =
        keygen_pk(&general_params, verifying_key, &circuit).expect("keygen_pk should not fail");

    // Create a proof
    let transcript = Blake2bWrite::<_, G1Affine, Challenge255<_>>::init(vec![]);
    let instance = circuit.instance();

    (
        circuit,
        general_params,
        verifier_params,
        proving_key,
        transcript,
        instance,
    )
}

fn test_state_circuit_block_proof(
    rng: &XorShiftRng,
    circuit: StateCircuit<Fr>,
    general_params: &ParamsKZG<Bn256>,
    proving_key: &ProvingKey<G1Affine>,
    mut transcript: Blake2bWrite<Vec<u8>, G1Affine, Challenge255<G1Affine>>,
    instance: &Vec<Vec<Fr>>,
) -> Vec<u8> {
    let instances: Vec<&[Fr]> = (*instance).iter().map(|v| v.as_slice()).collect();

    create_proof::<
        KZGCommitmentScheme<Bn256>,
        ProverSHPLONK<'_, Bn256>,
        Challenge255<G1Affine>,
        XorShiftRng,
        Blake2bWrite<Vec<u8>, G1Affine, Challenge255<G1Affine>>,
        StateCircuit<Fr>,
    >(
        general_params,
        proving_key,
        &[circuit],
        &[&instances],
        rng.clone(),
        &mut transcript,
    )
    .expect("proof generation should not fail");

    transcript.finalize()
}

fn test_state_circuit_block_verify(
    general_params: &ParamsKZG<Bn256>,
    verifier_params: &ParamsKZG<Bn256>,
    verifying_key: &VerifyingKey<G1Affine>,
    instance: &Vec<Vec<Fr>>,
    proof: &[u8],
) {
    let instances: Vec<&[Fr]> = (*instance).iter().map(|v| v.as_slice()).collect();

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
        &[&instances],
        &mut verifier_transcript,
    )
    .expect("failed to verify bench circuit");
}

async fn test_state_circuit_block(block_num: u64) {
    log::info!("test state circuit, block number: {}", block_num);

    // Initialize the polynomial commitment parameters
    let mut rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);

    const DEGREE: u32 = 17;

    let (circuit, general_params, verifier_params, proving_key, transcript, instance) =
        test_state_circuit_block_gen_circuit(block_num, &mut rng, DEGREE).await;

    let mock_prover = MockProver::<Fr>::run(DEGREE, &circuit, instance.clone()).unwrap();
    mock_prover
        .verify()
        .expect("state_circuit verification failed");

    let proof = test_state_circuit_block_proof(
        &rng,
        circuit,
        &general_params,
        &proving_key,
        transcript,
        &instance,
    );

    let vk = proving_key.get_vk();
    test_state_circuit_block_verify(&general_params, &verifier_params, vk, &instance, &proof);
}

async fn test_tx_circuit_block(block_num: u64) {
    const DEGREE: u32 = 20;

    log::info!("test tx circuit, block number: {}", block_num);
    let cli = get_client();
    let cli = BuilderClient::new(cli, CircuitsParams::default())
        .await
        .unwrap();

    let (_, eth_block) = cli.gen_inputs(block_num).await.unwrap();
    let txs: Vec<_> = eth_block
        .transactions
        .iter()
        .map(geth_types::Transaction::from)
        .collect();

    let mut rng = ChaCha20Rng::seed_from_u64(2);
    let aux_generator = <Secp256k1Affine as CurveAffine>::CurveExt::random(&mut rng).to_affine();

    let circuit = TxCircuit::<Fr, 4, { 4 * (4 + 32 + 32) }> {
        sign_verify: SignVerifyChip {
            aux_generator,
            window_size: 2,
            _marker: PhantomData,
        },
        txs,
        chain_id: CHAIN_ID,
    };

    let prover = MockProver::run(DEGREE, &circuit, vec![vec![]]).unwrap();

    prover.verify().expect("tx_circuit verification failed");
}

pub async fn test_bytecode_circuit_block(block_num: u64) {
    const DEGREE: u32 = 16;

    log::info!("test bytecode circuit, block number: {}", block_num);
    let cli = get_client();
    let cli = BuilderClient::new(cli, CircuitsParams::default())
        .await
        .unwrap();
    let (builder, _) = cli.gen_inputs(block_num).await.unwrap();
    let bytecodes: Vec<Vec<u8>> = builder.code_db.0.values().cloned().collect();

    test_bytecode_circuit::<Fr>(DEGREE, bytecodes);
}

pub async fn test_copy_circuit_block(block_num: u64) {
    const DEGREE: u32 = 16;

    log::info!("test copy circuit, block number: {}", block_num);
    let cli = get_client();
    let cli = BuilderClient::new(cli, CircuitsParams::default())
        .await
        .unwrap();
    let (builder, _) = cli.gen_inputs(block_num).await.unwrap();
    let block = block_convert(&builder.block, &builder.code_db);

    assert!(test_copy_circuit(DEGREE, block).is_ok());
}

macro_rules! declare_tests {
    ($name:ident, $block_tag:expr) => {
        paste! {
            #[tokio::test]
            async fn [<serial_test_evm_ $name>]() {
                log_init();
                let block_num = GEN_DATA.blocks.get($block_tag).unwrap();
                test_evm_circuit_block(*block_num).await;
            }

            #[tokio::test]
            async fn [<serial_test_state_ $name>]() {
                log_init();
                let block_num = GEN_DATA.blocks.get($block_tag).unwrap();
                test_state_circuit_block(*block_num).await;
            }

            #[tokio::test]
            async fn [<serial_test_tx_ $name>]() {
                log_init();
                let block_num = GEN_DATA.blocks.get($block_tag).unwrap();
                test_tx_circuit_block(*block_num).await;
            }

            #[tokio::test]
            async fn [<serial_test_bytecode_ $name>]() {
                log_init();
                let block_num = GEN_DATA.blocks.get($block_tag).unwrap();
                test_bytecode_circuit_block(*block_num).await;
            }

            #[tokio::test]
            async fn [<serial_test_copy_ $name>]() {
                log_init();
                let block_num = GEN_DATA.blocks.get($block_tag).unwrap();
                test_copy_circuit_block(*block_num).await;
            }

        }
    };
}

/*
declare_tests!(
    test_evm_circuit_block_transfer_0,
    test_state_circuit_block_transfer_0,
    "Transfer 0"
);
declare_tests!(
    test_evm_circuit_deploy_greeter,
    test_state_circuit_deploy_greeter,
    "Deploy Greeter"
);
declare_tests!(
    test_evm_circuit_multiple_transfers_0,
    test_state_circuit_multiple_transfers_0,
    "Multiple transfers 0"
);
*/
declare_tests!(
    circuit_erc20_openzeppelin_transfer_fail,
    "ERC20 OpenZeppelin transfer failed"
);
declare_tests!(
    circuit_erc20_openzeppelin_transfer_succeed,
    "ERC20 OpenZeppelin transfer successful"
);
declare_tests!(
    circuit_multiple_erc20_openzeppelin_transfers,
    "Multiple ERC20 OpenZeppelin transfers"
);
