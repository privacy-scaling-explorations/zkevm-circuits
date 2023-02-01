//! PI circuit benchmarks
use ark_std::{end_timer, start_timer};
use eth_types::geth_types::GethData;
use eth_types::{address, bytecode, Word, U256};
use ethers_signers::LocalWallet;
use ethers_signers::Signer;
use halo2_proofs::arithmetic::Field;
use halo2_proofs::plonk::{create_proof, keygen_pk, keygen_vk, verify_proof};
use halo2_proofs::poly::kzg::commitment::{KZGCommitmentScheme, ParamsKZG, ParamsVerifierKZG};
use halo2_proofs::poly::kzg::multiopen::{ProverSHPLONK, VerifierSHPLONK};
use halo2_proofs::poly::kzg::strategy::SingleStrategy;
use halo2_proofs::{
    halo2curves::bn256::{Bn256, Fr, G1Affine},
    poly::commitment::ParamsProver,
    transcript::{
        Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
    },
};
use mock::{TestContext, MOCK_CHAIN_ID};
use rand::SeedableRng;
use rand_chacha::{ChaCha20Rng, ChaChaRng};
use rand_xorshift::XorShiftRng;
use std::collections::HashMap;
use std::env::var;
use std::io::Read;
use zkevm_circuits::pi_circuit::{PiCircuit, PiTestCircuit, PublicData};
use zkevm_circuits::super_circuit::SuperCircuit;
use zkevm_circuits::test_util::rand_tx;
use zkevm_circuits::util::SubCircuit;

#[test]
fn bench_super_circuit_prover() {
    let degree: u32 = 20;

    let mut rng = ChaChaRng::seed_from_u64(2);

    let chain_id = (*MOCK_CHAIN_ID).as_u64();

    let bytecode = bytecode! {
        STOP
    };

    let wallet_a = LocalWallet::new(&mut rng).with_chain_id(chain_id);

    let addr_a = wallet_a.address();
    let addr_b = address!("0x000000000000000000000000000000000000BBBB");

    let mut wallets = HashMap::new();
    wallets.insert(wallet_a.address(), wallet_a);

    let mut block: GethData = TestContext::<2, 1>::new(
        None,
        |accs| {
            accs[0]
                .address(addr_b)
                .balance(Word::from(1u64 << 20))
                .code(bytecode);
            accs[1].address(addr_a).balance(Word::from(1u64 << 20));
        },
        |mut txs, accs| {
            txs[0]
                .from(accs[1].address)
                .to(accs[0].address)
                .gas(Word::from(1_000_000u64));
        },
        |block, _tx| block.number(0xcafeu64),
    )
    .unwrap()
    .into();

    block.sign(&wallets);

    type TestSuperCircuit = SuperCircuit::<Fr, 4, 32, 512>;
    let (_, circuit, instance, _) = TestSuperCircuit::build(block).unwrap();
    let instance_refs: Vec<&[Fr]> = instance.iter().map(|v| &v[..]).collect();

    // Bench setup generation
    let setup_message = format!("Setup generation with degree = {}", degree);
    let start1 = start_timer!(|| setup_message);
    let general_params = ParamsKZG::<Bn256>::setup(degree, &mut rng);
    let verifier_params: ParamsVerifierKZG<Bn256> = general_params.verifier_params().clone();
    end_timer!(start1);

    // Initialize the proving key
    let vk = keygen_vk(&general_params, &circuit).expect("keygen_vk should not fail");
    let pk = keygen_pk(&general_params, vk, &circuit).expect("keygen_pk should not fail");
    // Create a proof
    let mut transcript = Blake2bWrite::<_, G1Affine, Challenge255<_>>::init(vec![]);

    // Bench proof generation time
    let proof_message = format!("SuperCircuit Proof generation with degree = {}", degree);
    let start2 = start_timer!(|| proof_message);
    create_proof::<
        KZGCommitmentScheme<Bn256>,
        ProverSHPLONK<'_, Bn256>,
        Challenge255<G1Affine>,
        ChaChaRng,
        Blake2bWrite<Vec<u8>, G1Affine, Challenge255<G1Affine>>,
        TestSuperCircuit,
    >(
        &general_params,
        &pk,
        &[circuit.clone()],
        &[&instance_refs],
        rng,
        &mut transcript,
    )
    .expect("proof generation should not fail");
    let proof = transcript.finalize();
    end_timer!(start2);

    // Bench verification time
    let start3 = start_timer!(|| "SuperCircuit Proof verification");
    let mut verifier_transcript = Blake2bRead::<_, G1Affine, Challenge255<_>>::init(&proof[..]);
    let strategy = SingleStrategy::new(&general_params);

    verify_proof::<
        KZGCommitmentScheme<Bn256>,
        VerifierSHPLONK<'_, Bn256>,
        Challenge255<G1Affine>,
        Blake2bRead<&[u8], G1Affine, Challenge255<G1Affine>>,
        SingleStrategy<'_, Bn256>,
    >(
        &verifier_params,
        pk.get_vk(),
        strategy,
        &[&instance_refs],
        &mut verifier_transcript,
    )
    .expect("failed to verify bench circuit");
    end_timer!(start3);

    let deployment_code = gen_evm_verifier(
        &general_params,
        pk.get_vk(),
        SuperCircuit::<_, 1, 32, 512>::num_instance(),
    );

    evm_verify(deployment_code, circuit.instances(), proof.clone());
}

// use eth_types::Field;
use halo2_proofs::{
    dev::MockProver,
    halo2curves::bn256::Fq,
    plonk::{Circuit, ProvingKey, VerifyingKey},
    poly::commitment::Params,
    poly::kzg::{
        multiopen::{ProverGWC, VerifierGWC},
        strategy::AccumulatorStrategy,
    },
    poly::VerificationStrategy,
};
use itertools::Itertools;
use rand::rngs::OsRng;
use snark_verifier::{
    loader::evm::{self, encode_calldata, Address, EvmLoader, ExecutorBuilder},
    pcs::kzg::{Gwc19, KzgAs},
    system::halo2::{compile, transcript::evm::EvmTranscript, Config},
    verifier::{self, SnarkVerifier},
};
use std::fs::{self, File};
use std::{io::Cursor, io::Write, rc::Rc, time::Instant};

type PlonkVerifier = verifier::plonk::PlonkVerifier<KzgAs<Bn256, Gwc19>>;

pub fn write_params(degree: usize, params: &ParamsKZG<Bn256>) -> Result<(), std::io::Error> {
    let dir = "./generated";
    fs::create_dir_all(dir).unwrap_or_else(|_| panic!("create {}", dir));
    let path = format!("{}/srs-{}", dir, degree);
    let mut file = fs::File::create(&path).unwrap_or_else(|_| panic!("create {}", &path));
    params.write(&mut file)
}

pub fn read_params(degree: usize) -> Result<ParamsKZG<Bn256>, std::io::Error> {
    let dir = "./generated";
    let path = format!("{}/srs-{}", dir, degree);
    let mut file = fs::File::open(&path)?;
    ParamsKZG::<Bn256>::read(&mut file)
}

pub fn get_circuit_params<const D: usize>(degree: usize) -> ParamsKZG<Bn256> {
    let mut params = if let Ok(params) = read_params(degree) {
        params
    } else {
        let params = ParamsKZG::<Bn256>::setup(degree as u32, OsRng);
        write_params(degree, &params).expect("write srs ok");
        params
    };

    if D > 0 {
        params.downsize(D as u32);
    }
    params
}

trait InstancesExport {
    fn num_instance() -> Vec<usize>;

    fn instances(&self) -> Vec<Vec<Fr>>;
}

impl<const MAX_TXS: usize, const MAX_CALLDATA: usize, const MAX_RWS: usize> InstancesExport
    for SuperCircuit<Fr, MAX_TXS, MAX_CALLDATA, MAX_RWS>
{
    fn num_instance() -> Vec<usize> {
        vec![5]
    }

    fn instances(&self) -> Vec<Vec<Fr>> {
        self.instance()
    }
}

fn gen_evm_verifier(
    params: &ParamsKZG<Bn256>,
    vk: &VerifyingKey<G1Affine>,
    num_instance: Vec<usize>,
) -> Vec<u8> {
    let protocol = compile(
        params,
        vk,
        Config::kzg().with_num_instance(num_instance.clone()),
    );
    let vk = (params.get_g()[0], params.g2(), params.s_g2()).into();

    let loader = EvmLoader::new::<Fq, Fr>();
    let protocol = protocol.loaded(&loader);
    let mut transcript = EvmTranscript::<_, Rc<EvmLoader>, _, _>::new(&loader);

    let instances = transcript.load_instances(num_instance);
    let proof = PlonkVerifier::read_proof(&vk, &protocol, &instances, &mut transcript).unwrap();
    PlonkVerifier::verify(&vk, &protocol, &instances, &proof).unwrap();

    File::create("./PlonkEvmVerifier-super.sol")
        .expect("PlonkEvmVerifier-super.sol")
        .write_all(&loader.yul_code().as_bytes())
        .expect("PlonkEvmVerifier-super.sol");

    evm::compile_yul(&loader.yul_code())
}

fn evm_verify(deployment_code: Vec<u8>, instances: Vec<Vec<Fr>>, proof: Vec<u8>) {
    let calldata = encode_calldata(&instances, &proof);

    let success = {
        let mut evm = ExecutorBuilder::default()
            .with_gas_limit(u64::MAX.into())
            .build();

        let caller = Address::from_low_u64_be(0xfe);
        let verifier = evm
            .deploy(caller, deployment_code.into(), 0.into())
            .address
            .unwrap();
        let result = evm.call_raw(caller, verifier, calldata.into(), 0.into());

        dbg!(result.gas_used);

        !result.reverted
    };
    assert!(success);
}

fn gen_proof<C: Circuit<Fr>>(
    params: &ParamsKZG<Bn256>,
    pk: &ProvingKey<G1Affine>,
    circuit: C,
    instances: Vec<Vec<Fr>>,
) -> Vec<u8> {
    MockProver::run(params.k(), &circuit, instances.clone())
        .unwrap()
        .assert_satisfied();

    let instances = instances
        .iter()
        .map(|instances| instances.as_slice())
        .collect_vec();
    let proof = {
        let mut transcript = TranscriptWriterBuffer::<_, G1Affine, _>::init(Vec::new());
        create_proof::<KZGCommitmentScheme<Bn256>, ProverGWC<_>, _, _, EvmTranscript<_, _, _, _>, _>(
            params,
            pk,
            &[circuit],
            &[instances.as_slice()],
            OsRng,
            &mut transcript,
        )
        .unwrap();
        transcript.finalize()
    };

    let accept = {
        let mut transcript = TranscriptReadBuffer::<_, G1Affine, _>::init(proof.as_slice());
        VerificationStrategy::<_, VerifierGWC<_>>::finalize(
            verify_proof::<_, VerifierGWC<_>, _, EvmTranscript<_, _, _, _>, _>(
                params.verifier_params(),
                pk.get_vk(),
                AccumulatorStrategy::new(params.verifier_params()),
                &[instances.as_slice()],
                &mut transcript,
            )
            .unwrap(),
        )
    };
    assert!(accept);

    proof
}

use std::path::Path;

fn write_pk(pk_file_path: &Path, pk: &ProvingKey<G1Affine>) -> Result<(), std::io::Error> {
    let dir = pk_file_path.parent().unwrap();
    fs::create_dir_all(dir).expect(format!("create {:?}", dir).as_str());
    let mut file = fs::File::create(&pk_file_path)?;
    pk.write(&mut file)
}

fn read_pk<C: Circuit<Fr>>(
    pk_file_path: &str,
    params: &ParamsKZG<Bn256>,
) -> Result<ProvingKey<G1Affine>, std::io::Error> {
    let mut file = fs::File::open(&pk_file_path)?;
    ProvingKey::<G1Affine>::read::<File, C>(&mut file, params)
}

fn load_circuit_pk<C: Circuit<Fr>>(
    pk_name: &str,
    params: &ParamsKZG<Bn256>,
    circuit: &C,
) -> Result<ProvingKey<G1Affine>, halo2_proofs::plonk::Error> {
    let pk_file_path = Path::new("./generated/keys").join(pk_name);
    if pk_file_path.exists() {
        read_pk::<C>(pk_file_path.to_str().unwrap(), params).map_err(|e| e.into())
    } else {
        let pk = keygen_pk(params, keygen_vk(params, circuit).unwrap(), circuit)?;
        write_pk(pk_file_path.as_path(), &pk)?;
        Ok(pk)
    }
}

#[test]
fn test_query_dir() {
    let dir = Path::new("./");
    let paths = dir.read_dir().unwrap();
    paths.for_each(|path| println!("{}", path.unwrap().file_name().into_string().unwrap()));
}

use bus_mapping::circuit_input_builder::{BuilderClient, CircuitsParams};
use bus_mapping::rpc::GethClient;
use bus_mapping::Error;
use clap::Parser;
use ethers_providers::Http;
use serde::{Deserialize, Serialize};
use std::str::FromStr;
use zkevm_circuits::evm_circuit::witness::block_convert;
use zkevm_circuits::super_circuit::MOCK_RANDOMNESS;
use zkevm_circuits::tx_circuit::PrimeField;

#[derive(Parser, Debug)]
#[clap(version, about)]
pub(crate) struct ProverCmdConfig {
    /// geth_url
    geth_url: String,
    /// block_num
    block_num: u64,
    /// output_file
    output: Option<String>,
}

#[tokio::main]
async fn main() -> Result<(), Error> {
    let config = ProverCmdConfig::parse();
    let provider = Http::from_str(&config.geth_url).expect("Http geth url");
    let geth_client = GethClient::new(provider);
    const MAX_TXS: usize = 10;
    const MAX_CALLDATA: usize = 26288;
    const MAX_RWS: usize = 26288000;
    let circuit_params = CircuitsParams {
        max_rws: 280000,
        max_txs: MAX_TXS,
        max_calldata: MAX_CALLDATA,
        max_bytecode: 24634,
        keccak_padding: None,
    };

    let builder = BuilderClient::new(geth_client, circuit_params.clone()).await?;
    let (builder, eth_block) = builder.gen_inputs(config.block_num).await?;
    let mut block = block_convert(&builder.block, &builder.code_db).unwrap();
    block.randomness = Fr::from(MOCK_RANDOMNESS);
    // let circuit = PiTestCircuit::<Fr, MAX_TXS,
    // MAX_CALLDATA>(PiCircuit::new_from_block(&block));
    assert!(block.txs.len() <= MAX_TXS);

    let (min_k, circuit, instance) =
        SuperCircuit::<_, MAX_TXS, MAX_CALLDATA, MAX_RWS>::build_from_circuit_input_builder(
            &builder,
        )
        .unwrap();

    println!("min_k of super circuit is {}", min_k);
    let degree = 22;
    let params = get_circuit_params::<0>(degree as usize);

    // let pk = keygen_pk(&params, keygen_vk(&params, &circuit).unwrap(),
    // &circuit).unwrap();
    let pk = {
        let key_file_name = format!(
            "{}-{}-{}",
            "super", circuit_params.max_txs, circuit_params.max_calldata
        );
        load_circuit_pk(&key_file_name, &params, &circuit).unwrap()
    };

    let deployment_code = gen_evm_verifier(
        &params,
        pk.get_vk(),
        SuperCircuit::<_, MAX_TXS, MAX_CALLDATA, MAX_RWS>::num_instance(),
    );

    // let proof = gen_proof(&params, &pk, circuit.clone(), circuit.instances());
    // evm_verify(deployment_code, circuit.instances(), proof.clone());

    // #[derive(Serialize, Deserialize, Debug)]
    // struct BlockProofData {
    //     instances: Vec<U256>,
    //     proof: Vec<u8>,
    // }

    // let block_proof_data = BlockProofData {
    //     instances: circuit
    //         .instances()
    //         .iter()
    //         .flatten()
    //         .map(|v| U256::from_little_endian(v.to_repr().as_ref()))
    //         .collect(),
    //     proof: proof,
    // };

    // let output_file = if let Some(output) = config.output {
    //     output
    // } else {
    //     format!("./block-{}_super_circuit_proof.json", config.block_num)
    // };
    // File::create(output_file)
    //     .expect("open output_file")
    //     .write_all(&serde_json::to_vec(&block_proof_data).unwrap())
    //     .expect("write output_file");

    Ok(())
}
