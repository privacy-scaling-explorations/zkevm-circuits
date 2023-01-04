//! PI circuit benchmarks
use ark_std::{end_timer, start_timer};
use eth_types::Word;
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
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
use rand_xorshift::XorShiftRng;
use std::env::var;
use zkevm_circuits::pi_circuit::{PiCircuit, PiTestCircuit, PublicData};
use zkevm_circuits::test_util::rand_tx;
use zkevm_circuits::util::SubCircuit;

#[cfg_attr(not(feature = "benches"), ignore)]
#[test]
fn bench_pi_circuit_prover() {
    let degree: u32 = var("DEGREE")
        .unwrap_or_else(|_| "15".to_string())
        .parse()
        .expect("Cannot parse DEGREE env var as u32");

    const MAX_TXS: usize = 10;
    const MAX_CALLDATA: usize = 128;

    let mut rng = ChaCha20Rng::seed_from_u64(2);
    let randomness = Fr::random(&mut rng);
    let rand_rpi = Fr::random(&mut rng);
    let public_data = generate_publicdata::<MAX_TXS, MAX_CALLDATA>();
    let circuit = PiTestCircuit::<Fr, MAX_TXS, MAX_CALLDATA>(PiCircuit::<Fr>::new(
        MAX_TXS,
        MAX_CALLDATA,
        randomness,
        rand_rpi,
        public_data,
    ));
    let public_inputs = circuit.0.instance();
    let instance: Vec<&[Fr]> = public_inputs.iter().map(|input| &input[..]).collect();
    let instances = &[&instance[..]][..];

    let mut rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);

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
    let proof_message = format!("PI_circuit Proof generation with {} rows", degree);
    let start2 = start_timer!(|| proof_message);
    create_proof::<
        KZGCommitmentScheme<Bn256>,
        ProverSHPLONK<'_, Bn256>,
        Challenge255<G1Affine>,
        XorShiftRng,
        Blake2bWrite<Vec<u8>, G1Affine, Challenge255<G1Affine>>,
        PiTestCircuit<Fr, MAX_TXS, MAX_CALLDATA>,
    >(
        &general_params,
        &pk,
        &[circuit],
        instances,
        rng,
        &mut transcript,
    )
    .expect("proof generation should not fail");
    let proof = transcript.finalize();
    end_timer!(start2);

    // Bench verification time
    let start3 = start_timer!(|| "PI_circuit Proof verification");
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
        instances,
        &mut verifier_transcript,
    )
    .expect("failed to verify bench circuit");
    end_timer!(start3);
}

fn generate_publicdata<const MAX_TXS: usize, const MAX_CALLDATA: usize>() -> PublicData {
    let mut rng = ChaCha20Rng::seed_from_u64(2);
    let mut public_data = PublicData::default();
    let chain_id = 1337u64;
    public_data.chain_id = Word::from(chain_id);

    let n_tx = MAX_TXS;
    for _ in 0..n_tx {
        let eth_tx = eth_types::Transaction::from(&rand_tx(&mut rng, chain_id, true));
        public_data.transactions.push(eth_tx);
    }
    public_data
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

fn new_pi_circuit<const MAX_TXS: usize, const MAX_CALLDATA: usize>(
) -> PiTestCircuit<Fr, MAX_TXS, MAX_CALLDATA> {
    let mut rng = ChaCha20Rng::seed_from_u64(2);
    let randomness = Fr::random(&mut rng);
    let rand_rpi = Fr::random(&mut rng);
    let public_data = generate_publicdata::<MAX_TXS, MAX_CALLDATA>();
    let circuit = PiTestCircuit::<Fr, MAX_TXS, MAX_CALLDATA>(PiCircuit::<Fr>::new(
        MAX_TXS,
        MAX_CALLDATA,
        randomness,
        rand_rpi,
        public_data,
    ));
    circuit
}

trait InstancesExport {
    fn num_instance() -> Vec<usize>;

    fn instances(&self) -> Vec<Vec<Fr>>;
}

impl<const MAX_TXS: usize, const MAX_CALLDATA: usize> InstancesExport
    for PiTestCircuit<Fr, MAX_TXS, MAX_CALLDATA>
{
    fn num_instance() -> Vec<usize> {
        vec![5]
    }

    fn instances(&self) -> Vec<Vec<Fr>> {
        // vec![vec![self.0]]
        self.0.instance()
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

    File::create("./PlonkEvmVerifier.sol")
        .expect("PlonkEvmVerifier.sol")
        .write_all(&loader.yul_code().as_bytes())
        .expect("PlonkEvmVerifier.sol");

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

#[test]
fn test_pi_with_verifier() {
    let degree: u32 = var("DEGREE")
        .unwrap_or_else(|_| "18".to_string())
        .parse()
        .expect("Cannot parse DEGREE env var as u32");

    let params = get_circuit_params::<0>(degree as usize);
    const MAX_TXS: usize = 10;
    const MAX_CALLDATA: usize = 128;
    let circuit = new_pi_circuit::<MAX_TXS, MAX_CALLDATA>();

    let pk = keygen_pk(&params, keygen_vk(&params, &circuit).unwrap(), &circuit).unwrap();
    let deployment_code = gen_evm_verifier(
        &params,
        pk.get_vk(),
        PiTestCircuit::<Fr, MAX_TXS, MAX_CALLDATA>::num_instance(),
    );

    let proof = gen_proof(&params, &pk, circuit.clone(), circuit.instances());
    evm_verify(deployment_code, circuit.instances(), proof);
}
