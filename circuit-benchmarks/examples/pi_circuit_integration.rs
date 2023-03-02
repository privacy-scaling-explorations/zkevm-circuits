//! PI circuit benchmarks
use ark_std::{end_timer, start_timer};
use eth_types::{Bytes, U256};
use halo2_proofs::plonk::{create_proof, keygen_pk, keygen_vk, verify_proof};
use halo2_proofs::poly::kzg::commitment::{KZGCommitmentScheme, ParamsKZG};
use halo2_proofs::{
    halo2curves::bn256::{Bn256, Fr, G1Affine},
    poly::commitment::ParamsProver,
    transcript::{TranscriptReadBuffer, TranscriptWriterBuffer},
};
use std::env::var;
use zkevm_circuits::pi_circuit2::{PiCircuit, PiTestCircuit, PublicData};
use zkevm_circuits::util::SubCircuit;

#[cfg(test)]
mod test {
    use super::*;
    use eth_types::Word;
    use halo2_proofs::arithmetic::Field;
    use halo2_proofs::poly::kzg::commitment::ParamsVerifierKZG;
    use halo2_proofs::poly::kzg::multiopen::{ProverSHPLONK, VerifierSHPLONK};
    use halo2_proofs::poly::kzg::strategy::SingleStrategy;
    use halo2_proofs::transcript::{Blake2bRead, Blake2bWrite, Challenge255};
    use rand::SeedableRng;
    use rand_chacha::ChaCha20Rng;
    use rand_xorshift::XorShiftRng;
    use std::io::Read;
    use zkevm_circuits::pi_circuit::PublicData;
    use zkevm_circuits::test_util::rand_tx;

    #[cfg_attr(not(feature = "benches"), ignore)]
    #[test]
    fn bench_pi_circuit_prover() {
        let degree: u32 = var("DEGREE")
            .unwrap_or_else(|_| "21".to_string())
            .parse()
            .expect("Cannot parse DEGREE env var as u32");

        const MAX_TXS: usize = 80;
        const MAX_CALLDATA: usize = 65536 * 16;

        let public_data = generate_publicdata::<MAX_TXS, MAX_CALLDATA>();
        let circuit = PiTestCircuit::<Fr, MAX_TXS, MAX_CALLDATA>(PiCircuit::<Fr>::new(
            MAX_TXS,
            MAX_CALLDATA,
            randomness,
        ));
        let public_inputs = circuit.0.instance();
        let instance: Vec<&[Fr]> = public_inputs.iter().map(|input| &input[..]).collect();
        let instances = &[&instance[..]][..];

        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
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

    #[test]
    fn test_dummy_pi_verifier() {
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
            None,
        );

        let proof = gen_proof(&params, &pk, circuit.clone(), circuit.instances());
        evm_verify(deployment_code, circuit.instances(), proof);
    }

    #[test]
    fn test_calldata_contract_pairing() {
        let calldata_path = "./calldata.bin";
        let metadata = fs::metadata(&calldata_path).expect("unable to read calldata_file");
        let mut calldata_file = fs::File::open(calldata_path).expect("open calldata bin");
        let mut calldata = vec![0; metadata.len() as usize];
        calldata_file
            .read(&mut calldata)
            .expect("read calldata bin");

        let yul_code_path = "./PlonkEvmVerifier.sol";
        let yul_code = fs::read_to_string(yul_code_path).unwrap();
        let deployment_code = evm::compile_yul(yul_code.as_str());

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

    fn new_pi_circuit<const MAX_TXS: usize, const MAX_CALLDATA: usize>(
    ) -> PiTestCircuit<Fr, MAX_TXS, MAX_CALLDATA> {
        let public_data = generate_publicdata::<MAX_TXS, MAX_CALLDATA>();
        let circuit = PiTestCircuit::<Fr, MAX_TXS, MAX_CALLDATA>(PiCircuit::<Fr>::new(
            MAX_TXS,
            MAX_CALLDATA,
            randomness,
        ));
        circuit
    }
}

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
use std::{io::Write, rc::Rc};

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

impl<const MAX_TXS: usize, const MAX_CALLDATA: usize> InstancesExport
    for PiTestCircuit<Fr, MAX_TXS, MAX_CALLDATA>
{
    fn num_instance() -> Vec<usize> {
        vec![2]
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
    yul_file_name: Option<String>,
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

    let file_path = &yul_file_name.unwrap_or(String::from("./PlonkEvmVerifier.sol"));
    File::create(file_path)
        .expect(file_path)
        .write_all(&loader.yul_code().as_bytes())
        .expect(file_path);

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
        create_proof::<KZGCommitmentScheme<_>, ProverGWC<_>, _, _, EvmTranscript<_, _, _, _>, _>(
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

pub fn write_pk(pk_file_path: &Path, pk: &ProvingKey<G1Affine>) -> Result<(), std::io::Error> {
    let dir = pk_file_path.parent().unwrap();
    fs::create_dir_all(dir).expect(format!("create {:?}", dir).as_str());
    let mut file = fs::File::create(&pk_file_path)?;
    pk.write(&mut file)
}

pub fn read_pk<C: Circuit<Fr>>(
    pk_file_path: &str,
    params: &ParamsKZG<Bn256>,
) -> Result<ProvingKey<G1Affine>, std::io::Error> {
    let mut file = fs::File::open(&pk_file_path)?;
    ProvingKey::<G1Affine>::read::<File, C>(&mut file, params)
}

#[cfg(feature = "load_pk")]
mod cfg {
    pub const LOAD_PK: bool = true;
    pub const SAVE_PK: bool = true;
}
#[cfg(not(feature = "load_pk"))]
mod cfg {
    pub const LOAD_PK: bool = false;
    pub const SAVE_PK: bool = false;
}

fn load_circuit_pk<C: Circuit<Fr>>(
    pk_name: &str,
    params: &ParamsKZG<Bn256>,
    circuit: &C,
) -> Result<ProvingKey<G1Affine>, halo2_proofs::plonk::Error> {
    let pk_file_path = Path::new("./generated/keys").join(pk_name);
    if pk_file_path.exists() && cfg::LOAD_PK {
        read_pk::<C>(pk_file_path.to_str().unwrap(), params).map_err(|e| e.into())
    } else {
        let pk = keygen_pk(params, keygen_vk(params, circuit).unwrap(), circuit)?;
        if cfg::SAVE_PK {
            write_pk(pk_file_path.as_path(), &pk)?;
        }
        Ok(pk)
    }
}

use bus_mapping::circuit_input_builder::{BuilderClient, CircuitsParams};
use bus_mapping::public_input_builder::get_txs_rlp;
use bus_mapping::rpc::GethClient;
use bus_mapping::Error;
use clap::Parser;
use serde::{Deserialize, Serialize};
use std::str::FromStr;
use zkevm_circuits::evm_circuit::witness::block_convert;
use zkevm_circuits::tx_circuit::PrimeField;

#[cfg(feature = "http_provider")]
use ethers_providers::Http;
#[cfg(not(feature = "http_provider"))]
use ethers_providers::Ws;

#[derive(Parser, Debug)]
#[clap(version, about)]
pub(crate) struct ProverCmdConfig {
    /// l1_geth_url
    l1_geth_url: Option<String>,
    /// propose tx hash
    propose_tx_hash: Option<String>,
    /// l2_geth_url
    l2_geth_url: Option<String>,
    /// block_num
    block_num: Option<u64>,
    /// prover address
    address: Option<String>,
    /// generate yul
    yul_output: Option<String>,
    /// output_file
    output: Option<String>,
}

#[derive(Clone, Default, Debug, Serialize, Deserialize)]
pub struct CircuitConfig {
    pub block_gas_limit: usize,
    pub max_txs: usize,
    pub max_calldata: usize,
    pub max_bytecode: usize,
    pub max_rws: usize,
    pub min_k: usize,
    pub pad_to: usize,
    pub min_k_aggregation: usize,
    pub keccak_padding: usize,
}

// from zkevm-chain
macro_rules! select_circuit_config {
    ($txs:expr, $on_match:expr, $on_error:expr) => {
        match $txs {
            0..=10 => {
                const CIRCUIT_CONFIG: CircuitConfig = CircuitConfig {
                    block_gas_limit: 6300000,
                    max_txs: 10,
                    max_calldata: 131072,
                    max_bytecode: 131072,
                    max_rws: 3161966,
                    min_k: 19,
                    pad_to: 2097152,
                    min_k_aggregation: 26,
                    keccak_padding: 336000,
                };
                $on_match
            }
            16..=80 => {
                const CIRCUIT_CONFIG: CircuitConfig = CircuitConfig {
                    block_gas_limit: 6300000,
                    max_txs: 80,
                    max_calldata: 697500,
                    max_bytecode: 139500,
                    max_rws: 3161966,
                    min_k: 21,
                    pad_to: 2097152,
                    min_k_aggregation: 26,
                    keccak_padding: 1600000,
                };
                $on_match
            }

            _ => $on_error,
        }
    };
}

#[tokio::main]
async fn main() -> Result<(), Error> {
    let txs: u32 = var("TXS")
        .unwrap_or_else(|_| "21".to_string())
        .parse()
        .expect("Cannot parse TXS env var as u32");

    let config = ProverCmdConfig::parse();
    let block_num = config.block_num.map_or_else(|| 1, |n| n);
    let prover = eth_types::Address::from_slice(
        &hex::decode(config.address.expect("needs prover").as_bytes()).expect("parse_address"),
    );

    #[cfg(feature = "http_provider")]
    let l1_provider = Http::from_str(&config.l1_geth_url.unwrap()).expect("Http geth url");
    #[cfg(not(feature = "http_provider"))]
    let l1_provider = Ws::connect(&config.l1_geth_url.unwrap())
        .await
        .expect("l1 ws rpc connected");
    let l1_geth_client = GethClient::new(l1_provider);
    let propose_tx_hash = eth_types::H256::from_slice(
        &hex::decode(config.propose_tx_hash.unwrap().as_bytes()).expect("parse_hash"),
    );
    let txs_rlp = get_txs_rlp(&l1_geth_client, propose_tx_hash).await?;

    #[cfg(feature = "http_provider")]
    let l2_provider = Http::from_str(&config.l2_geth_url.unwrap()).expect("Http geth url");
    #[cfg(not(feature = "http_provider"))]
    let l2_provider = Ws::connect(&config.l2_geth_url.unwrap())
        .await
        .expect("l2 ws rpc connected");
    let l2_geth_client = GethClient::new(l2_provider);

    let circuit_params = select_circuit_config!(
        txs,
        {
            CircuitsParams {
                max_rws: CIRCUIT_CONFIG.max_rws,
                max_txs: CIRCUIT_CONFIG.max_txs,
                max_calldata: CIRCUIT_CONFIG.max_calldata,
                max_bytecode: CIRCUIT_CONFIG.max_bytecode,
                keccak_padding: Some(CIRCUIT_CONFIG.keccak_padding),
            }
        },
        {
            panic!("no match txs circuit");
        }
    );

    let builder = BuilderClient::new(l2_geth_client, circuit_params.clone()).await?;
    let (builder, _) = builder.gen_inputs(block_num).await?;
    let block = block_convert(&builder.block, &builder.code_db).unwrap();
    select_circuit_config!(
        txs,
        {
            let public_data = PublicData::new(&block, prover, txs_rlp);
            println!("using CIRCUIT_CONFIG = {:?}", CIRCUIT_CONFIG);
            let circuit =
                PiTestCircuit::<Fr, { CIRCUIT_CONFIG.max_txs }, { CIRCUIT_CONFIG.max_calldata }>(
                    PiCircuit::new(
                        CIRCUIT_CONFIG.max_txs,
                        CIRCUIT_CONFIG.max_calldata,
                        public_data,
                    ),
                );
            assert!(block.txs.len() <= CIRCUIT_CONFIG.max_txs);

            let params = get_circuit_params::<0>(CIRCUIT_CONFIG.min_k as usize);

            // let pk = keygen_pk(&params, keygen_vk(&params, &circuit).unwrap(),
            // &circuit).unwrap();
            let pk = {
                let key_file_name = format!(
                    "{}-{}-{}",
                    "pi", circuit_params.max_txs, circuit_params.max_calldata
                );
                load_circuit_pk(&key_file_name, &params, &circuit).unwrap()
            };

            let deployment_code = if config.yul_output.is_some() {
                gen_evm_verifier(
                        &params,
                        pk.get_vk(),
                        PiTestCircuit::<
                            Fr,
                            { CIRCUIT_CONFIG.max_txs },
                            { CIRCUIT_CONFIG.max_calldata },
                        >::num_instance(),
                        config.yul_output
                    )
            } else {
                vec![]
            };

            let start = start_timer!(|| "EVM circuit Proof verification");
            let proof = gen_proof(&params, &pk, circuit.clone(), circuit.instances());
            end_timer!(start);

            if !deployment_code.is_empty() {
                evm_verify(deployment_code, circuit.instances(), proof.clone());
            }

            #[derive(Serialize, Deserialize, Debug)]
            struct BlockProofData {
                instances: Vec<U256>,
                proof: Bytes,
            }

            let block_proof_data = BlockProofData {
                instances: circuit
                    .instances()
                    .iter()
                    .flatten()
                    .map(|v| U256::from_little_endian(v.to_repr().as_ref()))
                    .collect(),
                proof: proof.into(),
            };

            let output_file = if let Some(output) = config.output {
                output
            } else {
                let l1_tx_hash = propose_tx_hash.to_string();
                format!("./block-{}_proof-new.json", &l1_tx_hash)
            };
            File::create(output_file)
                .expect("open output_file")
                .write_all(&serde_json::to_vec(&block_proof_data).unwrap())
                .expect("write output_file");
            Ok(())
        },
        { panic!("no matched txs") }
    )
}
