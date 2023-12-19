use std::io::Write;

use eth_types::{ Field};
use ethers::{prelude::*, types::transaction::eip2930::AccessList};
use eyre::Result;
use halo2_proofs::halo2curves::bn256::Fr;
use halo2curves::ff::PrimeField;
use zkevm_circuits::util::word::Word;

use light_client_poc::{
    circuits::initial_state::{InitialStateCircuit},
    witness::{utils::new_eth_signer_client, Witness},
};
use light_client_poc::circuits::initial_state::circuit::InitialCircuitHelper;


fn wf_to_h<F: Field>(value: Word<F>) -> H256 {
    let lo = &value.lo().to_repr()[0..16];
    let hi = &value.hi().to_repr()[0..16];
    let lo_hi = lo.iter().chain(hi.iter()).rev().copied().collect::<Vec<_>>();
    H256::from_slice(&lo_hi[..])
}

fn h_to_vf<F: Field>(value: H256) -> Vec<F> {
    let mut bytes = value.as_bytes().to_vec();
    bytes.reverse();

    let mut lo = [0u8; 32];
    let mut hi = [0u8; 32];
    lo[0..16].copy_from_slice(&bytes[..16]);
    hi[0..16].copy_from_slice(&bytes[16..]);

    let lo = F::from_repr(lo).unwrap();
    let hi = F::from_repr(hi).unwrap();

    vec![lo, hi]
}

fn wf_to_u<F: Field>(value: Word<F>) -> U256 {
    let lo = &value.lo().to_repr()[0..16];
    let hi = &value.hi().to_repr()[0..16];
    let lo_hi = lo.iter().chain(hi.iter()).copied().collect::<Vec<_>>();
    U256::from_little_endian(&lo_hi[..])
}

fn u_to_vf<F: Field>(value: U256) -> Vec<F> {
    let mut bytes = [0u8;32];

    value.to_little_endian(&mut bytes);

    let mut lo = [0u8; 32];
    let mut hi = [0u8; 32];
    lo[0..16].copy_from_slice(&bytes[..16]);
    hi[0..16].copy_from_slice(&bytes[16..]);

    let lo = F::from_repr(lo).unwrap();
    let hi = F::from_repr(hi).unwrap();

    vec![lo, hi]
}

fn wf_to_a<F: Field>(value: F) -> Address {
    Address::from_slice(&value.to_repr()[0..20])
}

fn a_to_vf<F: Field>(value: Address) -> Vec<F> {
    let mut f = [0u8; 32];
    f[0..20].copy_from_slice(value.as_bytes());

    vec![F::from_repr(f).unwrap()]
}


#[tokio::main]
async fn main() -> Result<()> {
    let bytes : Vec<u8> = std::iter::successors(Some(0u8), |n| Some(n+1)).take(32).collect();

    let h1 = H256::from_slice(&bytes[..]);
    let w1 = h_to_vf::<Fr>(h1);
    let h2 = wf_to_h::<Fr>(Word::new([w1[0],w1[1]]));

    assert_eq!(h1, h2);

    let u1 = U256::from_little_endian(&bytes[..]);
    let w1 = u_to_vf::<Fr>(u1);
    let u2 = wf_to_u::<Fr>(Word::new([w1[0],w1[1]]));

    assert_eq!(u1, u2);

    let bytes : Vec<u8> = std::iter::successors(Some(0u8), |n| Some(n+1)).take(20).collect();

    let provider = env!("PROVIDER_URL");
    println!("provider: {}", provider);

    const PVK: &str = "7ccb34dc5fd31fd0aa7860de89a4adc37ccb34dc5fd31fd0aa7860de89a4adc3";
    let client = new_eth_signer_client(provider, PVK).await?;

    let degree = 16;
    let block_no = 107;
    let max_proof_count = 30;
    let access_list = include_str!("../test_mainnet/al/107.json");
    let access_list: AccessList = serde_json::from_str(access_list)?;

    let witness = Witness::<Fr>::build(
        client.clone(),
        provider,
        U64::from(block_no),
        Some(access_list),
        true,
    )
    .await?
    .unwrap();

    let verifier_data = witness.lc_witness.verifier_data();
    let data = serde_json::to_string(&verifier_data)?;

    let circuit = InitialStateCircuit::new(witness, degree, max_proof_count)?;
    circuit.assert_satisfied();


    println!("Creating key & verifing...");

    let (fk, proof, _pi) = circuit.assert_real_prover()?;
    let (fk_s, proof_s) = light_client_poc::verifier::wasm_serialize(&fk, &proof)?;

    std::fs::File::create("./prover.fk")?.write_all(fk_s.as_bytes())?;
    std::fs::File::create("./prover.proof")?.write_all(proof_s.as_bytes())?;
    std::fs::File::create("./prover.data")?.write_all(data.as_bytes())?;

    let result = light_client_poc::verifier::wasm_verify_serialized(&data, &fk_s, &proof_s);
    println!("{}", result);

    Ok(())
}