use eth_types::ToLittleEndian;
use ethers::types::{H256, U256, Address, U64};
use eyre::{eyre, Result};
use halo2_proofs::{
    halo2curves::bn256::{Bn256, Fr, G1Affine},
    plonk::{verify_proof, VerifyingKey},
    poly::{
        commitment::Params,
        kzg::{
            commitment::{KZGCommitmentScheme, ParamsVerifierKZG},
            multiopen::VerifierSHPLONK,
            strategy::SingleStrategy,
        },
    },
    transcript::{Blake2bRead, Challenge255, TranscriptReadBuffer},
};
use base64::prelude::*;
use halo2curves::ff::PrimeField;
use num_enum::IntoPrimitive;
use serde::{Serialize, Deserialize};

pub struct FullVerifierKey {
    pub verifier_params: ParamsVerifierKZG<Bn256>,
    pub vk: VerifyingKey<G1Affine>,
}

impl FullVerifierKey {
    pub fn serialize(&self) -> Result<Vec<u8>> {
        let mut vk = self.vk.clone();
        vk.remove_debug_info();

        let vk_ser: Vec<u8> = bincode::serialize(&vk)?;
        let mut verifier_params_ser: Vec<u8> = Vec::new();
        self.verifier_params.write(&mut verifier_params_ser)?;

        let all = (verifier_params_ser, vk_ser);
        let encoded = bincode::serialize(&all)?;

        Ok(encoded)
    }
    pub fn deserialize(encoded: Vec<u8>) -> Result<Self> {
        let (verifier_params_ser, vk_ser): (Vec<u8>, Vec<u8>) =
            bincode::deserialize(&encoded[..])?;
        Ok(Self {
            vk: bincode::deserialize(&vk_ser[..])?,
            verifier_params: ParamsVerifierKZG::<Bn256>::read(&mut &verifier_params_ser[..])?,
        })
    }
}

pub fn verify(fk: &FullVerifierKey, proof: &[u8], public_inputs: &[Fr]) -> Result<bool> {
    let mut verifier_transcript = Blake2bRead::<_, G1Affine, Challenge255<_>>::init(proof);
    let strategy = SingleStrategy::new(&fk.verifier_params);

    let result = verify_proof::<
        KZGCommitmentScheme<Bn256>,
        VerifierSHPLONK<'_, Bn256>,
        Challenge255<G1Affine>,
        Blake2bRead<&[u8], G1Affine, Challenge255<G1Affine>>,
        SingleStrategy<'_, Bn256>,
    >(
        &fk.verifier_params,
        &fk.vk,
        strategy,
        &[&[public_inputs]],
        &mut verifier_transcript,
    );
    Ok(result.is_ok())
}

pub fn wasm_serialize(fk: &FullVerifierKey, proof: &[u8], pi: &[Fr]) -> Result<(String, String, String)> {

    let fk = BASE64_STANDARD_NO_PAD.encode(fk.serialize()?);
    let proof = BASE64_STANDARD_NO_PAD.encode(proof);
    let pi = pi.iter().map(|x| hex::encode(x.to_bytes())).collect::<Vec<_>>().join(",");

    Ok((fk, proof, pi))
}

pub fn wasm_verify_serialized(fk: &str, proof: &str, pi: &str) -> String {

    fn str_to_fr(x: &str) -> Result<Fr> {
        let bytes = hex::decode(x)?;
        let bytes: [u8;32] = bytes.try_into().map_err(|_| eyre!("invalid fr"))?;
        let fr = Fr::from_bytes(&bytes);
        if fr.is_some().into() {
            Ok(fr.unwrap())
        } else {
            Err(eyre!("invalid fr"))
        }
    }
    fn inner(fk: &str, proof: &str, pi: Vec<&str>) -> Result<bool> {
        let fk = FullVerifierKey::deserialize(BASE64_STANDARD_NO_PAD.decode(fk)?)?;
        let proof = BASE64_STANDARD_NO_PAD.decode(proof)?;
        let pi = pi.into_iter().map(str_to_fr).collect::<Result<Vec<Fr>>>()?;
        verify(&fk, &proof, &pi)
    }
    match inner(fk, proof, pi.split(',').collect()) {
        Ok(result) => format!("success:{}", result),
        Err(err) => format!("error:{}", err),
    }
}

#[derive(Default, Debug, IntoPrimitive, Clone, Copy, Serialize, Deserialize)]
#[repr(u8)]
pub enum ProofType {
    #[default]
    Disabled = 0,
    NonceChanged = 1,
    BalanceChanged = 2,
    CodeHashChanged = 3,
    AccountDestructed = 4,
    AccountDoesNotExist = 5,
    StorageChanged = 6,
    StorageDoesNotExist = 7,
    AccountCreate = 8,
}

#[derive(Default, Debug, Clone, Serialize, Deserialize)]
pub struct InitialStateCircuitVerifierData {
    pub prev_hash : H256,
    pub next_hash : H256,
    pub trie_modifications : Vec<TrieModification>,
}

#[derive(Default, Debug, Clone, Serialize, Deserialize)]
pub struct TrieModification {
    pub typ: u64,
    pub address: Address,
    pub value: U256,
    pub key: H256,
}


fn h_to_vf(value: H256) -> Vec<Fr> {
    let mut bytes = value.as_bytes().to_vec();
    bytes.reverse();

    let mut lo = [0u8; 32];
    let mut hi = [0u8; 32];
    lo[0..16].copy_from_slice(&bytes[..16]);
    hi[0..16].copy_from_slice(&bytes[16..]);

    let lo = Fr::from_repr(lo).unwrap();
    let hi = Fr::from_repr(hi).unwrap();

    vec![lo, hi]
}

fn u_to_vf(value: U256) -> Vec<Fr> {
    let mut bytes = [0u8;32];

    value.to_little_endian(&mut bytes);

    let mut lo = [0u8; 32];
    let mut hi = [0u8; 32];
    lo[0..16].copy_from_slice(&bytes[..16]);
    hi[0..16].copy_from_slice(&bytes[16..]);

    let lo = Fr::from_repr(lo).unwrap();
    let hi = Fr::from_repr(hi).unwrap();

    vec![lo, hi]
}

fn a_to_vf(value: Address) -> Fr {
    let mut f = [0u8; 32];
    f[0..20].copy_from_slice(value.as_bytes());

    Fr::from_repr(f).unwrap()
}

impl InitialStateCircuitVerifierData {
    pub fn hash(&self) -> H256 {

        let h =| x : H256 | { let mut v = x.as_bytes().to_vec(); v.reverse(); v };
        let u =| x : U256 | { let mut v = [0u8;32]; x.to_little_endian(&mut v);  v.to_vec() };
        let a =| x : Address | { x.as_bytes().to_vec() };

        let mut bytes = Vec::new();
        bytes.append(&mut h(self.prev_hash));
        bytes.append(&mut h(self.next_hash));

        for m in &self.trie_modifications {
            bytes.push(m.typ as u8);
            bytes.append(&mut a(m.address));
            bytes.append(&mut u(m.value));
            bytes.append(&mut h(m.key));
        }

        println!("i: {}", hex::encode(&bytes));

        let hash = ethers::utils::keccak256(bytes);

        H256::from_slice(&hash)
    }
}
