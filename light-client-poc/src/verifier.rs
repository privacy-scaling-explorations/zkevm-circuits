use base64::prelude::*;
use ethers_core::types::{Address, H256, U256};
use eyre::Result;
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
use halo2curves::ff::PrimeField;
use num_enum::IntoPrimitive;
use serde::{Deserialize, Serialize};

pub struct FullVerifierKey {
    pub verifier_params: ParamsVerifierKZG<Bn256>,
    pub vk: VerifyingKey<G1Affine>,
}

impl FullVerifierKey {
    pub fn serialize(&self) -> Result<Vec<u8>> {
        let vk = self.vk.clone().strip();

        let vk_ser: Vec<u8> = bincode::serialize(&vk)?;
        let mut verifier_params_ser: Vec<u8> = Vec::new();
        self.verifier_params.write(&mut verifier_params_ser)?;

        let all = (verifier_params_ser, vk_ser);
        let encoded = bincode::serialize(&all)?;

        Ok(encoded)
    }
    pub fn deserialize(encoded: Vec<u8>) -> Result<Self> {
        let (verifier_params_ser, vk_ser): (Vec<u8>, Vec<u8>) = bincode::deserialize(&encoded[..])?;
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

pub fn wasm_serialize(fk: &FullVerifierKey, proof: &[u8]) -> Result<(String, String)> {
    let fk = BASE64_STANDARD_NO_PAD.encode(fk.serialize()?);
    let proof = BASE64_STANDARD_NO_PAD.encode(proof);

    Ok((fk, proof))
}

pub fn wasm_verify_serialized(data: &str, fk: &str, proof: &str) -> String {
    fn inner(data: &str, fk: &str, proof: &str) -> Result<bool> {
        let data = serde_json::from_str::<InitialStateCircuitVerifierData>(data)?;
        let fk = FullVerifierKey::deserialize(BASE64_STANDARD_NO_PAD.decode(fk)?)?;
        let proof = BASE64_STANDARD_NO_PAD.decode(proof)?;

        let mut data_hash = data.hash().to_fixed_bytes();
        data_hash.reverse();
        let mut lo = [0u8; 32];
        let mut hi = [0u8; 32];
        hi[0..16].copy_from_slice(&data_hash[16..32]);
        lo[0..16].copy_from_slice(&data_hash[0..16]);
        let pi = vec![Fr::from_repr(lo).unwrap(), Fr::from_repr(hi).unwrap()];

        verify(&fk, &proof, &pi)
    }
    match inner(data, fk, proof) {
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
    pub prev_hash: H256,
    pub next_hash: H256,
    pub trie_modifications: Vec<TrieModification>,
}

#[derive(Default, Debug, Clone, Serialize, Deserialize)]
pub struct TrieModification {
    pub typ: u64,
    pub address: Address,
    pub value: U256,
    pub key: H256,
}

impl InitialStateCircuitVerifierData {
    pub fn hash(&self) -> H256 {
        let h = |x: H256| {
            let mut v = x.as_bytes().to_vec();
            v.reverse();
            v
        };
        let u = |x: U256| {
            let mut v = [0u8; 32];
            x.to_little_endian(&mut v);
            v.to_vec()
        };
        let a = |x: Address| x.as_bytes().to_vec();

        let mut bytes = Vec::new();
        bytes.append(&mut h(self.prev_hash));
        bytes.append(&mut h(self.next_hash));

        for m in &self.trie_modifications {
            bytes.push(m.typ as u8);
            bytes.append(&mut a(m.address));
            bytes.append(&mut u(m.value));
            bytes.append(&mut h(m.key));
        }

        let hash = ethers_core::utils::keccak256(bytes);

        H256::from_slice(&hash)
    }
}
