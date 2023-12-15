use std::time::Instant;

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
use zkevm_circuits::mpt_circuit::MPTCircuitParams;
use base64::prelude::*;

pub struct FullVerifierKey {
    pub circuit_params: MPTCircuitParams,
    pub verifier_params: ParamsVerifierKZG<Bn256>,
    pub vk: VerifyingKey<G1Affine>,
}

impl FullVerifierKey {
    pub fn serialize(&self) -> Result<Vec<u8>> {
        let circuit_params_ser: Vec<u8> = bincode::serialize(&self.circuit_params)?;
        let mut vk = self.vk.clone();
        vk.remove_debug_info();

        let vk_ser: Vec<u8> = bincode::serialize(&vk)?;
        let mut verifier_params_ser: Vec<u8> = Vec::new();
        self.verifier_params.write(&mut verifier_params_ser)?;

        let all = (circuit_params_ser, verifier_params_ser, vk_ser);
        let encoded = bincode::serialize(&all)?;

        Ok(encoded)
    }
    pub fn deserialize(encoded: Vec<u8>) -> Result<Self> {
        let (circuit_params_ser, verifier_params_ser, vk_ser): (Vec<u8>, Vec<u8>, Vec<u8>) =
            bincode::deserialize(&encoded[..])?;
        Ok(Self {
            circuit_params: bincode::deserialize(&circuit_params_ser[..])?,
            vk: bincode::deserialize(&vk_ser[..])?,
            verifier_params: ParamsVerifierKZG::<Bn256>::read(&mut &verifier_params_ser[..])?,
        })
    }
}

pub fn verify(fk: &FullVerifierKey, proof: &[u8], public_inputs: &[Fr]) -> Result<bool> {
    let start = Instant::now();

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

    println!("verification time: {:?}", start.elapsed());

    Ok(result.is_ok())
}



pub fn wasm_prepare(fk: &FullVerifierKey, proof: &[u8], pi: &[Fr]) -> Result<(String, String, String)> {

    let fk = BASE64_STANDARD_NO_PAD.encode(fk.serialize()?);
    let proof = BASE64_STANDARD_NO_PAD.encode(proof);
    let pi = pi.iter().map(|x| hex::encode(x.to_bytes())).collect::<Vec<_>>().join(",");

    Ok((fk, proof, pi))
}

pub fn wasm_verify(fk: String, proof: String, pi: String) -> String {

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
    fn inner(fk: String, proof: String, pi: Vec<&str>) -> Result<bool> {
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