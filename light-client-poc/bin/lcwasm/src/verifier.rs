use std::time::Instant;

use halo2_proofs::{dev::MockProver, halo2curves::bn256::{Fr, Bn256, G1Affine}, poly::{kzg::{commitment::{ParamsKZG, ParamsVerifierKZG, KZGCommitmentScheme}, multiopen::{ProverSHPLONK, VerifierSHPLONK}, strategy::SingleStrategy}, commitment::ParamsProver}, plonk::{keygen_vk, keygen_pk, create_proof, verify_proof, VerifyingKey}, transcript::{Blake2bWrite, Challenge255, TranscriptWriterBuffer, Blake2bRead, TranscriptReadBuffer}};
use eyre::Result;


pub fn verify(verifier_params: ParamsVerifierKZG<Bn256> , vk: VerifyingKey<G1Affine>, proof: Vec<u8>, public_inputs: Vec<Fr>) -> Result<bool>{
    let start = Instant::now();
    let mut verifier_transcript = Blake2bRead::<_, G1Affine, Challenge255<_>>::init(&proof[..]);
    let strategy = SingleStrategy::new(&verifier_params);

    let result = verify_proof::<
        KZGCommitmentScheme<Bn256>,
        VerifierSHPLONK<'_, Bn256>,
        Challenge255<G1Affine>,
        Blake2bRead<&[u8], G1Affine, Challenge255<G1Affine>>,
        SingleStrategy<'_, Bn256>,
    >(
        &verifier_params,
        &vk,
        strategy,
        &[&[&public_inputs]],
        &mut verifier_transcript,
    );

    Ok(result.is_err())
}
