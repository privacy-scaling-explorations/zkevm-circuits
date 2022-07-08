//! State circuit benchmarks

#[cfg(test)]
mod tests {
    use crate::bench_params::DEGREE;
    use ark_std::{end_timer, start_timer};
    use halo2_proofs::{
        halo2curves::bn256::{Bn256, Fr},
        plonk::{create_proof, keygen_pk, keygen_vk, verify_proof},
        poly::{
            commitment::ParamsProver,
            kzg::{
                commitment::{KZGCommitmentScheme, ParamsKZG},
                multiopen::{ProverSHPLONK, VerifierSHPLONK},
                strategy::SingleStrategy,
            },
        },
        transcript::{
            Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
        },
    };
    use rand::SeedableRng;
    use rand_xorshift::XorShiftRng;
    use zkevm_circuits::state_circuit::StateCircuit;

    type Scheme = KZGCommitmentScheme<Bn256>;

    #[cfg_attr(not(feature = "benches"), ignore)]
    #[test]
    fn bench_state_circuit_prover() {
        let empty_circuit = StateCircuit::<Fr, { 1 << 16 }>::default();

        // Initialize the polynomial commitment parameters
        let rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        // Bench setup generation
        let setup_message = format!("Setup generation with degree = {}", DEGREE);
        let start1 = start_timer!(|| setup_message);
        let general_params = ParamsKZG::<Bn256>::new(DEGREE.try_into().unwrap());
        let verifier_params = general_params.verifier_params();
        end_timer!(start1);

        // Initialize the proving key
        let vk = keygen_vk::<Scheme, _>(&general_params, &empty_circuit)
            .expect("keygen_vk should not fail");
        let pk = keygen_pk::<Scheme, _>(&general_params, vk, &empty_circuit)
            .expect("keygen_pk should not fail");
        // Create a proof
        let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);

        // Bench proof generation time
        let proof_message = format!("State Proof generation with {} degree", DEGREE);
        let start2 = start_timer!(|| proof_message);
        create_proof::<Scheme, ProverSHPLONK<_>, _, _, _, _>(
            &general_params,
            &pk,
            &[empty_circuit],
            &[&[]],
            rng,
            &mut transcript,
        )
        .expect("proof generation should not fail");
        let proof = transcript.finalize();
        end_timer!(start2);

        // Bench verification time
        let start3 = start_timer!(|| "State Proof verification");
        let mut verifier_transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
        let strategy = SingleStrategy::new(verifier_params);

        verify_proof::<Scheme, _, _, VerifierSHPLONK<_>, _>(
            verifier_params,
            pk.get_vk(),
            strategy,
            &[&[]],
            &mut verifier_transcript,
        )
        .expect("failed to verify bench circuit");
        end_timer!(start3);
    }
}
