//! Tx circuit benchmarks

#[cfg(test)]
mod tests {
    use ark_std::{end_timer, start_timer};
    use env_logger::Env;
    use halo2_proofs::{
        halo2curves::bn256::{Bn256, Fr, G1Affine},
        plonk::{create_proof, keygen_pk, keygen_vk, verify_proof},
        poly::{
            commitment::ParamsProver,
            kzg::{
                commitment::{KZGCommitmentScheme, ParamsKZG, ParamsVerifierKZG},
                multiopen::{ProverSHPLONK, VerifierSHPLONK},
                strategy::SingleStrategy,
            },
        },
        transcript::{
            Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
        },
    };
    use rand::SeedableRng;
    use rand_chacha::ChaCha20Rng;
    use std::env::var;
    use zkevm_circuits::tx_circuit::TxCircuit;

    #[cfg_attr(not(feature = "benches"), ignore)]
    #[test]
    fn bench_tx_circuit_prover() {
        env_logger::Builder::from_env(Env::default().default_filter_or("debug")).init();
        let setup_prfx = crate::constants::SETUP_PREFIX;
        let proof_gen_prfx = crate::constants::PROOFGEN_PREFIX;
        let proof_ver_prfx = crate::constants::PROOFVER_PREFIX;
        // Unique string used by bench results module for parsing the result
        const BENCHMARK_ID: &str = "Tx Circuit";

        // Approximate value, adjust with changes on the TxCircuit.
        const ROWS_PER_TX: usize = 175_000;

        const MAX_CALLDATA: usize = 1024;

        let degree: u32 = var("DEGREE")
            .unwrap_or_else(|_| "19".to_string())
            .parse()
            .expect("Cannot parse DEGREE env var as u32");

        let max_txs: usize = 2_usize.pow(degree) / ROWS_PER_TX;

        let mut rng = ChaCha20Rng::seed_from_u64(42);

        let chain_id: u64 = mock::MOCK_CHAIN_ID.low_u64();
        let txs = vec![mock::CORRECT_MOCK_TXS[0].clone().into()];
        let circuit = TxCircuit::<Fr>::new(max_txs, MAX_CALLDATA, chain_id, txs);

        // Bench setup generation
        let setup_message = format!("{} {} with degree = {}", BENCHMARK_ID, setup_prfx, degree);
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
        let proof_message = format!(
            "{} {} with degree = {}",
            BENCHMARK_ID, proof_gen_prfx, degree
        );
        let start2 = start_timer!(|| proof_message);
        create_proof::<
            KZGCommitmentScheme<Bn256>,
            ProverSHPLONK<'_, Bn256>,
            Challenge255<G1Affine>,
            ChaCha20Rng,
            Blake2bWrite<Vec<u8>, G1Affine, Challenge255<G1Affine>>,
            TxCircuit<Fr>,
        >(
            &general_params,
            &pk,
            &[circuit],
            &[&[&[]]],
            rng,
            &mut transcript,
        )
        .expect("proof generation should not fail");
        let proof = transcript.finalize();
        end_timer!(start2);

        // Bench verification time
        let start3 = start_timer!(|| format!("{} {}", BENCHMARK_ID, proof_ver_prfx));
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
            &[&[&[]]],
            &mut verifier_transcript,
        )
        .expect("failed to verify bench circuit");
        end_timer!(start3);
    }
}
