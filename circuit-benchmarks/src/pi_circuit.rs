//! Public input circuit benchmarks
#[cfg(test)]
mod tests {
    use ark_std::{end_timer, start_timer};
    use eth_types::Word;
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
    use itertools::Itertools;
    use rand::SeedableRng;
    use rand_xorshift::XorShiftRng;
    use std::env::var;
    use zkevm_circuits::{instance::PublicData, pi_circuit::PiCircuit, util::SubCircuit};

    #[cfg_attr(not(feature = "benches"), ignore)]
    #[test]
    fn bench_pi_circuit_prover() {
        let setup_prfx = crate::constants::SETUP_PREFIX;
        let proof_gen_prfx = crate::constants::PROOFGEN_PREFIX;
        let proof_ver_prfx = crate::constants::PROOFVER_PREFIX;
        // Unique string used by bench results module for parsing the result
        const BENCHMARK_ID: &str = "Pi Circuit";

        const MAX_TXS: usize = 10;
        const MAX_WITHDRAWALS: usize = 10;
        const MAX_CALLDATA: usize = 128;

        let degree: u32 = var("DEGREE")
            .unwrap_or_else(|_| "19".to_string())
            .parse()
            .expect("Cannot parse DEGREE env var as u32");

        let public_data = generate_publicdata(MAX_TXS);
        let circuit = PiCircuit::<Fr>::new(MAX_TXS, MAX_WITHDRAWALS, MAX_CALLDATA, public_data);
        let public_inputs = circuit.instance();
        let instance: Vec<&[Fr]> = public_inputs.iter().map(|input| &input[..]).collect();
        let instances = &[&instance[..]];

        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

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
            XorShiftRng,
            Blake2bWrite<Vec<u8>, G1Affine, Challenge255<G1Affine>>,
            PiCircuit<Fr>,
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
            instances,
            &mut verifier_transcript,
        )
        .expect("failed to verify bench circuit");
        end_timer!(start3);
    }

    fn generate_publicdata(max_txs: usize) -> PublicData {
        let transactions = std::iter::repeat(eth_types::geth_types::Transaction::from(
            mock::CORRECT_MOCK_TXS[0].clone(),
        ))
        .take(max_txs)
        .collect_vec();

        PublicData {
            chain_id: Word::from(1337),
            transactions,
            ..Default::default()
        }
    }
}
