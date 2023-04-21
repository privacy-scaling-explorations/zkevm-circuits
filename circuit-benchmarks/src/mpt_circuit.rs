//! MPT circuit benchmarks

#[cfg(test)]
mod tests {
    use ark_std::{end_timer, start_timer};
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
    use halo2_proofs::arithmetic::FieldExt;
    use rand::SeedableRng;
    use rand_xorshift::XorShiftRng;
    use std::env::var;
    use zkevm_circuits::mpt_circuit::MPTCircuit;
    use zkevm_circuits::mpt_circuit::witness_row::{MptWitnessRow, prepare_witness};

    #[cfg_attr(not(feature = "benches"), ignore)]
    #[test]
    fn bench_mpt_circuit_prover() {
        let degree: u32 = var("DEGREE")
            .expect("No DEGREE env var was provided")
            .parse()
            .expect("Cannot parse DEGREE env var as u32");
    
        let path = "../zkevm-circuits/src/mpt_circuit/tests/UpdateOneLevel.json";
        let file = std::fs::File::open(path.clone());
        let reader = std::io::BufReader::new(file.unwrap());
        let w: Vec<Vec<u8>> = serde_json::from_reader(reader).unwrap();

        let count = w.iter().filter(|r| r[r.len() - 1] != 5).count() * 2;
        let randomness: Fr = Fr::one() + Fr::one();
        let instance: Vec<Vec<Fr>> = (1..32 + 1)
            .map(|exp| vec![randomness.pow(&[exp as u64, 0, 0, 0]); count])
            .collect();
    
        let mut keccak_data = vec![];
        let mut witness_rows = vec![];
        for row in w.iter() {
            if row[row.len() - 1] == 5 {
                keccak_data.push(row[0..row.len() - 1].to_vec());
            } else {
                let row = MptWitnessRow::<Fr>::new(row[0..row.len()].to_vec());
                witness_rows.push(row);
            }
        }
        let nodes = prepare_witness(&mut witness_rows);
        // let num_rows: usize = nodes.iter().map(|node| node.values.len()).sum();

        let circuit = MPTCircuit::<Fr> {
            nodes,
            keccak_data,
            randomness,
        };

        // Initialize the polynomial commitment parameters
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
        let proof_message = format!(
            "MPT Proof generation with degree = {}",
            degree
        );
        let start2 = start_timer!(|| proof_message);

        let instances:Vec<&[Fr]> = instance.iter().map(|i| i.as_slice()).collect();

        create_proof::<
            KZGCommitmentScheme<Bn256>,
            ProverSHPLONK<'_, Bn256>,
            Challenge255<G1Affine>,
            XorShiftRng,
            Blake2bWrite<Vec<u8>, G1Affine, Challenge255<G1Affine>>,
            MPTCircuit<Fr>,
        >(
            &general_params,
            &pk,
            &[circuit],
            &[instances.as_slice()],
            rng,
            &mut transcript,
        )
        .expect("proof generation should not fail");
        let proof = transcript.finalize();
        end_timer!(start2);

        // Bench verification time
        let start3 = start_timer!(|| "MPT verification");
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
            &[instances.as_slice()],
            &mut verifier_transcript,
        )
        .expect("failed to verify bench circuit");
        end_timer!(start3);
    }
}
