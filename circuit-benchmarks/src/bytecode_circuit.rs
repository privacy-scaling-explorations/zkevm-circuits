//! State circuit benchmarks

#[cfg(test)]
mod tests {
    use ark_std::{end_timer, start_timer};
    use bus_mapping::evm::OpcodeId;
    use eth_types::Field;
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
    use rand::SeedableRng;
    use rand_xorshift::XorShiftRng;
    use std::env::var;
    use zkevm_circuits::bytecode_circuit::bytecode_unroller::{unroll, UnrolledBytecode};
    use zkevm_circuits::bytecode_circuit::dev::{get_randomness, BytecodeCircuitTester};

    #[cfg_attr(not(feature = "benches"), ignore)]
    #[test]
    fn bench_bytecode_circuit_prover() {
        let degree: u32 = var("DEGREE")
            .unwrap_or_else(|_| "12".to_string())
            .parse()
            .expect("Cannot parse DEGREE env var as u32");

        let bytecodes_len: u32 = var("BTYECODES_LEN")
            .unwrap_or_else(|_| "1".to_string())
            .parse()
            .expect("Cannot parse BTYECODES_LEN env var as u32");

        let randomness = get_randomness();
        let num_rows = 1 << degree;
        const NUM_BLINDING_ROWS: usize = 7 - 1;
        let max_bytecode_row_num = num_rows - NUM_BLINDING_ROWS;
        let instance = vec![randomness; max_bytecode_row_num];

        // Create the circuit
        let bytecode_circuit = BytecodeCircuitTester::<Fr>::new(
            fillup_codebytes(bytecodes_len, max_bytecode_row_num as u32, randomness),
            2usize.pow(degree),
            randomness,
        );

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
        let vk = keygen_vk(&general_params, &bytecode_circuit).expect("keygen_vk should not fail");
        let pk =
            keygen_pk(&general_params, vk, &bytecode_circuit).expect("keygen_pk should not fail");
        // Create a proof
        let mut transcript = Blake2bWrite::<_, G1Affine, Challenge255<_>>::init(vec![]);

        // Bench proof generation time
        let proof_message = format!("Bytecode Proof generation with {} rows", degree);
        let start2 = start_timer!(|| proof_message);
        create_proof::<
            KZGCommitmentScheme<Bn256>,
            ProverSHPLONK<'_, Bn256>,
            Challenge255<G1Affine>,
            XorShiftRng,
            Blake2bWrite<Vec<u8>, G1Affine, Challenge255<G1Affine>>,
            BytecodeCircuitTester<Fr>,
        >(
            &general_params,
            &pk,
            &[bytecode_circuit],
            &[&[instance.as_slice()][..]][..],
            rng,
            &mut transcript,
        )
        .expect("proof generation should not fail");
        let proof = transcript.finalize();
        end_timer!(start2);

        // Bench verification time
        let start3 = start_timer!(|| "Bytecode Proof verification");
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
            &[&[instance.as_slice()][..]][..],
            &mut verifier_transcript,
        )
        .expect("failed to verify bench circuit");
        end_timer!(start3);
    }

    fn fillup_codebytes<F: Field>(
        bytecodes_len: u32,
        max_bytecode_row_num: u32,
        randomness: F,
    ) -> Vec<UnrolledBytecode<F>> {
        if bytecodes_len == 0 {
            vec![]
        } else {
            let codebytes_size: usize = (max_bytecode_row_num / bytecodes_len) as usize;
            assert!(codebytes_size >= 1);
            (0..max_bytecode_row_num)
                .collect::<Vec<u32>>()
                .chunks(codebytes_size)
                .map(|idx_range| {
                    idx_range
                        .iter()
                        .filter_map(|v| OpcodeId::try_from(*v as u8).ok())
                        .map(|opcode| opcode.as_u8())
                        .collect::<Vec<u8>>()
                })
                .map(|bytes| unroll(bytes, randomness))
                .collect()
        }
    }
}
