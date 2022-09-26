//! State circuit benchmarks

#[cfg(test)]
mod tests {
    use ark_std::{end_timer, start_timer};
    use eth_types::geth_types::Transaction;
    use eth_types::Word;
    use ethers_core::types::{NameOrAddress, TransactionRequest};
    use ethers_signers::{LocalWallet, Signer};
    use halo2_proofs::arithmetic::Field;
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
    use rand::{CryptoRng, Rng, SeedableRng};
    use rand_chacha::ChaCha20Rng;
    use rand_xorshift::XorShiftRng;
    use std::env::var;
    use zkevm_circuits::pi_circuit::{
        raw_public_inputs_col, PiCircuit, PublicData, BLOCK_LEN, EXTRA_LEN, TX_LEN,
    };
    use zkevm_circuits::util::random_linear_combine_word as rlc;

    #[cfg_attr(not(feature = "benches"), ignore)]
    #[test]
    fn bench_pi_circuit_prover() {
        let degree: u32 = var("DEGREE")
            .unwrap_or("18".to_string())
            .parse()
            .expect("Cannot parse DEGREE env var as u32");

        const MAX_TXS: usize = 10;

        const MAX_CALLDATA: usize = 128;

        // Initialize the polynomial commitment parameters
        let mut rng = XorShiftRng::from_seed([
            0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        // Create the circuit
        let randomness = <Fr as Field>::random(&mut rng);
        let public_data = fillup_publicdata::<MAX_TXS, MAX_CALLDATA>();

        let rlc_rpi_col =
            raw_public_inputs_col::<Fr, MAX_TXS, MAX_CALLDATA>(&public_data, randomness);
        assert_eq!(
            rlc_rpi_col.len(),
            BLOCK_LEN + 1 + EXTRA_LEN + 3 * (TX_LEN * MAX_TXS + 1 + MAX_CALLDATA)
        );

        // Computation of raw_pulic_inputs
        let rlc_rpi = rlc_rpi_col
            .iter()
            .rev()
            .fold(Fr::zero(), |acc, val| acc * randomness + val);

        let public_inputs = vec![
            randomness,
            rlc_rpi,
            Fr::from(public_data.extra.chain_id.as_u64()),
            rlc(
                public_data.extra.eth_block.state_root.to_fixed_bytes(),
                randomness,
            ),
            rlc(public_data.prev_state_root.to_fixed_bytes(), randomness),
        ];

        let circuit = PiCircuit::<Fr, MAX_TXS, MAX_CALLDATA> {
            randomness: randomness,
            rand_rpi: randomness.clone(),
            public_data: public_data,
        };

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
        let proof_message = format!("PI_circuit Proof generation with {} rows", degree);
        let start2 = start_timer!(|| proof_message);
        create_proof::<
            KZGCommitmentScheme<Bn256>,
            ProverSHPLONK<'_, Bn256>,
            Challenge255<G1Affine>,
            XorShiftRng,
            Blake2bWrite<Vec<u8>, G1Affine, Challenge255<G1Affine>>,
            PiCircuit<Fr, MAX_TXS, MAX_CALLDATA>,
        >(
            &general_params,
            &pk,
            &[circuit],
            &[&[public_inputs.as_slice()][..]][..],
            rng,
            &mut transcript,
        )
        .expect("proof generation should not fail");
        let proof = transcript.finalize();
        end_timer!(start2);

        // Bench verification time
        let start3 = start_timer!(|| "PI_circuit Proof verification");
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
            &[&[public_inputs.as_slice()][..]][..],
            &mut verifier_transcript,
        )
        .expect("failed to verify bench circuit");
        end_timer!(start3);
    }

    fn fillup_publicdata<const MAX_TXS: usize, const MAX_CALLDATA: usize>() -> PublicData {
        let mut rng = ChaCha20Rng::seed_from_u64(2);

        let mut public_data = PublicData::default();
        let chain_id = 1337u64;
        public_data.extra.chain_id = Word::from(chain_id);

        let n_tx = MAX_TXS;
        for _ in 0..n_tx {
            public_data.txs.push(rand_tx(&mut rng, chain_id));
        }

        public_data
    }

    /// generate rand tx for pi circuit
    fn rand_tx<R: Rng + CryptoRng>(mut rng: R, chain_id: u64) -> Transaction {
        let wallet0 = LocalWallet::new(&mut rng).with_chain_id(chain_id);
        let wallet1 = LocalWallet::new(&mut rng).with_chain_id(chain_id);
        let from = wallet0.address();
        let to = wallet1.address();
        let data = b"hello";
        let tx = TransactionRequest::new()
            .chain_id(chain_id)
            .from(from)
            .to(to)
            .nonce(3)
            .value(1000)
            .data(data)
            .gas(500_000)
            .gas_price(1234);
        let sig = wallet0.sign_transaction_sync(&tx.clone().into());
        let to = tx.to.map(|to| match to {
            NameOrAddress::Address(a) => a,
            _ => unreachable!(),
        });
        Transaction {
            from: tx.from.unwrap(),
            to,
            gas_limit: tx.gas.unwrap(),
            gas_price: tx.gas_price.unwrap(),
            value: tx.value.unwrap(),
            call_data: tx.data.unwrap(),
            nonce: tx.nonce.unwrap(),
            v: sig.v,
            r: sig.r,
            s: sig.s,
            ..Transaction::default()
        }
    }
}
