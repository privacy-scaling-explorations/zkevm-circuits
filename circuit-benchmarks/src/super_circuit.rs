//! SuperCircuit circuit benchmarks

#[cfg(test)]
mod tests {
    use crate::bench_params::DEGREE;
    use ark_std::{end_timer, start_timer};
    use eth_types::{address, bytecode, geth_types::GethData, Word};
    use ethers_signers::{LocalWallet, Signer};
    use halo2_proofs::plonk::{create_proof, keygen_pk, keygen_vk, verify_proof, SingleVerifier};
    use halo2_proofs::{
        pairing::bn256::{Bn256, G1Affine},
        poly::commitment::{Params, ParamsVerifier},
        transcript::{Blake2bRead, Blake2bWrite, Challenge255},
    };
    use mock::{TestContext, MOCK_CHAIN_ID};
    use rand::SeedableRng;
    use rand_chacha::ChaChaRng;
    use std::collections::HashMap;
    use zkevm_circuits::super_circuit::SuperCircuit;

    use halo2_proofs::pairing::bn256::Fr;

    #[cfg_attr(not(feature = "benches"), ignore)]
    #[test]
    fn bench_super_circuit_prover() {
        let mut rng = ChaChaRng::seed_from_u64(2);

        let chain_id = (*MOCK_CHAIN_ID).as_u64();

        let bytecode = bytecode! {
            STOP
        };

        let wallet_a = LocalWallet::new(&mut rng).with_chain_id(chain_id);

        let addr_a = wallet_a.address();
        let addr_b = address!("0x000000000000000000000000000000000000BBBB");

        let mut wallets = HashMap::new();
        wallets.insert(wallet_a.address(), wallet_a);

        let mut block: GethData = TestContext::<2, 1>::new(
            None,
            |accs| {
                accs[0]
                    .address(addr_b)
                    .balance(Word::from(1u64 << 20))
                    .code(bytecode);
                accs[1].address(addr_a).balance(Word::from(1u64 << 20));
            },
            |mut txs, accs| {
                txs[0]
                    .from(accs[1].address)
                    .to(accs[0].address)
                    .gas(Word::from(1_000_000u64));
            },
            |block, _tx| block.number(0xcafeu64),
        )
        .unwrap()
        .into();

        block.sign(&wallets);

        let (_, circuit, instance) =
            SuperCircuit::<_, 1, 32>::build(block, ChaChaRng::seed_from_u64(2));
        let instance_refs: Vec<&[Fr]> = instance.iter().map(|v| &v[..]).collect();

        // Bench setup generation
        let setup_message = format!("Setup generation with degree = {}", DEGREE);
        let start1 = start_timer!(|| setup_message);
        let general_params: Params<G1Affine> =
            Params::<G1Affine>::unsafe_setup::<Bn256>(DEGREE.try_into().unwrap());
        let verifier_params: ParamsVerifier<Bn256> =
            general_params.verifier((1 << DEGREE) - 64).unwrap();
        end_timer!(start1);

        // Initialize the proving key
        let vk = keygen_vk(&general_params, &circuit).expect("keygen_vk should not fail");
        let pk = keygen_pk(&general_params, vk, &circuit).expect("keygen_pk should not fail");

        // Create a proof
        let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);

        // Bench proof generation time
        let proof_message = format!("State Proof generation with {} degree", DEGREE);
        let start2 = start_timer!(|| proof_message);
        create_proof(
            &general_params,
            &pk,
            &[circuit],
            &[&instance_refs],
            rng,
            &mut transcript,
        )
        .expect("proof generation should not fail");
        let proof = transcript.finalize();
        end_timer!(start2);

        // Bench verification time
        let start3 = start_timer!(|| "State Proof verification");
        let mut verifier_transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
        let strategy = SingleVerifier::new(&verifier_params);

        verify_proof(
            &verifier_params,
            pk.get_vk(),
            strategy,
            &[&instance_refs],
            &mut verifier_transcript,
        )
        .expect("failed to verify bench circuit");
        end_timer!(start3);
    }
}
