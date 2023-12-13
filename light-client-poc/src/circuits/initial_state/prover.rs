use std::time::Instant;

use halo2_proofs::{dev::MockProver, halo2curves::bn256::{Fr, G1Affine, Bn256}, transcript::{Blake2bWrite, Challenge255, TranscriptWriterBuffer, Blake2bRead, TranscriptReadBuffer}, poly::{kzg::{commitment::{KZGCommitmentScheme, ParamsVerifierKZG, ParamsKZG}, multiopen::{ProverSHPLONK, VerifierSHPLONK}, strategy::SingleStrategy}, commitment::ParamsProver}, plonk::{create_proof, VerifyingKey, keygen_vk, keygen_pk, Circuit, verify_proof}};
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
use zkevm_circuits::mpt_circuit::MPTCircuitParams;
use super::{InitialStateCircuit, circuit::STMHelper };
use eyre::{eyre, Result};

pub struct VerifierInput {
    circuit_params: MPTCircuitParams,
    verifier_params: ParamsVerifierKZG<Bn256>,
    vk: VerifyingKey<G1Affine>,
    proof: Vec<u8>,
    public_inputs: Vec<Fr>,
}

impl InitialStateCircuit<Fr> {
    pub fn assert_satisfied(&self) {
        let num_rows: usize = self
            .mpt_circuit
            .nodes
            .iter()
            .map(|node| node.values.len())
            .sum();

        let hash = self.lc_witness.initial_values_hash();
        let prover =
            MockProver::<Fr>::run(self.degree as u32, self, vec![vec![hash.lo(), hash.hi()]]).unwrap();
        prover.assert_satisfied_at_rows_par(0..num_rows, 0..num_rows);
    }
    pub fn gen_pk_and_prove(self) -> Result<VerifierInput> {
        let mut rng = ChaCha20Rng::seed_from_u64(42);

        let start = Instant::now();

        let general_params = ParamsKZG::<Bn256>::setup(self.degree as u32, &mut rng);
        let verifier_params: ParamsVerifierKZG<Bn256> = general_params.verifier_params().clone();

        // Initialize the proving key
        let vk = keygen_vk(&general_params, &self).expect("keygen_vk should not fail");
        let pk = keygen_pk(&general_params, vk.clone(), &self).expect("keygen_pk should not fail");

        println!("key generation time: {:?}", start.elapsed());

        let rng = ChaCha20Rng::seed_from_u64(42);

        // Create a proof
        let mut transcript = Blake2bWrite::<_, G1Affine, Challenge255<_>>::init(vec![]);

        let hash = self.lc_witness.initial_values_hash();
        let public_inputs = vec![hash.lo(), hash.hi()];

        let circuit_params = self.params().clone();

        // Bench proof generation time
        let start = Instant::now();
        create_proof::<
            KZGCommitmentScheme<Bn256>,
            ProverSHPLONK<'_, Bn256>,
            Challenge255<G1Affine>,
            ChaCha20Rng,
            Blake2bWrite<Vec<u8>, G1Affine, Challenge255<G1Affine>>,
            InitialStateCircuit<Fr>,
        >(
            &general_params,
            &pk,
            &[self],
            &[&[&public_inputs]],
            rng,
            &mut transcript,
        )?;

        let proof = transcript.finalize();
        println!("proof generation time: {:?}", start.elapsed());

        Ok(VerifierInput {
            circuit_params,
            verifier_params,
            vk,
            proof,
            public_inputs,
        })
    }

    pub fn verify(input: VerifierInput) -> Result<bool> {
        let VerifierInput {
            circuit_params,
            verifier_params,
            vk,
            proof,
            public_inputs,
        } = input;

        let mut verifier_transcript = Blake2bRead::<_, G1Affine, Challenge255<_>>::init(&proof[..]);
        let strategy = SingleStrategy::new(&verifier_params);

        let start = Instant::now();
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

        println!("verification time: {:?}", start.elapsed());

        Ok(result.is_ok())
    }

    // Sense keccak: Proof: 147k
    // Amb keccak: Proof: 250k

    pub fn assert_real_prover(self) -> Result<()> {
        let input = self.gen_pk_and_prove()?;
        let result = Self::verify(input)?;
        if !result {
            return Err(eyre!("proof verification failed"));
        }
        Ok(())
    }
}
