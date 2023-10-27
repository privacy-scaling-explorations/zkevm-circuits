use eyre::Result;
use halo2_proofs::{dev::MockProver, halo2curves::bn256::Fr, plonk::Circuit, SerdeFormat};
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
use std::time::Instant;

use crate::circuits::state_update::PublicInputs;
use halo2_proofs::{
    halo2curves::bn256::{Bn256, G1Affine},
    plonk::{create_proof, keygen_pk, keygen_vk, verify_proof, ProvingKey},
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

use super::StateUpdateCircuit;

#[derive(Clone)]
pub struct StateUpdateCircuitKeys {
    general_params: ParamsKZG<Bn256>,
    verifier_params: ParamsVerifierKZG<Bn256>,
    pk: ProvingKey<G1Affine>,
}

impl StateUpdateCircuitKeys {
    pub fn new(circuit: &StateUpdateCircuit<Fr>) -> StateUpdateCircuitKeys {
        let mut rng = ChaCha20Rng::seed_from_u64(42);

        let start = Instant::now();

        // let circuit = StateUpdateCircuit::default();

        let general_params = ParamsKZG::<Bn256>::setup(circuit.degree as u32, &mut rng);
        let verifier_params: ParamsVerifierKZG<Bn256> = general_params.verifier_params().clone();

        // Initialize the proving key
        let vk = keygen_vk(&general_params, circuit).expect("keygen_vk should not fail");
        let pk = keygen_pk(&general_params, vk, circuit).expect("keygen_pk should not fail");

        println!("key generation time: {:?}", start.elapsed());

        StateUpdateCircuitKeys {
            general_params,
            verifier_params,
            pk,
        }
    }

    pub fn serialize(&self) -> Result<Vec<u8>> {
        let mut buffer = Vec::new();
        self.general_params
            .write_custom(&mut buffer, SerdeFormat::RawBytes)?;
        self.verifier_params
            .write_custom(&mut buffer, SerdeFormat::RawBytes)?;
        self.pk.write(&mut buffer, SerdeFormat::RawBytes).unwrap();
        Ok(buffer)
    }

    pub fn unserialize(mut bytes: &[u8]) -> Result<Self> {
        let general_params = ParamsKZG::<Bn256>::read_custom(&mut bytes, SerdeFormat::RawBytes)?;
        let verifier_params =
            ParamsVerifierKZG::<Bn256>::read_custom(&mut bytes, SerdeFormat::RawBytes)?;
        let circuit_params = StateUpdateCircuit::<Fr>::default().params();
        let pk = ProvingKey::<G1Affine>::read::<_, StateUpdateCircuit<Fr>>(
            &mut bytes,
            SerdeFormat::RawBytes,
            circuit_params,
        )?;
        Ok(Self {
            general_params,
            verifier_params,
            pk,
        })
    }
}

impl StateUpdateCircuit<Fr> {
    pub fn assert_satisfied(&self) {
        let num_rows: usize = self
            .mpt_circuit
            .nodes
            .iter()
            .map(|node| node.values.len())
            .sum();

        let public_inputs: PublicInputs<Fr> = (&self.lc_witness).into();

        for (i, input) in public_inputs.iter().enumerate() {
            println!("input[{i:}]: {input:?}");
        }

        let prover =
            MockProver::<Fr>::run(self.degree as u32, self, vec![public_inputs.0]).unwrap();
        prover.assert_satisfied_at_rows_par(0..num_rows, 0..num_rows);
    }

    pub fn prove(self, keys: &StateUpdateCircuitKeys) -> Result<Vec<u8>> {
        let rng = ChaCha20Rng::seed_from_u64(42);

        // Create a proof
        let mut transcript = Blake2bWrite::<_, G1Affine, Challenge255<_>>::init(vec![]);

        let public_inputs: PublicInputs<Fr> = (&self.lc_witness).into();

        // Bench proof generation time
        let start = Instant::now();
        create_proof::<
            KZGCommitmentScheme<Bn256>,
            ProverSHPLONK<'_, Bn256>,
            Challenge255<G1Affine>,
            ChaCha20Rng,
            Blake2bWrite<Vec<u8>, G1Affine, Challenge255<G1Affine>>,
            StateUpdateCircuit<Fr>,
        >(
            &keys.general_params,
            &keys.pk,
            &[self],
            &[&[&public_inputs]],
            rng,
            &mut transcript,
        )?;

        let proof = transcript.finalize();

        println!("proof generation time: {:?}", start.elapsed());

        Ok(proof)
    }

    pub fn verify(proof: &[u8], public_inputs: &[Fr], keys: &StateUpdateCircuitKeys) -> Result<()> {
        // Bench verification time
        let start = Instant::now();
        let mut verifier_transcript = Blake2bRead::<_, G1Affine, Challenge255<_>>::init(proof);
        let strategy = SingleStrategy::new(&keys.general_params);

        verify_proof::<
            KZGCommitmentScheme<Bn256>,
            VerifierSHPLONK<'_, Bn256>,
            Challenge255<G1Affine>,
            Blake2bRead<&[u8], G1Affine, Challenge255<G1Affine>>,
            SingleStrategy<'_, Bn256>,
        >(
            &keys.verifier_params,
            keys.pk.get_vk(),
            strategy,
            &[&[public_inputs]],
            &mut verifier_transcript,
        )?;

        println!("verification time: {:?}", start.elapsed());

        Ok(())
    }
}
