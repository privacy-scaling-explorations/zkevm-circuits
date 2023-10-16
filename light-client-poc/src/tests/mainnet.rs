#[cfg(test)]
mod test {
    use ethers::{
        prelude::*,
        types::transaction::eip2930::AccessList,
    };
    use eyre::Result;
    use halo2_proofs::halo2curves::bn256::Fr;

    use crate::{circuit::{
        PublicInputs, StateUpdateCircuit, StateUpdateCircuitKeys, StateUpdateWitness,
        DEFAULT_CIRCUIT_DEGREE, DEFAULT_MAX_PROOF_COUNT,
    }, tests::cache::ORACLE_URL};

    #[ctor::ctor]
    fn init_tests() {
        // Enable RUST_LOG during tests
        env_logger::Builder::from_env(env_logger::Env::default().default_filter_or("error")).init();
    }

    async fn mock_prove(
        block_no: u64,
        access_list: &str,
        degree: usize,
        max_proof_count: usize,
    ) -> Result<StateUpdateCircuit<Fr>> {
        const PVK: &str = "7ccb34dc5fd31fd0aa7860de89a4adc37ccb34dc5fd31fd0aa7860de89a4adc3";
        let client = crate::utils::new_eth_signer_client(&ORACLE_URL, PVK).await?;

        let access_list : AccessList = serde_json::from_str(access_list)?;

        let witness = StateUpdateWitness::<Fr>::build(
            client.clone(),
            ORACLE_URL,
            U64::from(block_no),
            Some(access_list),
        )
        .await?
        .unwrap();

        println!("trns: {:#?}", witness.transforms);

        let circuit = StateUpdateCircuit::new(witness, degree, max_proof_count)?;

        circuit.assert_satisfied();

        Ok(circuit)
    }

    #[ignore]
    #[tokio::test]
    async fn test_block_436875() -> Result<()> {
        mock_prove(436875, include_str!("al/436875.json"), 16, DEFAULT_MAX_PROOF_COUNT).await?;
        Ok(())
    }

    #[ignore]
    #[tokio::test]
    async fn test_block_107() -> Result<()> {
        mock_prove(107, include_str!("al/107.json"), 16, DEFAULT_MAX_PROOF_COUNT).await?;
        Ok(())
    }

    #[ignore]
    #[tokio::test]
    async fn test_reuse_proving_keys() -> Result<()> {

        let block_no = 107;
        let access_list = include_str!("al/107.json");

        let circuit = mock_prove(block_no, access_list, 15, DEFAULT_MAX_PROOF_COUNT).await?;
        let public_inputs: PublicInputs<Fr> = (&circuit.lc_witness).into();

        let keys = StateUpdateCircuitKeys::new(&circuit);
        let proof = circuit.prove(&keys)?;

        let keys = StateUpdateCircuitKeys::unserialize(&keys.serialize()?)?;

        StateUpdateCircuit::verify(&proof, &public_inputs, &keys)?;

        let block_no = 436875;
        let access_list = include_str!("al/436875.json");

        let circuit = mock_prove(
            block_no,
            access_list,
            DEFAULT_CIRCUIT_DEGREE,
            DEFAULT_MAX_PROOF_COUNT,
        )
        .await?;
        let mut public_inputs: PublicInputs<Fr> = (&circuit.lc_witness).into();

        let proof = circuit.prove(&keys)?;

        StateUpdateCircuit::verify(&proof, &public_inputs, &keys)?;

        // ok, check also modifying public inputs to check if fails

        for i in 0..public_inputs.len() {
            public_inputs.0[i] += Fr::one();
            let _ = StateUpdateCircuit::verify(&proof, &public_inputs, &keys)
                .err()
                .unwrap();
            println!("public input: {}", i);
            public_inputs.0[i] -= Fr::one();
        }

        Ok(())
    }

    #[ignore]
    #[tokio::test]
    async fn test_block_2000007() -> Result<()> {
        mock_prove(2000007, include_str!("al/2000007.json"), 16, DEFAULT_MAX_PROOF_COUNT).await?;
        Ok(())
    }

    #[ignore]
    #[tokio::test]
    async fn test_block_2000004() -> Result<()> {
        mock_prove(2000004, include_str!("al/2000004.json"), 16, DEFAULT_MAX_PROOF_COUNT).await?;
        Ok(())
    }

    #[ignore]
    #[tokio::test]
    async fn test_block_2000070() -> Result<()> {
        mock_prove(2000070, include_str!("al/2000070.json"), 16, DEFAULT_MAX_PROOF_COUNT).await?;
        Ok(())
    }
    #[ignore]
    #[tokio::test]
    async fn test_block_18363441() -> Result<()> {
        mock_prove(18363441, include_str!("al/18363441.json"), 16, DEFAULT_MAX_PROOF_COUNT).await?;
        Ok(())
    }
    #[ignore]
    #[tokio::test]
    async fn test_block_18363442() -> Result<()> {
        mock_prove(18363442, include_str!("al/18363442.json"), 16, DEFAULT_MAX_PROOF_COUNT).await?;
        Ok(())
    }


}
