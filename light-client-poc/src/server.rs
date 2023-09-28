use eth_types::{Address, U64};
use ethers::{
    providers::Middleware,
    types::{transaction::eip2718::TypedTransaction, TransactionRequest},
};
use eyre::Result;
use halo2_proofs::halo2curves::bn256::Fr;
use std::{collections::HashMap, str::FromStr, time::SystemTime};

use crate::{
    circuit::{
        LightClientCircuit, LightClientCircuitKeys, DEFAULT_CIRCUIT_DEGREE, DEFAULT_MAX_PROOF_COUNT,
    },
    witness::{LightClientWitness, PublicInputs},
};

pub async fn serve() -> Result<()> {
    const PROVIDER_URL: &str = "http://localhost:8545";
    const PVK: &str = "7ccb34dc5fd31fd0aa7860de89a4adc37ccb34dc5fd31fd0aa7860de89a4adc3";

    let client = crate::utils::new_eth_signer_client(PROVIDER_URL, PVK).await?;

    let mut keys = None;

    let mut storage = HashMap::new();
    let mut last_processed_block = U64::from(1);

    loop {
        let current_block = client.get_block_number().await.unwrap();
        if current_block <= last_processed_block {
            std::thread::sleep(std::time::Duration::from_secs(1));
            let to = format!(
                "0x{:040x}",
                SystemTime::now()
                    .duration_since(SystemTime::UNIX_EPOCH)
                    .unwrap()
                    .as_millis()
            );
            let tx = TransactionRequest::new()
                .to(Address::from_str(&to).unwrap())
                .value(1);

            client
                .send_transaction(TypedTransaction::Legacy(tx), None)
                .await?
                .await?;
            continue;
        }

        println!("Processing block {}", last_processed_block);

        last_processed_block = last_processed_block + 1;

        let witness = LightClientWitness::<Fr>::build(
            client.clone(),
            PROVIDER_URL,
            last_processed_block,
            None,
        )
        .await?;

        let Some(witness) = witness else {
                continue;
            };

        let public_inputs: PublicInputs<Fr> = (&witness.lc_witness).into();
        let circuit =
            LightClientCircuit::new(witness, DEFAULT_CIRCUIT_DEGREE, DEFAULT_MAX_PROOF_COUNT)?;

        println!("trns: {:#?}", circuit.transforms);

        circuit.assert_satisfied();

        if keys.is_none() {
            keys = Some(LightClientCircuitKeys::new(&circuit));
        }

        let proof = circuit.prove(keys.as_ref().unwrap())?;
        LightClientCircuit::verify(&proof, &public_inputs, keys.as_ref().unwrap())?;

        storage.insert(last_processed_block, proof);
    }
}
