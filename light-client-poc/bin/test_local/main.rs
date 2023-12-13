use ethers::prelude::*;
use eyre::Result;
use halo2_proofs::halo2curves::bn256::Fr;
use std::sync::Arc;

use light_client_poc::{
    circuits::initial_state::InitialStateCircuit,
    witness::{new_eth_signer_client, MM, Witness},
};


mod contract;

const PVK: &str = "7ccb34dc5fd31fd0aa7860de89a4adc37ccb34dc5fd31fd0aa7860de89a4adc3";
const PROVIDER_URL: &str = "http://localhost:8545";

async fn local_test_proof(
    test: &str,
    client: &Arc<MM>,
    provider_url: &str,
    recipt: &TransactionReceipt,
) -> Result<()> {
    println!("Running test {}", test);

    let witness = Witness::<Fr>::build(
        client.clone(),
        provider_url,
        recipt.block_number.unwrap(),
        None,
        true,
    )
    .await?
    .unwrap();

    let circuit = InitialStateCircuit::new(witness, 17, 20)?;

    circuit.assert_satisfied();

    Ok(())
}

async fn run_localnode_test() -> Result<()> {
    let client = new_eth_signer_client(PROVIDER_URL, PVK).await?;

    // test contract creation
    let contract = contract::Contract::deploy(client.clone()).await?;
    local_test_proof(
        "contract creation",
        &client,
        PROVIDER_URL,
        &contract.receipt,
    )
    .await?;

    // test set value
    let receipt = contract.set(0xad41a.into(), 0xcafe.into()).await?;
    local_test_proof("test set slot", &client, PROVIDER_URL, &receipt).await?;

    // test unset value
    let receipt = contract.set(0xad41a.into(), 0.into()).await?;
    local_test_proof("test remove slot", &client, PROVIDER_URL, &receipt).await?;

    Ok(())
}

#[tokio::main]
async fn main() {
    run_localnode_test().await.unwrap();
}