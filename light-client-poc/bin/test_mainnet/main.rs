use std::{net::TcpListener, process::Command, thread, time::Duration};

use ethers::{prelude::*, types::transaction::eip2930::AccessList};
use eyre::Result;
use halo2_proofs::halo2curves::bn256::Fr;

use light_client_poc::{
    circuits::initial_state::InitialStateCircuit,
    witness::{utils::new_eth_signer_client, Witness},
};

pub const CACHE_URL: &str = "http://localhost:3000";

async fn mock_prove(
    block_no: u64,
    access_list: &str,
    degree: usize,
    max_proof_count: usize,
) -> Result<InitialStateCircuit<Fr>> {
    let provider = CACHE_URL;
    println!("provider: {}", provider);

    const PVK: &str = "7ccb34dc5fd31fd0aa7860de89a4adc37ccb34dc5fd31fd0aa7860de89a4adc3";
    let client = new_eth_signer_client(provider, PVK).await?;

    let access_list: AccessList = serde_json::from_str(access_list)?;

    let witness = Witness::<Fr>::build(
        client.clone(),
        provider,
        U64::from(block_no),
        Some(access_list),
        true,
    )
    .await?
    .unwrap();

    let circuit = InitialStateCircuit::new(witness, degree, max_proof_count)?;
    circuit.assert_satisfied();

    Ok(circuit)
}

async fn run_107() -> Result<()> {
    let max_proof_count = 30;
    let circuit = mock_prove(107, include_str!("al/107.json"), 16, max_proof_count).await?;

    circuit.assert_real_prover()?;

    Ok(())
}

async fn run_tests() -> Result<()> {
    let max_proof_count = 30;
    mock_prove(436875, include_str!("al/436875.json"), 16, max_proof_count).await?;
    mock_prove(107, include_str!("al/107.json"), 16, max_proof_count).await?;
    mock_prove(
        2000007,
        include_str!("al/2000007.json"),
        16,
        max_proof_count,
    )
    .await?;
    mock_prove(
        2000004,
        include_str!("al/2000004.json"),
        16,
        max_proof_count,
    )
    .await?;
    mock_prove(
        2000070,
        include_str!("al/2000070.json"),
        16,
        max_proof_count,
    )
    .await?;
    mock_prove(
        18363441,
        include_str!("al/18363441.json"),
        16,
        max_proof_count,
    )
    .await?;
    mock_prove(
        18363442,
        include_str!("al/18363442.json"),
        16,
        max_proof_count,
    )
    .await?;
    mock_prove(
        18363443,
        include_str!("al/18363443.json"),
        16,
        max_proof_count,
    )
    .await?;
    mock_prove(
        18363444,
        include_str!("al/18363444.json"),
        16,
        max_proof_count,
    )
    .await?;
    mock_prove(
        18363445,
        include_str!("al/18363445.json"),
        16,
        max_proof_count,
    )
    .await?;

    Ok(())
}

async fn start_web3_proxy() -> Result<()> {
    let result = Command::new("cargo")
        .arg("build")
        .arg("--bin")
        .arg("web3_cache")
        .arg("--release")
        .output()?;

    assert!(result.status.success());

    Command::new("cargo")
        .arg("run")
        .arg("--bin")
        .arg("web3_cache")
        .arg("--release")
        .spawn()?;

    thread::sleep(Duration::from_secs(1));
    Ok(())
}

#[tokio::main]
async fn main() -> Result<()> {
    match TcpListener::bind(("127.0.0.1", 3000)) {
        Ok(_) => (),
        Err(_) => start_web3_proxy().await?,
    }

    run_107().await?;

    // return Ok(());

    run_tests().await.unwrap();

    Ok(())
}
