#[macro_use]
extern crate lazy_static;

mod cache;
mod circuit;

use std::time::Duration;

use ethers::{prelude::*, types::transaction::eip2930::AccessList};
use eyre::Result;
use halo2_proofs::halo2curves::bn256::Fr;

use circuit::{state_update::StateUpdateCircuit, witness::Witness};

async fn mock_prove(block_no: u64, access_list: &str) -> Result<()> {
    let provider_url = "http://localhost:3000";

    let access_list: AccessList = serde_json::from_str(access_list)?;
    let proof_count = access_list.0.len() * 3
        + access_list
            .0
            .iter()
            .map(|k| k.storage_keys.len())
            .sum::<usize>();

    let witness = Witness::<Fr>::build(provider_url, U64::from(block_no), Some(access_list), true)
        .await?
        .unwrap();

    let circuit = StateUpdateCircuit::new(witness, 16, 2 * proof_count)?;
    circuit.assert_satisfied();
    Ok(())
}

#[tokio::main]
async fn main() -> Result<()> {
    cache::load().await?;

    let _cache = tokio::task::spawn(cache::start());

    tokio::time::sleep(Duration::from_millis(500)).await;

    let mut files: Vec<_> = glob::glob("access-lists/*.json")
        .unwrap()
        .filter_map(|v| v.ok())
        .map(|v| {
            let block = v
                .file_name()
                .unwrap()
                .to_str()
                .unwrap()
                .strip_suffix(".json")
                .unwrap();
            let block: u64 = str::parse(block).unwrap();
            (block, v)
        })
        .collect();

    files.sort_by(|(a, _), (b, _)| a.cmp(b));

    for (block_no, file) in files {
        let json = std::fs::read_to_string(&file)?;
        mock_prove(block_no, &json).await?;
    }

    Ok(())
}
