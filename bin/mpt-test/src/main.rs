#[macro_use]
extern crate lazy_static;

mod cache;
mod circuit;

use ethers::{prelude::*, types::transaction::eip2930::AccessList};
use eyre::Result;
use halo2_proofs::halo2curves::bn256::Fr;

use circuit::{state_update::StateUpdateCircuit, witness::Witness};

// test the StateUpdate circuit with a mock prover
async fn mock_prove(block_no: u64, access_list: &str) -> Result<()> {
    let provider_url = "http://localhost:3000";

    let access_list: AccessList = serde_json::from_str(access_list)?;
    let proof_count = 2 * access_list.0.len() * 3
        + 2 * access_list
            .0
            .iter()
            .map(|k| k.storage_keys.len())
            .sum::<usize>();

    let max_nodes = 1000000;
    let degree = 20;

    let witness = Witness::<Fr>::build(provider_url, U64::from(block_no), Some(access_list), true)
        .await?
        .unwrap();

    let circuit = StateUpdateCircuit::new(witness, degree, max_nodes, proof_count + 10)?;
    circuit.assert_satisfied();
    Ok(())
}

#[tokio::main]
async fn main() -> Result<()> {
    // load the cache file, if exists
    cache::load().await?;

    // start the cache server
    let _handle = tokio::task::spawn(cache::start());

    // read all the access list files, sorting them by block number
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

    // prove each block
    for (block_no, file) in files {
        let json = std::fs::read_to_string(&file)?;
        mock_prove(block_no, &json).await?;
    }

    Ok(())
}
