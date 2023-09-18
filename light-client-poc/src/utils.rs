use ethers::{
    middleware::SignerMiddleware,
    prelude::{k256::ecdsa::SigningKey, *},
    providers::{Http, Middleware, Provider},
    signers::{LocalWallet, Signer},
    utils::format_units,
};
use eyre::Result;
use halo2_proofs::{dev::MockProver, halo2curves::bn256::Fr};

use std::{convert::TryFrom, sync::Arc, time::Duration, collections::HashMap};
use zkevm_circuits::mpt_circuit::witness_row::*;

// #[rustfmt_skip]
#[allow(dead_code)]
pub fn print_nodes(node: &[Node]) {
    for n in node {
        println!("node:");
        if let Some(start) = &n.start {
            println!("   start:");
            println!("      proof_type: {:?}", start.proof_type);
            println!(
                "      disable_preimage_check: {:?}",
                start.disable_preimage_check
            );
        }
        if let Some(extension_branch) = &n.extension_branch {
            println!("   extension_branch:");
            println!("      is_extension: {:?}", extension_branch.is_extension);
            println!(
                "      is_placeholder: {:?}",
                extension_branch.is_placeholder
            );
            println!("      extension:");
            println!(
                "         list_rlp_bytes: {}",
                hex::encode(&extension_branch.extension.list_rlp_bytes)
            );
            println!("      branch:");
            println!(
                "         modified_index: {}",
                extension_branch.branch.modified_index
            );
            println!(
                "         drifted_index: {}",
                extension_branch.branch.drifted_index
            );
            println!(
                "         list_rlp_bytes[0]: {}",
                hex::encode(&extension_branch.branch.list_rlp_bytes[0])
            );
            println!(
                "         list_rlp_bytes[1]: {}",
                hex::encode(&extension_branch.branch.list_rlp_bytes[1])
            );
        }
        if let Some(account) = &n.account {
            println!("   account:");
            println!("       address: {}", hex::encode(&account.address));
            println!("       key: {}", hex::encode(&account.key));
            println!(
                "       list_rlp_bytes[0]: {}",
                hex::encode(&account.list_rlp_bytes[0])
            );
            println!(
                "       list_rlp_bytes[1]: {}",
                hex::encode(&account.list_rlp_bytes[1])
            );
            println!(
                "       value_rlp_bytes[0]: {}",
                hex::encode(&account.value_rlp_bytes[0])
            );
            println!(
                "       value_rlp_bytes[1]: {}",
                hex::encode(&account.value_rlp_bytes[1])
            );
            println!(
                "       value_list_rlp_bytes[0]: {}",
                hex::encode(&account.value_list_rlp_bytes[0])
            );
            println!(
                "       value_list_rlp_bytes[1]: {}",
                hex::encode(&account.value_list_rlp_bytes[1])
            );
            println!(
                "       drifted_rlp_bytes: {}",
                hex::encode(&account.drifted_rlp_bytes)
            );
            println!(
                "       wrong_rlp_bytes: {}",
                hex::encode(&account.wrong_rlp_bytes)
            );
        }

        if let Some(storage) = &n.storage {
            println!("   storage:");
            println!("       address: {}", hex::encode(&storage.address));
            println!("       key: {}", hex::encode(&storage.key));
            println!(
                "       list_rlp_bytes[0]: {}",
                hex::encode(&storage.list_rlp_bytes[0])
            );
            println!(
                "       list_rlp_bytes[1]: {}",
                hex::encode(&storage.list_rlp_bytes[1])
            );
            println!(
                "       value_rlp_bytes[0]: {}",
                hex::encode(&storage.value_rlp_bytes[0])
            );
            println!(
                "       value_rlp_bytes[1]: {}",
                hex::encode(&storage.value_rlp_bytes[1])
            );
            println!(
                "       drifted_rlp_bytes: {}",
                hex::encode(&storage.drifted_rlp_bytes)
            );
            println!(
                "       wrong_rlp_bytes: {}",
                hex::encode(&storage.wrong_rlp_bytes)
            );
        }
        println!("   values:");
        for (idx, value) in n.values.iter().enumerate() {
            println!("      [{}]: {}", idx, hex::encode(value));
        }

        println!("   keccak_data:");
        for (idx, value) in n.keccak_data.iter().enumerate() {
            println!("      [{}]: {}", idx, hex::encode(value));
        }
    }
}

pub fn verify_mpt_witness(nodes: Vec<Node>) -> Result<()> {
    // get the number of rows in the witness
    let num_rows: usize = nodes.iter().map(|node| node.values.len()).sum();

    // populate the keccak data
    let mut keccak_data = vec![];
    for node in nodes.iter() {
        for k in node.keccak_data.iter() {
            keccak_data.push(k.clone());
        }
    }

    // verify the circuit
    let disable_preimage_check = nodes[0].start.clone().unwrap().disable_preimage_check;
    let degree = 14;
    let circuit = zkevm_circuits::mpt_circuit::MPTCircuit::<Fr> {
        nodes,
        keccak_data,
        degree,
        disable_preimage_check,
        _marker: std::marker::PhantomData,
    };

    let prover = MockProver::<Fr>::run(degree as u32, &circuit, vec![]).unwrap();
    assert_eq!(prover.verify_at_rows(0..num_rows, 0..num_rows,), Ok(()));

    println!("success!");

    Ok(())
}

pub type MM = SignerMiddleware<Provider<Http>, Wallet<SigningKey>>;

pub async fn new_eth_client(provider_url: &str, pvk: &str) -> Result<Arc<MM>> {
    let provider: Provider<Http> =
        Provider::<Http>::try_from(provider_url)?.interval(Duration::from_millis(10u64));
    let chain_id = provider.get_chainid().await?.as_u64();

    let wallet = pvk.parse::<LocalWallet>()?;
    let client = Arc::new(SignerMiddleware::new(
        provider,
        wallet.with_chain_id(chain_id),
    ));
    let balance = client.get_balance(client.address(), None).await?;

    println!(
        "address {:?} , balance {}ETH",
        client.address(),
        format_units(balance, "ether")?
    );

    Ok(client)
}

