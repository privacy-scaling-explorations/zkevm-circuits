use std::{sync::Arc, time::Duration};

use ethers::{
    core::k256::ecdsa::SigningKey,
    middleware::SignerMiddleware,
    providers::{Http, Middleware, Provider},
    signers::{LocalWallet, Signer, Wallet},
    utils::format_units,
};
use eyre::Result;
use zkevm_circuits::mpt_circuit::witness_row::Node;

pub type MM = SignerMiddleware<Provider<Http>, Wallet<SigningKey>>;

pub async fn new_eth_signer_client(provider_url: &str, pvk: &str) -> Result<Arc<MM>> {
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
                hex::encode(&extension_branch.extension.list_rlp_bytes.to_vec())
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
                hex::encode(&extension_branch.branch.list_rlp_bytes[0].to_vec())
            );
            println!(
                "         list_rlp_bytes[1]: {}",
                hex::encode(&extension_branch.branch.list_rlp_bytes[1].to_vec())
            );
        }
        if let Some(account) = &n.account {
            println!("   account:");
            println!("       address: {}", hex::encode(&*account.address));
            println!("       key: {}", hex::encode(&account.key.to_vec()));
            println!(
                "       list_rlp_bytes[0]: {}",
                hex::encode(&account.list_rlp_bytes[0].to_vec())
            );
            println!(
                "       list_rlp_bytes[1]: {}",
                hex::encode(&account.list_rlp_bytes[1].to_vec())
            );
            println!(
                "       value_rlp_bytes[0]: {}",
                hex::encode(&account.value_rlp_bytes[0].to_vec())
            );
            println!(
                "       value_rlp_bytes[1]: {}",
                hex::encode(&account.value_rlp_bytes[1].to_vec())
            );
            println!(
                "       value_list_rlp_bytes[0]: {}",
                hex::encode(&account.value_list_rlp_bytes[0].to_vec())
            );
            println!(
                "       value_list_rlp_bytes[1]: {}",
                hex::encode(&account.value_list_rlp_bytes[1].to_vec())
            );
            println!(
                "       drifted_rlp_bytes: {}",
                hex::encode(&account.drifted_rlp_bytes.to_vec())
            );
            println!(
                "       wrong_rlp_bytes: {}",
                hex::encode(&account.wrong_rlp_bytes.to_vec())
            );
        }

        if let Some(storage) = &n.storage {
            println!("   storage:");
            println!("       address: {}", hex::encode(&*storage.address));
            println!("       key: {}", hex::encode(&storage.key.to_vec()));
            println!(
                "       list_rlp_bytes[0]: {}",
                hex::encode(&storage.list_rlp_bytes[0].to_vec())
            );
            println!(
                "       list_rlp_bytes[1]: {}",
                hex::encode(&storage.list_rlp_bytes[1].to_vec())
            );
            println!(
                "       value_rlp_bytes[0]: {}",
                hex::encode(&storage.value_rlp_bytes[0].to_vec())
            );
            println!(
                "       value_rlp_bytes[1]: {}",
                hex::encode(&storage.value_rlp_bytes[1].to_vec())
            );
            println!(
                "       drifted_rlp_bytes: {}",
                hex::encode(&storage.drifted_rlp_bytes.to_vec())
            );
            println!(
                "       wrong_rlp_bytes: {}",
                hex::encode(&storage.wrong_rlp_bytes.to_vec())
            );
        }
        println!("   values:");
        for (idx, value) in n.values.iter().enumerate() {
            println!("      [{}]: {}", idx, hex::encode(value.to_vec()));
        }

        println!("   keccak_data:");
        for (idx, value) in n.keccak_data.iter().enumerate() {
            println!("      [{}]: {}", idx, hex::encode(value.to_vec()));
        }
    }
}
