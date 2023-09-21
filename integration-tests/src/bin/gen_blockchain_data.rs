use core::{borrow::Borrow, clone::Clone};
use ethers::{
    abi::{self, Abi},
    contract::{builders::ContractCall, Contract},
    core::{
        types::{
            transaction::eip2718::TypedTransaction, Address, GethDebugTracingOptions,
            TransactionReceipt, TransactionRequest, H160, U256, U64,
        },
        utils::WEI_IN_ETHER,
    },
    middleware::{
        contract::{ContractDeploymentTx, ContractInstance},
        SignerMiddleware,
    },
    providers::{Http, Middleware, PendingTransaction, Provider},
    signers::Signer,
};
use integration_tests::{
    benchmarks::*, get_client, get_provider, get_wallet, greeter::*, log_init,
    openzeppelinerc20testtoken::openzeppelinerc20testtoken as ozerc20tt, GenDataOutput,
};
use log::{error, info};
use std::{collections::HashMap, fs::File, sync::Arc, thread::sleep, time::Duration};

async fn deploy<'a, M, C, B>(
    deployer_tx: ContractDeploymentTx<B, M, C>,
    name: &'a str,
) -> (Abi, H160, U64, C)
where
    M: Middleware + 'a,
    B: Borrow<M> + Clone + 'a,
    C: From<ContractInstance<B, M>> + 'a,
{
    info!("Deploying {}...", name);
    let binding = deployer_tx.clone();
    let contract_abi = binding.abi();
    let c_abi = contract_abi.clone();
    let contract_deployed = deployer_tx
        .send_with_receipt()
        .await
        .expect("Could not confirm contract deployment");
    let contract_instance = contract_deployed.0;
    let deploy_tx_receipt = contract_deployed.1;
    let block_number = deploy_tx_receipt
        .block_number
        .expect("failed to get block number");
    let contract_address = deploy_tx_receipt
        .contract_address
        .expect("failed to get contract address");
    (c_abi, contract_address, block_number, contract_instance)
}

async fn dump_tx_trace(prov: Provider<Http>, receipt: TransactionReceipt, name: &str) -> () {
    let options = GethDebugTracingOptions::default();
    let trace = prov
        .debug_trace_transaction(receipt.transaction_hash, options)
        .await
        .expect("SOME REASON");
    let filename = format!("{}_trace.json", name);
    serde_json::to_writer(&File::create(filename).expect("cannot create file"), &trace)
        .expect("reason");
}

fn erc20_transfer<M>(
    prov: Arc<M>,
    contract_address: Address,
    contract_abi: &abi::Contract,
    to: Address,
    amount: U256,
) -> TypedTransaction
where
    M: Middleware,
{
    let contract = Contract::new(contract_address, contract_abi.clone(), prov);
    let call: ContractCall<M, _> = contract
        .method::<_, bool>("transfer", (to, amount))
        .expect("cannot construct ERC20 transfer call");
    // Set gas to avoid `eth_estimateGas` call
    let call = call.legacy();
    let call = call.gas(100_000);
    call.tx
}

async fn send_confirm_tx<M>(prov: &Arc<M>, tx: TypedTransaction) -> TransactionReceipt
where
    M: Middleware,
{
    prov.send_transaction(tx, None)
        .await
        .expect("cannot send ERC20 transfer call")
        .confirmations(0usize)
        .await
        .unwrap()
        .unwrap()
}

#[tokio::main]
async fn main() {
    log_init();

    let prov = get_provider();
    let mut contracts = HashMap::new();

    // Wait for geth to be online.
    loop {
        match prov.client_version().await {
            Ok(version) => {
                info!("Geth online: {}", version);
                break;
            }
            Err(err) => {
                error!("Geth not available: {:?}", err);
                sleep(Duration::from_millis(500));
            }
        }
    }

    // Make sure the blockchain is in a clean state: block 0 is the last block.
    let block_number = prov
        .get_block_number()
        .await
        .expect("cannot get block number");
    if block_number.as_u64() != 0 {
        panic!(
            "Blockchain is not in a clean state.  Last block number: {}",
            block_number
        );
    }

    let accounts = prov.get_accounts().await.expect("cannot get accounts");
    let wallet0 = get_wallet(0);
    info!("wallet0: {:x}", wallet0.address());

    let mut blocks = HashMap::new();

    // ETH Transfer: Transfer funds to our account.
    //

    info!("Transferring funds from coinbase...");
    let tx = TransactionRequest::new()
        .to(wallet0.address())
        .value(WEI_IN_ETHER) // send 1 ETH
        .from(accounts[0]);
    prov.send_transaction(tx, None)
        .await
        .expect("cannot send tx")
        .await
        .expect("cannot confirm tx");
    let block_num = prov.get_block_number().await.expect("cannot get block_num");
    blocks.insert("Transfer 0".to_string(), block_num.as_u64());

    // Deploy smart contracts
    //

    let mut deployments = HashMap::new();
    let prov_wallet0 = Arc::new(SignerMiddleware::new(get_provider(), wallet0));

    // Greeter
    let greeter_deployer = greeter::greeter::deploy(prov_wallet0.clone(), U256::from(42))
        .expect("Error building deployment Transaction");
    let (contract_abi, contract_address, block_number, _greeter_instance) =
        deploy(greeter_deployer, "Greeter").await;

    contracts.insert("greeter".to_string(), contract_abi.clone());
    deployments.insert(
        "greeter".to_string(),
        (block_number.as_u64(), contract_address),
    );
    blocks.insert("Deploy Greeter".to_string(), block_num.as_u64());
    

    // OpenZeppelinERC20TestToken
    let ozerc20tt_deployer = ozerc20tt::deploy(prov_wallet0.clone(), prov_wallet0.address())
        .expect("Error building deployment Transaction");
    let (contract_abi, contract_address, block_number, _ozerc20tt_instance) =
        deploy(ozerc20tt_deployer, "OpenZeppelinERC20TestToken").await;

    contracts.insert("ozerc20tt".to_string(), contract_abi);
    deployments.insert(
        "ozerc20tt".to_string(),
        (block_number.as_u64(), contract_address),
    );

    // Deploy smart contracts for worst case block benches
    //

    // Benchmarks
    let benchmarks_deployer = benchmarks::benchmarks::deploy(prov_wallet0.clone(), ())
        .expect("Error building deployment Transaction");
    let (contract_abi, contract_address, block_number, benchmarks_instance) =
        deploy(benchmarks_deployer, "Benchmarks").await;

    contracts.insert("benchmarks".to_string(), contract_abi);
    deployments.insert(
        "benchmarks".to_string(),
        (block_number.as_u64(), contract_address),
    );

    // ETH transfers: Generate a block with multiple transfers
    //

    info!("Generating block with multiple transfers...");
    const NUM_TXS: usize = 4; // NUM_TXS must be >= 4 for the rest of the cases to work.
    let wallets: Vec<_> = (0..NUM_TXS + 1)
        .map(|i| Arc::new(SignerMiddleware::new(get_provider(), get_wallet(i as u32))))
        .collect();

    let cli = get_client();

    // Fund NUM_TXS wallets from coinbase
    cli.miner_stop().await.expect("cannot stop miner");
    let mut pending_txs = Vec::new();
    for wallet in &wallets[0..NUM_TXS] {
        let tx = TransactionRequest::new()
            .to(wallet.address())
            .value(WEI_IN_ETHER * 2u8) // send 2 ETH
            .from(accounts[0]);
        pending_txs.push(
            prov.send_transaction(tx, None)
                .await
                .expect("cannot send tx"),
        );
    }
    cli.miner_start().await.expect("cannot start miner");
    for tx in pending_txs {
        tx.await.expect("cannot confirm tx");
    }
    let block_num = prov.get_block_number().await.expect("cannot get block_num");
    blocks.insert("Fund wallets".to_string(), block_num.as_u64());

    // Make NUM_TXS transfers in a "chain"
    cli.miner_stop().await.expect("cannot stop miner");
    let mut pending_txs = Vec::new();
    for i in 0..NUM_TXS {
        let tx = TransactionRequest::new()
            .to(wallets[i + 1].address())
            .value(WEI_IN_ETHER / (2 * (i + 1))) // send a fraction of an ETH
            .from(wallets[i].address());
        pending_txs.push(
            wallets[i]
                .send_transaction(tx, None)
                .await
                .expect("cannot send tx"),
        );
    }
    cli.miner_start().await.expect("cannot start miner");
    for tx in pending_txs {
        tx.await.expect("cannot confirm tx");
    }
    let block_num = prov.get_block_number().await.expect("cannot get block_num");
    blocks.insert("Multiple transfers 0".to_string(), block_num.as_u64());

    // ERC20 calls (OpenZeppelin)
    //

    info!("Generating ERC20 calls...");

    let contract_address = deployments.get("ozerc20tt").expect("contract not found").1;
    let contract_abi = &contracts.get("ozerc20tt").expect("contract not found");
    // .abi;

    // OpenZeppelin ERC20 single failed transfer (wallet2 sends 345.67 Tokens to
    // wallet3, but wallet2 has 0 Tokens)
    info!("Doing OpenZeppelin ERC20 single failed transfer...");
    let amount = U256::from_dec_str("345670000000000000000").unwrap();
    let tx = erc20_transfer(
        wallets[2].clone(),
        contract_address,
        contract_abi,
        wallets[3].address(),
        amount,
    );
    let receipt = send_confirm_tx(&wallets[2], tx).await;
    assert_eq!(receipt.status, Some(U64::from(0u64)));
    blocks.insert(
        "ERC20 OpenZeppelin transfer failed".to_string(),
        receipt.block_number.unwrap().as_u64(),
    );

    // OpenZeppelin ERC20 single successful transfer (wallet0 sends 123.45 Tokens to
    // wallet4)
    info!("Doing OpenZeppelin ERC20 single successful transfer...");
    let amount = U256::from_dec_str("123450000000000000000").unwrap();
    let tx = erc20_transfer(
        wallets[0].clone(),
        contract_address,
        contract_abi,
        wallets[4].address(),
        amount,
    );
    let receipt = send_confirm_tx(&wallets[0], tx).await;
    assert_eq!(receipt.status, Some(U64::from(1u64)));
    blocks.insert(
        "ERC20 OpenZeppelin transfer successful".to_string(),
        receipt.block_number.unwrap().as_u64(),
    );

    // OpenZeppelin ERC20 multiple transfers in a single block (some successful,
    // some unsuccessful)
    // - wallet0 -> wallet1 (ok)
    // - wallet2 -> wallet3 (ko)
    // - wallet1 -> wallet0 (ok)
    // - wallet3 -> wallet2 (ko)
    info!("Doing OpenZeppelin ERC20 multiple transfers...");
    cli.miner_stop().await.expect("cannot stop miner");
    let mut tx_hashes = Vec::new();
    for (i, (from_i, to_i)) in [(0, 1), (2, 3), (1, 0), (3, 2)].iter().enumerate() {
        let amount = U256::from(0x800000000000000 / (i + 1));
        let prov_wallet = &wallets[*from_i];
        let tx = erc20_transfer(
            prov_wallet.clone(),
            contract_address,
            contract_abi,
            wallets[*to_i].address(),
            amount,
        );

        let pending_tx = prov_wallet
            .send_transaction(tx, None)
            .await
            .expect("cannot send ERC20 transfer call");
        let tx_hash = *pending_tx; // Deref for PendingTransaction returns TxHash
        tx_hashes.push(tx_hash);
    }
    cli.miner_start().await.expect("cannot start miner");
    for (i, tx_hash) in tx_hashes.iter().enumerate() {
        let pending_tx = PendingTransaction::new(*tx_hash, wallets[i].inner());
        let receipt = pending_tx.confirmations(0usize).await.unwrap().unwrap();
        let expected_status = if i % 2 == 0 { 1u64 } else { 0u64 };
        assert_eq!(
            receipt.status,
            Some(U64::from(expected_status)),
            "failed tx hash: {:?}, receipt: {:#?}",
            tx_hash,
            receipt
        );
    }
    let block_num = prov.get_block_number().await.expect("cannot get block_num");
    blocks.insert(
        "Multiple ERC20 OpenZeppelin transfers".to_string(),
        block_num.as_u64(),
    );

    // Create Transactions optimized for circuit benchmarks
    //
    // MLOAD (EVM)
    info!("Sending Tx optimized for maximum MLOAD opcode calls up to 300k gas");
    cli.miner_start().await.expect("cannot start miner");
    let bench_tx = benchmarks_instance.check_mload(benchmarks::Len(77500));
    let tx_call = bench_tx
        .send()
        .await
        .expect("Could not confirm transaction");
    let tx_receipt = tx_call
        .await
        .expect("failed to fetch the transaction receipt")
        .unwrap();
    blocks.insert(
        "MLOAD".to_string(),
        tx_receipt.block_number.unwrap().as_u64(),
    );
    // dump_tx_trace(get_provider(), tx_receipt, "mload").await;

    // SDIV (STATE)
    info!("Sending Tx optimized for maximum SDIV opcode calls up to 300k gas");
    cli.miner_start().await.expect("cannot start miner");
    let bench_tx = benchmarks_instance.check_sdiv(benchmarks::Len(32400));
    let tx_call = bench_tx
        .send()
        .await
        .expect("Could not confirm transaction");
    let tx_receipt = tx_call
        .await
        .expect("failed to fetch the transaction receipt")
        .unwrap();
    blocks.insert(
        "SDIV".to_string(),
        tx_receipt.block_number.unwrap().as_u64(),
    );
    // dump_tx_trace(get_provider(), tx_receipt, "sdiv").await;

    let gen_data = GenDataOutput {
        coinbase: accounts[0],
        wallets: wallets.iter().map(|w| w.address()).collect(),
        blocks,
        deployments,
    };
    gen_data.store();
}
