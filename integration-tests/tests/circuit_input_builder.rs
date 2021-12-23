#![cfg(feature = "circuit_input_builder")]

use bus_mapping::circuit_input_builder::{
    gen_state_access_trace, AccessSet, CircuitInputBuilder,
};
use bus_mapping::eth_types::{Address, Word};
use bus_mapping::state_db::{self, CodeDB, StateDB};
use integration_tests::{
    get_chain_constants, get_client, log_init, GenDataOutput,
};
use lazy_static::lazy_static;
use log::trace;
use std::collections::HashMap;

lazy_static! {
    pub static ref GEN_DATA: GenDataOutput = GenDataOutput::load();
}

/// This test builds the complete circuit inputs for the block where the Greeter
/// contract is deployed.
#[tokio::test]
async fn test_circuit_input_builder_block_a() {
    log_init();
    let (block_num, _address) = GEN_DATA.deployments.get("Greeter").unwrap();
    let cli = get_client();

    // 1. Query geth for Block, Txs and TxExecTraces
    let eth_block = cli.get_block_by_number((*block_num).into()).await.unwrap();
    let geth_trace = cli
        .trace_block_by_number((*block_num).into())
        .await
        .unwrap();
    let tx_index = 0;

    // 2. Get State Accesses from TxExecTraces
    let access_trace = gen_state_access_trace(
        &eth_block,
        &eth_block.transactions[tx_index],
        &geth_trace[tx_index],
    )
    .unwrap();
    trace!("AccessTrace:");
    for access in &access_trace {
        trace!("{:#?}", access);
    }

    let access_set = AccessSet::from(access_trace);
    trace!("AccessSet: {:#?}", access_set);

    // 3. Query geth for all accounts, storage keys, and codes from Accesses
    let mut proofs = Vec::new();
    for (address, key_set) in access_set.state {
        let mut keys: Vec<Word> = key_set.iter().cloned().collect();
        keys.sort();
        let proof = cli
            .get_proof(address, keys, (*block_num - 1).into())
            .await
            .unwrap();
        proofs.push(proof);
    }
    let mut codes: HashMap<Address, Vec<u8>> = HashMap::new();
    for address in access_set.code {
        let code = cli
            .get_code(address, (*block_num - 1).into())
            .await
            .unwrap();
        codes.insert(address, code);
    }

    // 4. Build a partial StateDB from step 3
    let mut sdb = StateDB::new();
    for proof in proofs {
        let mut storage = HashMap::new();
        for storage_proof in proof.storage_proof {
            storage.insert(storage_proof.key, storage_proof.value);
        }
        sdb.set_account(
            &proof.address,
            state_db::Account {
                nonce: proof.nonce,
                balance: proof.balance,
                storage,
                code_hash: proof.code_hash,
            },
        )
    }
    trace!("StateDB: {:#?}", sdb);

    let mut code_db = CodeDB::new();
    for (_address, code) in codes {
        code_db.insert(code.clone());
    }
    let constants = get_chain_constants().await;
    let mut builder =
        CircuitInputBuilder::new(sdb, code_db, &eth_block, constants);

    // 5. For each step in TxExecTraces, gen the associated ops and state
    // circuit inputs
    let block_geth_trace = cli
        .trace_block_by_number((*block_num).into())
        .await
        .unwrap();
    for (tx_index, tx) in eth_block.transactions.iter().enumerate() {
        let geth_trace = &block_geth_trace[tx_index];
        builder.handle_tx(tx, geth_trace).unwrap();
    }

    trace!("CircuitInputBuilder: {:#?}", builder);
}
