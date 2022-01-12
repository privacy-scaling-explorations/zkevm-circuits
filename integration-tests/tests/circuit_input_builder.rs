#![cfg(feature = "circuit_input_builder")]

use bus_mapping::circuit_input_builder::BuilderClient;
use integration_tests::{get_client, log_init, GenDataOutput};
use lazy_static::lazy_static;
use log::trace;

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

    let cli = BuilderClient::new(cli).await.unwrap();

    // 1. Query geth for Block, Txs and TxExecTraces
    let (eth_block, geth_trace) = cli.get_block(*block_num).await.unwrap();

    // 2. Get State Accesses from TxExecTraces
    let access_set = cli.get_state_accesses(&eth_block, &geth_trace).unwrap();
    trace!("AccessSet: {:#?}", access_set);

    // 3. Query geth for all accounts, storage keys, and codes from Accesses
    let (proofs, codes) = cli.get_state(*block_num, access_set).await.unwrap();

    // 4. Build a partial StateDB from step 3
    let (state_db, code_db) = cli.build_state_code_db(proofs, codes);
    trace!("StateDB: {:#?}", state_db);

    // 5. For each step in TxExecTraces, gen the associated ops and state
    // circuit inputs
    let builder = cli
        .gen_inputs_from_state(state_db, code_db, &eth_block, &geth_trace)
        .unwrap();

    trace!("CircuitInputBuilder: {:#?}", builder);
}
