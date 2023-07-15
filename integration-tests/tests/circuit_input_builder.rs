#![cfg(feature = "circuit_input_builder")]

use integration_tests::{build_circuit_input_builder_block, log_init, GenDataOutput};
use lazy_static::lazy_static;

lazy_static! {
    pub static ref GEN_DATA: GenDataOutput = GenDataOutput::load();
}

macro_rules! declare_tests {
    ($test_name:ident, $block_tag:expr) => {
        #[tokio::test]
        async fn $test_name() {
            log_init();
            let block_num = GEN_DATA.blocks.get($block_tag).unwrap();
            build_circuit_input_builder_block(*block_num).await;
        }
    };
}

// This test builds the complete circuit inputs for the block where 1 ETH is
// transfered.
declare_tests!(test_circuit_input_builder_block_transfer_0, "Transfer 0");
// This test builds the complete circuit inputs for the block where the Greeter
// contract is deployed.
declare_tests!(test_circuit_input_builder_deploy_greeter, "Deploy Greeter");
// This test builds the complete circuit inputs for the block with multiple
// transfer txs.
declare_tests!(
    test_circuit_input_builder_multiple_transfers_0,
    "Multiple transfers 0"
);
// This test builds the complete circuit inputs for the block with a failed
// OpenZeppelin ERC20 transfer tx.
declare_tests!(
    test_circuit_input_builder_erc20_openzeppelin_transfer_fail,
    "ERC20 OpenZeppelin transfer failed"
);
// This test builds the complete circuit inputs for the block with a successful
// OpenZeppelin ERC20 transfer tx.
declare_tests!(
    test_circuit_input_builder_erc20_openzeppelin_transfer_succeed,
    "ERC20 OpenZeppelin transfer successful"
);
// This test builds the complete circuit inputs for the block with multiple
// successful and failed OpenZeppelin ERC20 transfer txs.
declare_tests!(
    test_circuit_input_builder_multiple_erc20_openzeppelin_transfers,
    "Multiple ERC20 OpenZeppelin transfers"
);
