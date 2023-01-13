#![cfg(feature = "circuits_actual")]
use integration_tests::integration_test_circuits::{
    test_bytecode_circuit_block, test_copy_circuit_block, test_evm_circuit_block,
    test_state_circuit_block, test_tx_circuit_block, GEN_DATA,
};
use integration_tests::log_init;
use paste::paste;

macro_rules! declare_tests {
    ($name:ident, $block_tag:expr, $mock:expr) => {
        paste! {
            #[tokio::test]
            async fn [<serial_test_evm_ $name>]() {
                log_init();
                let block_num = GEN_DATA.blocks.get($block_tag).unwrap();
                test_evm_circuit_block(*block_num, $mock).await;
            }

            #[tokio::test]
            async fn [<serial_test_state_ $name>]() {
                log_init();
                let block_num = GEN_DATA.blocks.get($block_tag).unwrap();
                test_state_circuit_block(*block_num, $mock).await;
            }

            #[tokio::test]
            async fn [<serial_test_tx_ $name>]() {
                log_init();
                let block_num = GEN_DATA.blocks.get($block_tag).unwrap();
                test_tx_circuit_block(*block_num, $mock).await;
            }

            #[tokio::test]
            async fn [<serial_test_bytecode_ $name>]() {
                log_init();
                let block_num = GEN_DATA.blocks.get($block_tag).unwrap();
                test_bytecode_circuit_block(*block_num, $mock).await;
            }

            #[tokio::test]
            async fn [<serial_test_copy_ $name>]() {
                log_init();
                let block_num = GEN_DATA.blocks.get($block_tag).unwrap();
                test_copy_circuit_block(*block_num, $mock).await;
            }
        }
    };
}

// Mock tests
declare_tests!(circuit_block_transfer_0_mock, "Transfer 0", true);
/*
declare_tests!(
    circuit_deploy_greeter,
    "Deploy Greeter",
    true
);
*/
declare_tests!(
    circuit_multiple_transfers_0_mock,
    "Multiple transfers 0",
    true
);
declare_tests!(
    circuit_erc20_openzeppelin_transfer_fail_mock,
    "ERC20 OpenZeppelin transfer failed",
    true
);
declare_tests!(
    circuit_erc20_openzeppelin_transfer_succeed_mock,
    "ERC20 OpenZeppelin transfer successful",
    true
);
declare_tests!(
    circuit_multiple_erc20_openzeppelin_transfers_mock,
    "Multiple ERC20 OpenZeppelin transfers",
    true
);

// Actual tests
declare_tests!(circuit_block_transfer_0, "Transfer 0", false);
declare_tests!(circuit_multiple_transfers_0, "Multiple transfers 0", false);
declare_tests!(
    circuit_erc20_openzeppelin_transfer_fail,
    "ERC20 OpenZeppelin transfer failed",
    false
);
declare_tests!(
    circuit_erc20_openzeppelin_transfer_succeed,
    "ERC20 OpenZeppelin transfer successful",
    false
);
declare_tests!(
    circuit_multiple_erc20_openzeppelin_transfers,
    "Multiple ERC20 OpenZeppelin transfers",
    false
);
