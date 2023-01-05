#![cfg(feature = "circuits_mock")]
use integration_tests::integration_test_circuits::{
    test_bytecode_circuit_block, test_copy_circuit_block, test_evm_circuit_block,
    test_state_circuit_block, test_super_circuit_block, test_tx_circuit_block, GEN_DATA,
};
use integration_tests::log_init;
use paste::paste;

macro_rules! declare_tests {
    ($name:ident, $block_tag:expr) => {
        paste! {
            #[tokio::test]
            async fn [<serial_test_evm_ $name>]() {
                log_init();
                let block_num = GEN_DATA.blocks.get($block_tag).unwrap();
                test_evm_circuit_block(*block_num, false).await;
            }

            #[tokio::test]
            async fn [<serial_test_state_ $name>]() {
                log_init();
                let block_num = GEN_DATA.blocks.get($block_tag).unwrap();
                test_state_circuit_block(*block_num, false).await;
            }

            #[tokio::test]
            async fn [<serial_test_tx_ $name>]() {
                log_init();
                let block_num = GEN_DATA.blocks.get($block_tag).unwrap();
                test_tx_circuit_block(*block_num, false).await;
            }

            #[tokio::test]
            async fn [<serial_test_bytecode_ $name>]() {
                log_init();
                let block_num = GEN_DATA.blocks.get($block_tag).unwrap();
                test_bytecode_circuit_block(*block_num, false).await;
            }

            #[tokio::test]
            async fn [<serial_test_copy_ $name>]() {
                log_init();
                let block_num = GEN_DATA.blocks.get($block_tag).unwrap();
                test_copy_circuit_block(*block_num, false).await;
            }

            #[tokio::test]
            async fn [<serial_test_super_ $name>]() {
                log_init();
                let block_num = GEN_DATA.blocks.get($block_tag).unwrap();
                test_super_circuit_block(*block_num).await;
            }
        }
    };
}

declare_tests!(circuit_block_transfer_0, "Transfer 0");
/*
declare_tests!(
    circuit_deploy_greeter,
    "Deploy Greeter",
    true
);
*/
declare_tests!(circuit_multiple_transfers_0, "Multiple transfers 0");
declare_tests!(
    circuit_erc20_openzeppelin_transfer_fail,
    "ERC20 OpenZeppelin transfer failed"
);
declare_tests!(
    circuit_erc20_openzeppelin_transfer_succeed,
    "ERC20 OpenZeppelin transfer successful"
);
declare_tests!(
    circuit_multiple_erc20_openzeppelin_transfers,
    "Multiple ERC20 OpenZeppelin transfers"
);
