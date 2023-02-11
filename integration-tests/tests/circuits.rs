macro_rules! run_test {
    ($test_instance:expr, $block_tag:expr, $real_prover:expr) => {
        log_init();
        let block_num = GEN_DATA.blocks.get($block_tag).unwrap();

        let mut test = $test_instance.lock().await;
        test.test_at_block(*block_num, $real_prover).await;
        drop(test) // make sure the compiler does not drop it before
    };
}

macro_rules! declare_tests {
    (($name:ident, $block_tag:expr),$real_prover:expr) => {
        paste! {
            #[tokio::test]
            async fn [<serial_test_evm_ $name>]() {
                run_test! (EVM_CIRCUIT_TEST, $block_tag, $real_prover);
            }

            #[tokio::test]
            async fn [<serial_test_state_ $name>]() {
                run_test! (STATE_CIRCUIT_TEST, $block_tag, $real_prover);
            }

            #[tokio::test]
            async fn [<serial_test_tx_ $name>]() {
                run_test! (TX_CIRCUIT_TEST, $block_tag, $real_prover);
            }

            #[tokio::test]
            async fn [<serial_test_bytecode_ $name>]() {
                run_test! (BYTECODE_CIRCUIT_TEST, $block_tag, $real_prover);
            }

            #[tokio::test]
            async fn [<serial_test_copy_ $name>]() {
                run_test! (COPY_CIRCUIT_TEST, $block_tag, $real_prover);
            }

            #[tokio::test]
            async fn [<serial_test_super_ $name>]() {
                run_test! (SUPER_CIRCUIT_TEST, $block_tag, $real_prover);
            }
        }
    };
}

macro_rules! unroll_tests {
    ($($arg:tt),*) => {
        use paste::paste;
        use zkevm_circuits::{
            state_circuit::StateCircuit,
            super_circuit::SuperCircuit,
            tx_circuit::TxCircuit,
            evm_circuit::EvmCircuit,
            bytecode_circuit::circuit::BytecodeCircuit,
            copy_circuit::CopyCircuit,
            witness::block_convert
        };
        use halo2_proofs::halo2curves::bn256::Fr;
        use integration_tests::integration_test_circuits::*;
        use integration_tests::log_init;
        mod real_prover {
            use super::*;
            $(
                declare_tests! ($arg, true) ;
            )*
        }

        mod mock_prover {
            use super::*;
            $(
                declare_tests! ($arg, false) ;
            )*
        }
    }
}

unroll_tests!(
    (circuit_block_transfer_0, "Transfer 0"),
    (circuit_multiple_transfers_0, "Multiple transfers 0"),
    (
        circuit_erc20_openzeppelin_transfer_fail,
        "ERC20 OpenZeppelin transfer failed"
    ),
    (
        circuit_erc20_openzeppelin_transfer_succeed,
        "ERC20 OpenZeppelin transfer successful"
    ),
    (
        circuit_multiple_erc20_openzeppelin_transfers,
        "Multiple ERC20 OpenZeppelin transfers"
    )
);
