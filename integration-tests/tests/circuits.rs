macro_rules! declare_tests {
    (($name:ident, $block_tag:expr),$real_prover:expr) => {
        paste! {
            #[tokio::test]
            async fn [<serial_test_evm_ $name>]() {
                log_init();
                let block_num = GEN_DATA.blocks.get($block_tag).unwrap();
                let pk = if $real_prover { Some((*EVM_CIRCUIT_KEY).clone()) } else { None };
                let (builder, _) = gen_inputs(*block_num).await;
                let block = block_convert::<Fr>(&builder.block, &builder.code_db).unwrap();
                let rows_required = EvmCircuit::get_min_num_rows_required(&block);
                if rows_required > rows_required {
                    panic!("EVM circuit not enough rows {}, required {}", rows_required, rows_required);
                }
                test_circuit_at_block::<EvmCircuit::<Fr>>(
                    "evm", EVM_CIRCUIT_DEGREE, *block_num, $real_prover, pk).await;
            }

            #[tokio::test]
            async fn [<serial_test_state_ $name>]() {
                log_init();
                let block_num = GEN_DATA.blocks.get($block_tag).unwrap();
                let pk = if $real_prover { Some((*STATE_CIRCUIT_KEY).clone()) } else { None };
                test_circuit_at_block::<StateCircuit::<Fr>>
                    ("state", STATE_CIRCUIT_DEGREE, *block_num, $real_prover, pk).await;
            }

            #[tokio::test]
            async fn [<serial_test_tx_ $name>]() {
                log_init();
                let block_num = GEN_DATA.blocks.get($block_tag).unwrap();
                let pk = if $real_prover { Some((*TX_CIRCUIT_KEY).clone()) } else { None };
                test_circuit_at_block::<TxCircuit::<Fr>>
                    ("tx", TX_CIRCUIT_DEGREE, *block_num, $real_prover, pk).await;
            }

            #[tokio::test]
            async fn [<serial_test_bytecode_ $name>]() {
                log_init();
                let block_num = GEN_DATA.blocks.get($block_tag).unwrap();
                let pk = if $real_prover { Some((*BYTECODE_CIRCUIT_KEY).clone()) } else { None };
                test_circuit_at_block::<BytecodeCircuit::<Fr>>
                    ("bytecode", BYTECODE_CIRCUIT_DEGREE, *block_num, $real_prover, pk).await;
            }

            #[tokio::test]
            async fn [<serial_test_copy_ $name>]() {
                log_init();
                let block_num = GEN_DATA.blocks.get($block_tag).unwrap();
                let pk = if $real_prover { Some((*COPY_CIRCUIT_KEY).clone()) } else { None };
                test_circuit_at_block::<CopyCircuit::<Fr>>
                    ("copy", COPY_CIRCUIT_DEGREE, *block_num, $real_prover, pk).await;
            }

            #[tokio::test]
            async fn [<serial_test_super_ $name>]() {
                log_init();
                let block_num = GEN_DATA.blocks.get($block_tag).unwrap();
                let pk = None;
                test_circuit_at_block::<SuperCircuit::<Fr, MAX_TXS, MAX_CALLDATA, TEST_MOCK_RANDOMNESS>>
                    ("super", SUPER_CIRCUIT_DEGREE, *block_num, $real_prover, pk).await;
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
