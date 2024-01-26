pub use super::*;
use ethers_signers::{LocalWallet, Signer};
use halo2_proofs::{dev::MockProver, halo2curves::bn256::Fr};
use log::error;
use mock::{TestContext, MOCK_CHAIN_ID};
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
use std::collections::HashMap;

use eth_types::{address, bytecode, geth_types::GethData, Word};

#[test]
fn super_circuit_degree() {
    let mut cs = ConstraintSystem::<Fr>::default();
    let params = SuperCircuitParams {
        max_txs: 1,
        max_withdrawals: 5,
        max_calldata: 32,
        mock_randomness: Fr::from(0x100),
    };
    SuperCircuit::configure_with_params(&mut cs, params);
    log::info!("super circuit degree: {}", cs.degree());
    log::info!("super circuit minimum_rows: {}", cs.minimum_rows());
    assert!(cs.degree() <= 10);
}

fn test_super_circuit(block: GethData, circuits_params: FixedCParams, mock_randomness: Fr) {
    let (k, circuit, instance, _) =
        SuperCircuit::<Fr>::build(block, circuits_params, mock_randomness).unwrap();
    let prover = MockProver::run(k, &circuit, instance).unwrap();
    let res = prover.verify_par();
    if let Err(err) = res {
        error!("Verification failures: {:#?}", err);
        panic!("Failed verification");
    }
}

pub(crate) fn block_1tx() -> GethData {
    let mut rng = ChaCha20Rng::seed_from_u64(2);

    let chain_id = (*MOCK_CHAIN_ID).as_u64();

    let bytecode = bytecode! {
        GAS
        STOP
    };

    let wallet_a = LocalWallet::new(&mut rng).with_chain_id(chain_id);

    let addr_a = wallet_a.address();
    let addr_b = address!("0x000000000000000000000000000000000000BBBB");

    let mut wallets = HashMap::new();
    wallets.insert(wallet_a.address(), wallet_a);

    let mut block: GethData = TestContext::<2, 1>::new(
        None,
        |accs| {
            accs[0]
                .address(addr_b)
                .balance(Word::from(1u64 << 20))
                .code(bytecode);
            accs[1].address(addr_a).balance(Word::from(1u64 << 20));
        },
        |mut txs, accs| {
            txs[0]
                .from(accs[1].address)
                .to(accs[0].address)
                .gas(Word::from(1_000_000u64));
        },
        |block, _tx| block.number(0xcafeu64),
    )
    .unwrap()
    .into();
    block.sign(&wallets);
    block
}

fn block_2tx() -> GethData {
    let mut rng = ChaCha20Rng::seed_from_u64(2);

    let chain_id = (*MOCK_CHAIN_ID).as_u64();

    let bytecode = bytecode! {
        GAS
        STOP
    };

    let wallet_a = LocalWallet::new(&mut rng).with_chain_id(chain_id);

    let addr_a = wallet_a.address();
    let addr_b = address!("0x000000000000000000000000000000000000BBBB");

    let mut wallets = HashMap::new();
    wallets.insert(wallet_a.address(), wallet_a);

    let mut block: GethData = TestContext::<2, 2>::new(
        None,
        |accs| {
            accs[0]
                .address(addr_b)
                .balance(Word::from(1u64 << 20))
                .code(bytecode);
            accs[1].address(addr_a).balance(Word::from(1u64 << 20));
        },
        |mut txs, accs| {
            txs[0]
                .from(accs[1].address)
                .to(accs[0].address)
                .gas(Word::from(1_000_000u64));
            txs[1]
                .from(accs[1].address)
                .to(accs[0].address)
                .gas(Word::from(1_000_000u64));
        },
        |block, _tx| block.number(0xcafeu64),
    )
    .unwrap()
    .into();
    block.sign(&wallets);
    block
}

const TEST_MOCK_RANDOMNESS: u64 = 0x100;

// High memory usage test.  Run in serial with:
// `cargo test [...] serial_ -- --ignored --test-threads 1`
#[ignore]
#[test]
fn serial_test_super_circuit_1tx_1max_tx() {
    let block = block_1tx();
    let circuits_params = FixedCParams {
        max_txs: 1,
        max_withdrawals: 5,
        max_calldata: 32,
        max_rws: 256,
        max_copy_rows: 256,
        max_exp_steps: 256,
        max_bytecode: 512,
        max_evm_rows: 0,
        max_keccak_rows: 0,
    };
    test_super_circuit(block, circuits_params, Fr::from(TEST_MOCK_RANDOMNESS));
}
#[ignore]
#[test]
fn serial_test_super_circuit_1tx_2max_tx() {
    let block = block_1tx();
    let circuits_params = FixedCParams {
        max_txs: 2,
        max_withdrawals: 5,
        max_calldata: 32,
        max_rws: 256,
        max_copy_rows: 256,
        max_exp_steps: 256,
        max_bytecode: 512,
        max_evm_rows: 0,
        max_keccak_rows: 0,
    };
    test_super_circuit(block, circuits_params, Fr::from(TEST_MOCK_RANDOMNESS));
}
#[ignore]
#[test]
fn serial_test_super_circuit_2tx_2max_tx() {
    let block = block_2tx();
    let circuits_params = FixedCParams {
        max_txs: 2,
        max_withdrawals: 5,
        max_calldata: 32,
        max_rws: 256,
        max_copy_rows: 256,
        max_exp_steps: 256,
        max_bytecode: 512,
        max_evm_rows: 0,
        max_keccak_rows: 0,
    };
    test_super_circuit(block, circuits_params, Fr::from(TEST_MOCK_RANDOMNESS));
}
