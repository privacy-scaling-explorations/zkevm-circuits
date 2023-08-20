#![allow(unused_imports)]
pub use super::*;
use bus_mapping::circuit_input_builder::MetaHash;
use ethers_signers::{LocalWallet, Signer};
use halo2_proofs::{dev::MockProver, halo2curves::bn256::Fr};
use log::error;
use mock::{
    TestContext, MOCK_ANCHOR_GAS_LIMIT, MOCK_ANCHOR_L1_HASH, MOCK_ANCHOR_L1_HIGHT,
    MOCK_ANCHOR_PARENT_GAS_USED, MOCK_ANCHOR_SIGNAL_ROOT, MOCK_CHAIN_ID,
};
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
use std::str::FromStr;

use eth_types::{address, bytecode, geth_types::GethData, Hash, ToWord, Word};

#[test]
fn super_circuit_degree() {
    let mut cs = ConstraintSystem::<Fr>::default();
    SuperCircuit::configure(&mut cs);
    log::info!("super circuit degree: {}", cs.degree());
    log::info!("super circuit minimum_rows: {}", cs.minimum_rows());
    assert!(cs.degree() <= 9);
}

fn test_super_circuit(
    block: GethData,
    protocol_instance: ProtocolInstance,
    circuits_params: CircuitsParams,
) {
    let (_, circuit, instance, _) =
        SuperCircuit::<Fr>::build(block, circuits_params, protocol_instance).unwrap();
    // TODO: fix k from build
    let k = 18;
    let prover = MockProver::run(k, &circuit, instance).unwrap();
    let res = prover.verify_par();
    if let Err(err) = res {
        error!("Verification failures: {:#?}", err);
        panic!("Failed verification");
    }
}

/// build a block with anchor tx
pub fn block_1tx() -> GethData {
    let mut rng = ChaCha20Rng::seed_from_u64(2);

    let chain_id = (*MOCK_CHAIN_ID).as_u64();

    let bytecode = bytecode! {
        GAS
        STOP
    };

    let wallet_a = LocalWallet::new(&mut rng).with_chain_id(chain_id);

    let addr_a = wallet_a.address();
    let addr_b = address!("0x000000000000000000000000000000000000BBBB");

    let mut block: GethData = TestContext::<2, 1>::new_with_taiko(
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
                .nonce(0)
                .gas(Word::from(1_000_000u64));
            let geth_tx: eth_types::Transaction = txs[0].clone().into();
            let req: ethers_core::types::TransactionRequest = (&geth_tx).into();
            let sig = wallet_a.sign_transaction_sync(&req.chain_id(chain_id).into());
            txs[0].sig_data((sig.v, sig.r, sig.s));
        },
        |block, _tx| block.number(0xcafeu64),
    )
    .unwrap()
    .into();
    block.history_hashes = vec![block.eth_block.parent_hash.to_word()];
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
                .nonce(0)
                .gas(Word::from(1_000_000u64));
            let geth_tx: eth_types::Transaction = txs[0].clone().into();
            let req: ethers_core::types::TransactionRequest = (&geth_tx).into();
            let sig = wallet_a.sign_transaction_sync(&req.chain_id(chain_id).into());
            txs[0].sig_data((sig.v, sig.r, sig.s));
            txs[1]
                .from(accs[1].address)
                .to(accs[0].address)
                .nonce(1)
                .gas(Word::from(1_000_000u64));
            let geth_tx: eth_types::Transaction = txs[1].clone().into();
            let req: ethers_core::types::TransactionRequest = (&geth_tx).into();
            let sig = wallet_a.sign_transaction_sync(&req.chain_id(chain_id).into());
            txs[1].sig_data((sig.v, sig.r, sig.s));
        },
        |block, _tx| block.number(0xcafeu64),
    )
    .unwrap()
    .into();
    block.history_hashes = vec![block.eth_block.parent_hash.to_word()];
    block
}

// High memory usage test.  Run in serial with:
// `cargo test [...] serial_ -- --ignored --test-threads 1`
// #[ignore]
#[test]
fn serial_test_super_circuit_1tx_1max_tx() {
    let block_hash =
        Hash::from_str("0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347")
            .unwrap();
    let parent_hash =
        Hash::from_str("0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49346")
            .unwrap();
    let protocol_instance = ProtocolInstance::default();
    let mut block = block_1tx();
    let circuits_params = CircuitsParams::default();
    block.eth_block.hash = Some(block_hash);
    block.eth_block.parent_hash = parent_hash;
    block.history_hashes = vec![block.eth_block.parent_hash.to_word()];
    test_super_circuit(block, protocol_instance, circuits_params);
}
#[ignore]
#[test]
fn taiko_serial_test_super_circuit_1tx_3max_tx() {
    let protocol_instance = ProtocolInstance::default();
    let block = block_1tx();
    let circuits_params = CircuitsParams {
        max_txs: 3,
        max_calldata: 200,
        max_rws: 256,
        max_copy_rows: 256,
        max_exp_steps: 256,
        max_bytecode: 512,
        max_evm_rows: 0,
        max_keccak_rows: 0,
    };
    test_super_circuit(block, protocol_instance, circuits_params);
}
#[ignore]
#[test]
fn taiko_serial_test_super_circuit_2tx_3max_tx() {
    let protocol_instance = ProtocolInstance::default();
    let block = block_2tx();
    let circuits_params = CircuitsParams {
        max_txs: 3,
        max_calldata: 200,
        max_rws: 256,
        max_copy_rows: 256,
        max_exp_steps: 256,
        max_bytecode: 512,
        max_evm_rows: 0,
        max_keccak_rows: 0,
    };
    test_super_circuit(block, protocol_instance, circuits_params);
}
