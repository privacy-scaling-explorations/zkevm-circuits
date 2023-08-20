#![allow(unused_imports)]
use std::{collections::HashMap, str::FromStr};

use super::{
    sign_verify::{GOLDEN_TOUCH_ADDRESS, GOLDEN_TOUCH_PRIVATEKEY, GX1, GX1_MUL_PRIVATEKEY, GX2, N},
    *,
};
use crate::{
    util::{log2_ceil, unusable_rows},
    witness::{block_convert, Block},
};
use bus_mapping::{
    circuit_input_builder::{CircuitInputBuilder, CircuitsParams},
    mock::BlockData,
};
use eth_types::{
    address, bytecode,
    geth_types::GethData,
    sign_types::{biguint_to_32bytes_le, ct_option_ok_or, sign, SignData, SECP256K1_Q},
    word, Address, Field, ToBigEndian, ToLittleEndian, ToWord, Word, H256, U256,
};
use ethers_core::types::TransactionRequest;
use ethers_signers::{LocalWallet, Signer};
use gadgets::{
    is_equal::IsEqualChip,
    mul_add::{MulAddChip, MulAddConfig},
    util::{split_u256, Expr},
};
use halo2_proofs::{
    arithmetic::Field as _,
    circuit::{Layouter, Region, Value},
    dev::{MockProver, VerifyFailure},
    halo2curves::{
        bn256::Fr,
        ff::PrimeField,
        group::Curve,
        secp256k1::{self, Secp256k1Affine},
    },
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed, SecondPhase, Selector},
    poly::Rotation,
};
use itertools::Itertools;
use log::error;
use mock::{AddrOrWallet, MockAccount, MockTransaction, TestContext, MOCK_CHAIN_ID};
use num::Integer;
use num_bigint::BigUint;
use once_cell::sync::Lazy;
use sha3::{Digest, Keccak256};

fn run<F: Field>(block: &Block<F>, sign_hash: Option<H256>) -> Result<(), Vec<VerifyFailure>> {
    let k = log2_ceil(
        AnchorTxCircuit::<Fr>::unusable_rows()
            + AnchorTxCircuit::<Fr>::min_num_rows(block.circuits_params.max_txs),
    );
    let mut circuit = TestAnchorTxCircuit::<F>::new_from_block(block);
    if let Some(sign_hash) = sign_hash {
        circuit.sign_hash(sign_hash);
    }
    let prover = match MockProver::run(k + 3, &circuit, vec![]) {
        Ok(prover) => prover,
        Err(e) => panic!("{:#?}", e),
    };
    prover.verify()
}

fn gen_block<const NUM_TXS: usize>(
    max_txs: usize,
    max_calldata: usize,
    protocol_instance: ProtocolInstance,
) -> Block<Fr> {
    let chain_id = (*MOCK_CHAIN_ID).as_u64();
    let mut wallets = HashMap::new();

    let wallet =
        LocalWallet::from_str("0x92954368afd3caa1f3ce3ead0069c1af414054aefe1ef9aeacc1bf426222ce38")
            .unwrap()
            .with_chain_id(chain_id);

    wallets.insert(*GOLDEN_TOUCH_ADDRESS, wallet);

    let block: GethData = TestContext::<0, NUM_TXS>::new_with_taiko(
        None,
        |_accs| {},
        |_txs, _accs| {},
        |block, _tx| block,
    )
    .unwrap()
    .into();
    let circuits_params = CircuitsParams {
        max_txs,
        max_calldata,
        ..Default::default()
    };
    let mut builder = BlockData::new_from_geth_data_with_params(block.clone(), circuits_params)
        .new_circuit_input_builder();
    builder
        .handle_block(&block.eth_block, &block.geth_traces)
        .unwrap();
    let mut block = block_convert::<Fr>(&builder.block, &builder.code_db).unwrap();
    block.protocol_instance = Some(protocol_instance);
    block
}

fn sign_tx_r_is_gx2(tx: &mut Transaction) {
    let msg_hash = *N - *GX1_MUL_PRIVATEKEY;
    let msg_hash = ct_option_ok_or(
        secp256k1::Fq::from_repr(msg_hash.to_le_bytes()),
        libsecp256k1::Error::InvalidMessage,
    )
    .unwrap();
    let k2 = secp256k1::Fq::ONE + secp256k1::Fq::ONE;
    let sk = ct_option_ok_or(
        secp256k1::Fq::from_repr(GOLDEN_TOUCH_PRIVATEKEY.to_le_bytes()),
        libsecp256k1::Error::InvalidSecretKey,
    )
    .unwrap();
    let (sig_r, sig_s) = sign(k2, sk, msg_hash);
    let sig_r = U256::from_little_endian(sig_r.to_bytes().as_slice());
    let sig_s = U256::from_little_endian(sig_s.to_bytes().as_slice());
    tx.v = 2712;
    tx.r = sig_r;
    tx.s = sig_s;
}

#[test]
fn anchor_tx_circuit_unusable_rows() {
    assert_eq!(
        AnchorTxCircuit::<Fr>::unusable_rows(),
        unusable_rows::<Fr, TestAnchorTxCircuit::<Fr>>(()),
    )
}

#[test]
fn anchor_test() {
    let protocol_instance = Default::default();
    let block = gen_block::<0>(2, 200, protocol_instance);
    assert_eq!(run::<Fr>(&block, None), Ok(()));
}

#[test]
fn anchor_test_when_sign_r_is_gx2() {
    let protocol_instance = Default::default();
    let msg_hash = *N - *GX1_MUL_PRIVATEKEY;
    let msg_hash = H256::from(msg_hash.to_le_bytes());
    let mut block = gen_block::<0>(2, 200, protocol_instance);
    sign_tx_r_is_gx2(&mut block.txs[0]);
    assert_eq!(run::<Fr>(&block, Some(msg_hash)), Ok(()));
}
