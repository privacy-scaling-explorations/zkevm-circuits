use crate::{
    MockTransaction, GOLDEN_TOUCH_PRIVATEKEY, MOCK_ANCHOR_L1_HASH, MOCK_ANCHOR_L1_HIGHT,
    MOCK_ANCHOR_PARENT_GAS_USED, MOCK_ANCHOR_SIGNAL_ROOT, MOCK_CHAIN_ID,
};
use eth_types::{
    geth_types::Transaction,
    sign_types::{biguint_to_32bytes_le, ct_option_ok_or, sign as eth_sign, SignData, SECP256K1_Q},
    word, Bytes, ToBigEndian, ToLittleEndian, ToWord, Word, U256,
};
use ethers_core::types::Eip1559TransactionRequest;
use halo2_proofs::{
    arithmetic::Field as _,
    halo2curves::{
        ff::PrimeField,
        group::Curve,
        secp256k1::{self, Secp256k1Affine},
    },
};
use num::Integer;
use num_bigint::BigUint;
use once_cell::sync::Lazy;
use sha3::{Digest, Keccak256};

static GX1: Lazy<Word> =
    Lazy::new(|| word!("0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798"));
static GX2: Lazy<Word> =
    Lazy::new(|| word!("0xc6047f9441ed7d6d3045406e95c07cd85c778e4b8cef3ca7abac09b95c709ee5"));

fn fixd_k_sign(anchor_tx: &Transaction, chain_id: u64) -> Result<SignData, eth_types::Error> {
    // msg = rlp([nonce, gasPrice, gas, to, value, data, sig_v, r, s])
    let req: Eip1559TransactionRequest = anchor_tx.into();
    let msg = req.chain_id(chain_id).rlp();
    let msg_hash: [u8; 32] = Keccak256::digest(&msg)
        .as_slice()
        .to_vec()
        .try_into()
        .expect("hash length isn't 32 bytes");
    // msg_hash = msg_hash % q
    let msg_hash = BigUint::from_bytes_be(msg_hash.as_slice());
    let msg_hash = msg_hash.mod_floor(&*SECP256K1_Q);
    let msg_hash_le = biguint_to_32bytes_le(msg_hash);
    let msg_hash = ct_option_ok_or(
        secp256k1::Fq::from_repr(msg_hash_le),
        libsecp256k1::Error::InvalidMessage,
    )?;
    let k1 = secp256k1::Fq::ONE;
    let sk = ct_option_ok_or(
        secp256k1::Fq::from_repr((*GOLDEN_TOUCH_PRIVATEKEY).to_le_bytes()),
        libsecp256k1::Error::InvalidSecretKey,
    )?;
    let generator = Secp256k1Affine::generator();
    let pk = generator * sk;
    let pk = pk.to_affine();
    let (mut sig_r, mut sig_s) = eth_sign(k1, sk, msg_hash);
    let gx1 = ct_option_ok_or(
        secp256k1::Fq::from_repr(GX1.to_le_bytes()),
        libsecp256k1::Error::InvalidSignature,
    )?;
    assert!(sig_r == gx1);
    if sig_s == secp256k1::Fq::ZERO {
        let k2 = secp256k1::Fq::ONE + secp256k1::Fq::ONE;
        (sig_r, sig_s) = eth_sign(k2, sk, msg_hash);
        let gx2 = ct_option_ok_or(
            secp256k1::Fq::from_repr(GX2.to_le_bytes()),
            libsecp256k1::Error::InvalidSignature,
        )?;
        assert!(sig_r == gx2);
    }
    Ok(SignData {
        signature: (sig_r, sig_s),
        pk,
        msg_hash,
    })
}

/// The signature of anchor transaction
pub fn sign(tx: &mut MockTransaction) {
    let chain_id = (*MOCK_CHAIN_ID).as_u64();
    let _tx: Transaction = tx.to_owned().into();
    let sig_data = fixd_k_sign(&_tx, chain_id).unwrap();
    let sig_r = U256::from_little_endian(sig_data.signature.0.to_bytes().as_slice());
    let sig_s = U256::from_little_endian(sig_data.signature.1.to_bytes().as_slice());
    tx.sig_data((2712, sig_r, sig_s));
}

/// gen anchor call
// anchor(l1_hash,signal_root,l1_height,parent_gas_used)
pub fn anchor_call() -> Bytes {
    const METHOD_SIGNATURE: u32 = 0xda69d3db;
    let mut result = Vec::new();
    result.extend_from_slice(&METHOD_SIGNATURE.to_be_bytes());
    result.extend_from_slice(&MOCK_ANCHOR_L1_HASH.to_fixed_bytes());
    result.extend_from_slice(&MOCK_ANCHOR_SIGNAL_ROOT.to_fixed_bytes());
    result.extend_from_slice(&MOCK_ANCHOR_L1_HIGHT.to_word().to_be_bytes());
    result.extend_from_slice(
        &(*MOCK_ANCHOR_PARENT_GAS_USED as u64)
            .to_word()
            .to_be_bytes(),
    );
    result.into()
}
