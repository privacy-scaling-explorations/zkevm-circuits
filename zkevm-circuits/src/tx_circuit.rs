//! The transaction circuit implementation.

// Naming notes:
// - *_be: Big-Endian bytes
// - *_le: Little-Endian bytes

mod sign_verify;

use crate::util::Expr;
use eth_types::{Address, Bytes, Field, ToBigEndian, ToLittleEndian, ToScalar, Word, U256};
use ff::PrimeField;
use group::GroupEncoding;
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, Region, SimpleFloorPlanner},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error},
    poly::Rotation,
};
use itertools::Itertools;
use lazy_static::lazy_static;
use libsecp256k1;
use log::error;
use num::Integer;
use num_bigint::BigUint;
use rlp::RlpStream;
use secp256k1::Secp256k1Affine;
use sha3::{Digest, Keccak256};
use sign_verify::{SignData, SignVerifyChip, SignVerifyConfig};
pub use sign_verify::{POW_RAND_SIZE, VERIF_HEIGHT};
use std::convert::TryInto;
use std::marker::PhantomData;
use subtle::CtOption;

lazy_static! {
    // Scalar
    static ref SECP256K1_Q: BigUint = BigUint::from_slice(&[
        0xd0364141, 0xbfd25e8c,
        0xaf48a03b, 0xbaaedce6,
        0xfffffffe, 0xffffffff,
        0xffffffff, 0xffffffff,
    ]);
}

/// Transaction to be verified by the TxCircuit
#[derive(Clone, Default, Debug)]
pub struct Transaction {
    /// Sender address
    pub from: Address,

    /// Recipient address (None for contract creation)
    pub to: Option<Address>,

    /// Supplied gas
    pub gas: U256,

    /// Gas price
    pub gas_price: U256,

    /// Transfered value (None for no transfer)
    pub value: U256,

    /// The compiled code of a contract OR the first 4 bytes of the hash of the
    /// invoked method signature and encoded parameters. For details see
    /// Ethereum Contract ABI
    pub data: Bytes,

    /// Transaction nonce
    pub nonce: U256,

    /// "v" value of the transaction signature
    pub v: u64,
    /// "r" value of the transaction signature
    pub r: U256,
    /// "s" value of the transaction signature
    pub s: U256,
}

fn random_linear_combine<F: Field>(bytes: [u8; 32], randomness: F) -> F {
    crate::evm_circuit::util::Word::random_linear_combine(bytes, randomness)
}

fn recover_pk(v: u8, r: &Word, s: &Word, msg_hash: &[u8; 32]) -> Result<Secp256k1Affine, Error> {
    let r_be = r.to_be_bytes();
    let s_be = s.to_be_bytes();
    let mut r = libsecp256k1::curve::Scalar::from_int(0);
    let r_overflow: bool = r.set_b32(&r_be).into();
    let mut s = libsecp256k1::curve::Scalar::from_int(0);
    let s_overflow: bool = s.set_b32(&s_be).into();
    if r_overflow || s_overflow {
        error!("Overflow on 'r' or 's' signature values");
        return Err(Error::Synthesis);
    }
    let signature = libsecp256k1::Signature { r, s };
    let msg_hash = libsecp256k1::Message::parse_slice(msg_hash.as_slice()).map_err(|e| {
        error!("Message hash parsing from slice failed: {:?}", e);
        Error::Synthesis
    })?;
    let recovery_id = libsecp256k1::RecoveryId::parse(v).map_err(|e| {
        error!("secp256k1::RecoveriId::parse error: {:?}", e);
        Error::Synthesis
    })?;
    let pk = libsecp256k1::recover(&msg_hash, &signature, &recovery_id).map_err(|e| {
        error!("Public key recovery failed: {:?}", e);
        Error::Synthesis
    })?;
    let pk_be = pk.serialize();
    let mut pk_le = [0u8; 64];
    pk_le.copy_from_slice(&pk_be[1..]);
    pk_le[..32].reverse();
    pk_le[32..].reverse();
    let mut pk_bytes = secp256k1::Serialized::default();
    pk_bytes.as_mut().copy_from_slice(&pk_le[..]);
    let pk = Secp256k1Affine::from_bytes(&pk_bytes);
    ct_option_ok_or(pk, Error::Synthesis).map_err(|e| {
        error!("Invalid public key little endian bytes");
        e
    })
}

fn biguint_to_32bytes_le(v: BigUint) -> [u8; 32] {
    let mut res = [0u8; 32];
    let v_le = v.to_bytes_le();
    res[..v_le.len()].copy_from_slice(&v_le);
    res
}

fn ct_option_ok_or<T, E>(v: CtOption<T>, err: E) -> Result<T, E> {
    Option::<T>::from(v).ok_or(err)
}

fn tx_to_sign_data(tx: &Transaction, chain_id: u64) -> Result<SignData, Error> {
    let sig_r_le = tx.r.to_le_bytes();
    let sig_s_le = tx.s.to_le_bytes();
    let sig_r =
        ct_option_ok_or(secp256k1::Fq::from_repr(sig_r_le), Error::Synthesis).map_err(|e| {
            error!("Invalid 'r' signature value");
            e
        })?;
    let sig_s =
        ct_option_ok_or(secp256k1::Fq::from_repr(sig_s_le), Error::Synthesis).map_err(|e| {
            error!("Invalid 's' signature value");
            e
        })?;
    // msg = rlp([nonce, gasPrice, gas, to, value, data, sig_v, r, s])
    let mut stream = RlpStream::new_list(9);
    stream
        .append(&tx.nonce)
        .append(&tx.gas_price)
        .append(&tx.gas)
        .append(&tx.to.unwrap_or_else(Address::zero))
        .append(&tx.value)
        .append(&tx.data.0)
        .append(&chain_id)
        .append(&0u32)
        .append(&0u32);
    let msg = stream.out();
    let msg_hash: [u8; 32] = Keccak256::digest(&msg)
        .as_slice()
        .to_vec()
        .try_into()
        .expect("hash length isn't 32 bytes");
    let v = (tx.v - 35 - chain_id * 2) as u8;
    let pk = recover_pk(v, &tx.r, &tx.s, &msg_hash)?;
    // msg_hash = msg_hash % q
    let msg_hash = BigUint::from_bytes_be(msg_hash.as_slice());
    let msg_hash = msg_hash.mod_floor(&*SECP256K1_Q);
    let msg_hash_le = biguint_to_32bytes_le(msg_hash);
    let msg_hash = ct_option_ok_or(secp256k1::Fq::from_repr(msg_hash_le), Error::Synthesis)
        .map_err(|e| {
            error!("Invalid msg hash value");
            e
        })?;
    Ok(SignData {
        signature: (sig_r, sig_s),
        pk,
        msg_hash,
    })
}

// TODO: Deduplicate with
// `zkevm-circuits/src/evm_circuit/table.rs::TxContextFieldTag`.
/// Tag used to identify each field in the transaction in a row of the
/// transaction table.
#[derive(Clone, Copy, Debug)]
pub enum TxFieldTag {
    /// Unused tag
    Null = 0,
    /// Nonce
    Nonce,
    /// Gas
    Gas,
    /// GasPrice
    GasPrice,
    /// CallerAddress
    CallerAddress,
    /// CalleeAddress
    CalleeAddress,
    /// IsCreate
    IsCreate,
    /// Value
    Value,
    /// CallDataLength
    CallDataLength,
    /// TxSignHash: Hash of the transaction without the signature, used for
    /// signing.
    TxSignHash,
    /// CallData
    CallData,
}

#[derive(Clone, Debug)]
struct TxCircuitConfig<F: Field> {
    tx_id: Column<Advice>,
    tag: Column<Advice>,
    index: Column<Advice>,
    value: Column<Advice>,
    sign_verify: SignVerifyConfig<F>,
    _marker: PhantomData<F>,
}

impl<F: Field> TxCircuitConfig<F> {
    fn new(meta: &mut ConstraintSystem<F>) -> Self {
        let tx_id = meta.advice_column();
        let tag = meta.advice_column();
        let index = meta.advice_column();
        let value = meta.advice_column();
        meta.enable_equality(value);

        // This gate is used just to get the array of expressions from the power of
        // randomness instance column, so that later on we don't need to query
        // columns everywhere, and can pass the power of randomness array
        // expression everywhere.  The gate itself doesn't add any constraints.
        let power_of_randomness = {
            let columns = [(); sign_verify::POW_RAND_SIZE].map(|_| meta.instance_column());
            let mut power_of_randomness = None;

            meta.create_gate("power of randomness", |meta| {
                power_of_randomness =
                    Some(columns.map(|column| meta.query_instance(column, Rotation::cur())));

                [0.expr()]
            });

            power_of_randomness.unwrap()
        };
        let sign_verify = SignVerifyConfig::new(meta, power_of_randomness);

        Self {
            tx_id,
            tag,
            index,
            value,
            sign_verify,
            _marker: PhantomData,
        }
    }
}

#[derive(Default)]
struct TxCircuit<F: Field, const MAX_TXS: usize, const MAX_CALLDATA: usize> {
    sign_verify: SignVerifyChip<F, MAX_TXS>,
    randomness: F,
    txs: Vec<Transaction>,
    chain_id: u64,
}

/// Assigns a tx circuit row and returns the assigned cell of the value in
/// the row.
fn assign_row<F: Field>(
    region: &mut Region<'_, F>,
    config: &TxCircuitConfig<F>,
    offset: usize,
    tx_id: usize,
    tag: TxFieldTag,
    index: usize,
    value: F,
) -> Result<AssignedCell<F, F>, Error> {
    region.assign_advice(
        || "tx_id",
        config.tx_id,
        offset,
        || Ok(F::from(tx_id as u64)),
    )?;
    region.assign_advice(|| "tag", config.tag, offset, || Ok(F::from(tag as u64)))?;
    region.assign_advice(
        || "index",
        config.index,
        offset,
        || Ok(F::from(index as u64)),
    )?;
    region.assign_advice(|| "value", config.value, offset, || Ok(value))
}

impl<F: Field, const MAX_TXS: usize, const MAX_CALLDATA: usize> Circuit<F>
    for TxCircuit<F, MAX_TXS, MAX_CALLDATA>
{
    type Config = TxCircuitConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        TxCircuitConfig::new(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        assert!(self.txs.len() <= MAX_TXS);
        let sign_datas: Vec<SignData> = self
            .txs
            .iter()
            .map(|tx| {
                tx_to_sign_data(tx, self.chain_id).map_err(|e| {
                    error!("tx_to_sign_data error for tx {:?}", tx);
                    e
                })
            })
            .try_collect()?;
        let assigned_sig_verifs = self.sign_verify.assign_txs(
            &config.sign_verify,
            &mut layouter,
            self.randomness,
            &sign_datas,
        )?;

        layouter.assign_region(
            || "tx table",
            |mut region| {
                let mut offset = 0;
                // Empty entry
                assign_row(
                    &mut region,
                    &config,
                    offset,
                    0,
                    TxFieldTag::Null,
                    0,
                    F::zero(),
                )?;
                offset += 1;
                // Assign al Tx fields except for call data
                let tx_default = Transaction::default();
                // for i in 0..MAX_TXS
                for (i, assigned_sig_verif) in assigned_sig_verifs.iter().enumerate() {
                    let tx = if i < self.txs.len() {
                        &self.txs[i]
                    } else {
                        &tx_default
                    };
                    let address_cell = assigned_sig_verif.address.cell();
                    let msg_hash_rlc_cell = assigned_sig_verif.msg_hash_rlc.cell();
                    let msg_hash_rlc_value = assigned_sig_verif.msg_hash_rlc.value();
                    for (tag, value) in &[
                        (
                            TxFieldTag::Nonce,
                            random_linear_combine(tx.nonce.to_le_bytes(), self.randomness),
                        ),
                        (
                            TxFieldTag::Gas,
                            random_linear_combine(tx.gas.to_le_bytes(), self.randomness),
                        ),
                        (
                            TxFieldTag::GasPrice,
                            random_linear_combine(tx.gas_price.to_le_bytes(), self.randomness),
                        ),
                        (
                            TxFieldTag::CallerAddress,
                            tx.from.to_scalar().expect("tx.from too big"),
                        ),
                        (
                            TxFieldTag::CalleeAddress,
                            tx.to
                                .unwrap_or_else(Address::zero)
                                .to_scalar()
                                .expect("tx.to too big"),
                        ),
                        (TxFieldTag::IsCreate, F::from(tx.to.is_none() as u64)),
                        (
                            TxFieldTag::Value,
                            random_linear_combine(tx.value.to_le_bytes(), self.randomness),
                        ),
                        (TxFieldTag::CallDataLength, F::from(tx.data.0.len() as u64)),
                        (
                            TxFieldTag::TxSignHash,
                            *msg_hash_rlc_value.unwrap_or(&F::zero()),
                        ),
                    ] {
                        let assigned_cell =
                            assign_row(&mut region, &config, offset, i + 1, *tag, 0, *value)?;
                        offset += 1;

                        // Ref. spec 0. Copy constraints using fixed offsets between the tx rows and
                        // the SignVerifyChip
                        match tag {
                            TxFieldTag::CallerAddress => {
                                region.constrain_equal(assigned_cell.cell(), address_cell)?
                            }
                            TxFieldTag::TxSignHash => {
                                region.constrain_equal(assigned_cell.cell(), msg_hash_rlc_cell)?
                            }
                            _ => (),
                        }
                    }
                }

                // Assign call data
                let mut calldata_count = 0;
                for (i, tx) in self.txs.iter().enumerate() {
                    for (index, byte) in tx.data.0.iter().enumerate() {
                        assert!(calldata_count < MAX_CALLDATA);
                        assign_row(
                            &mut region,
                            &config,
                            offset,
                            i + 1, // tx_id
                            TxFieldTag::CallData,
                            index,
                            F::from(*byte as u64),
                        )?;
                        offset += 1;
                        calldata_count += 1;
                    }
                }
                for _ in calldata_count..MAX_CALLDATA {
                    assign_row(
                        &mut region,
                        &config,
                        offset,
                        0, // tx_id
                        TxFieldTag::CallData,
                        0,
                        F::zero(),
                    )?;
                    offset += 1;
                }
                Ok(())
            },
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tx_circuit_tests {
    use super::*;
    use ethers_core::{
        types::{NameOrAddress, TransactionRequest},
        utils::keccak256,
    };
    use ethers_signers::{LocalWallet, Signer};
    use group::{Curve, Group};
    use halo2_proofs::{arithmetic::CurveAffine, dev::MockProver, pairing::bn256::Fr};
    use pretty_assertions::assert_eq;
    use rand::{CryptoRng, Rng, SeedableRng};
    use rand_chacha::ChaCha20Rng;

    fn run<F: Field, const MAX_TXS: usize, const MAX_CALLDATA: usize>(
        k: u32,
        txs: Vec<Transaction>,
        chain_id: u64,
    ) {
        let mut rng = ChaCha20Rng::seed_from_u64(2);
        let aux_generator =
            <Secp256k1Affine as CurveAffine>::CurveExt::random(&mut rng).to_affine();

        let randomness = F::random(&mut rng);
        let mut power_of_randomness: Vec<Vec<F>> = (1..POW_RAND_SIZE + 1)
            .map(|exp| vec![randomness.pow(&[exp as u64, 0, 0, 0]); txs.len() * VERIF_HEIGHT])
            .collect();
        // SignVerifyChip -> ECDSAChip -> MainGate instance column
        power_of_randomness.push(vec![]);
        let circuit = TxCircuit::<F, MAX_TXS, MAX_CALLDATA> {
            sign_verify: SignVerifyChip {
                aux_generator,
                window_size: 2,
                _marker: PhantomData,
            },
            randomness,
            txs,
            chain_id,
        };

        let prover = match MockProver::run(k, &circuit, power_of_randomness) {
            Ok(prover) => prover,
            Err(e) => panic!("{:#?}", e),
        };
        assert_eq!(prover.verify(), Ok(()));
    }

    fn rand_tx<R: Rng + CryptoRng>(mut rng: R, chain_id: u64) -> Transaction {
        let wallet0 = LocalWallet::new(&mut rng).with_chain_id(chain_id);
        let wallet1 = LocalWallet::new(&mut rng).with_chain_id(chain_id);
        let from = wallet0.address();
        let to = wallet1.address();
        let data = b"hello";
        let tx = TransactionRequest::new()
            .from(from)
            .to(to)
            .nonce(3)
            .value(1000)
            .data(data)
            .gas(500_000)
            .gas_price(1234);
        let tx_rlp = tx.rlp(chain_id);
        let sighash = keccak256(tx_rlp.as_ref()).into();
        let sig = wallet0.sign_hash(sighash, true);
        let to = tx.to.map(|to| match to {
            NameOrAddress::Address(a) => a,
            _ => unreachable!(),
        });
        Transaction {
            from: tx.from.unwrap(),
            to,
            gas: tx.gas.unwrap(),
            gas_price: tx.gas_price.unwrap(),
            value: tx.value.unwrap(),
            data: tx.data.unwrap(),
            nonce: tx.nonce.unwrap(),
            v: sig.v,
            r: sig.r,
            s: sig.s,
        }
    }

    #[ignore]
    #[test]
    fn serial_test_tx_circuit() {
        const NUM_TXS: usize = 2;
        const MAX_TXS: usize = 2;
        const MAX_CALLDATA: usize = 32;

        let mut rng = ChaCha20Rng::seed_from_u64(2);
        let chain_id: u64 = 1337;
        let mut txs = Vec::new();
        for _ in 0..NUM_TXS {
            txs.push(rand_tx(&mut rng, chain_id));
        }

        let k = 19;
        run::<Fr, MAX_TXS, MAX_CALLDATA>(k, txs, chain_id);
    }
}
