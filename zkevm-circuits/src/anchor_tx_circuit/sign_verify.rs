//! # How to check the signature
//!
//! 1. IF r == GX1 OR r == GX2
//! 2. IF r == GX2 THEN MUST CHECK IF s == 0 when r = GX1
//! 3. IF s == 0 THEN GX1_MUL_PRIVATEKEY + msg_hash == N
//!
//! So, IF r == GX2 THEN GX1_MUL_PRIVATEKEY + msg_hash == N
//!
//! ## Why we only need to prove the equation: GX1_MUL_PRIVATEKEY + msg_hash == N
//!
//! based on the algorithm of [taiko-mono](https://github.com/taikoxyz/taiko-mono/blob/ad26803e5bcbcc76b812084b7bd08f45992e59dd/packages/protocol/contracts/libs/LibAnchorSignature.sol#L68)
//!
//! ### The formula of signature with K = 1
//!
//! ```
//! s = (GX1 * GOLDEN_TOUCH_PRIVATEKEY + msg_hash) (mod N) (K = 1)
//! ```
//!
//! #### Formula deformation
//!
//! ```
//! s = (GX1 * GOLDEN_TOUCH_PRIVATEKEY (mod N) + msg_hash (mod N)) (mod N)
//! ```
//!
//! - Our `GX1_MUL_PRIVATEKEY` is equal to `GX1 * GOLDEN_TOUCH_PRIVATEKEY (mod N)`
//! - Our `msg_hash` has already been (mod N) in [zkevm-circuit](https://github.com/taikoxyz/zkevm-circuits/blob/839152c04ab3ddd1b8ce32632a407e5e7ef823a8/eth-types/src/geth_types.rs#L236)
//!
//! ```rust
//! let msg_hash = msg_hash.mod_floor(&*SECP256K1_Q);
//! ```
//!
//! ### Summary
//!
//! ```
//! because: 0 < GX1_MUL_PRIVATEKEY + msg_hash < 2N
//! need prove: (GX1_MUL_PRIVATEKEY + msg_hash) (mod N) == 0
//! so: GX1_MUL_PRIVATEKEY + msg_hash == N
//! ```

use crate::{
    evm_circuit::util::{
        constraint_builder::{BaseConstraintBuilder, ConstrainBuilderCommon},
        rlc, split_u256_limb64,
    },
    table::{byte_table::ByteTable, LookupTable, TxFieldTag, TxTable},
    util::Challenges,
    witness::Transaction,
};
use eth_types::{address, word, Address, Field, ToBigEndian, ToLittleEndian, Word, U256};
use ethers_signers::LocalWallet;
use gadgets::{
    is_equal::{IsEqualChip, IsEqualConfig, IsEqualInstruction},
    mul_add::{MulAddChip, MulAddConfig},
    util::{split_u256, Expr},
};
use halo2_proofs::{
    circuit::{Layouter, Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed, SecondPhase, Selector},
    poly::Rotation,
};
use once_cell::sync::Lazy;
use std::str::FromStr;

const MAX_DEGREE: usize = 9;
const BYTE_POW_BASE: u64 = 1 << 8;

pub(crate) static GOLDEN_TOUCH_ADDRESS: Lazy<Address> =
    Lazy::new(|| address!("0x0000777735367b36bC9B61C50022d9D0700dB4Ec"));

// 0x92954368afd3caa1f3ce3ead0069c1af414054aefe1ef9aeacc1bf426222ce38
pub(crate) static GOLDEN_TOUCH_PRIVATEKEY: Lazy<Word> =
    Lazy::new(|| word!("0x92954368afd3caa1f3ce3ead0069c1af414054aefe1ef9aeacc1bf426222ce38"));

pub(crate) static GOLDEN_TOUCH_WALLET: Lazy<LocalWallet> = Lazy::new(|| {
    LocalWallet::from_str("0x92954368afd3caa1f3ce3ead0069c1af414054aefe1ef9aeacc1bf426222ce38")
        .unwrap()
});

// 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
pub(crate) static GX1: Lazy<Word> =
    Lazy::new(|| word!("0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798"));
static GX1_LO_HI: Lazy<(U256, U256)> = Lazy::new(|| split_u256(&GX1));

// 0xc6047f9441ed7d6d3045406e95c07cd85c778e4b8cef3ca7abac09b95c709ee5
pub(crate) static GX2: Lazy<Word> =
    Lazy::new(|| word!("0xc6047f9441ed7d6d3045406e95c07cd85c778e4b8cef3ca7abac09b95c709ee5"));
static GX2_LO_HI: Lazy<(U256, U256)> = Lazy::new(|| split_u256(&GX2));

// 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141
pub(crate) static N: Lazy<Word> =
    Lazy::new(|| word!("0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141"));
static N_LO_HI: Lazy<(U256, U256)> = Lazy::new(|| split_u256(&N));

// private key 0x92954368afd3caa1f3ce3ead0069c1af414054aefe1ef9aeacc1bf426222ce38
// GX1 * PRIVATEKEY(mod N) = 0x4341adf5a780b4a87939938fd7a032f6e6664c7da553c121d3b4947429639122
pub(crate) static GX1_MUL_PRIVATEKEY: Lazy<Word> =
    Lazy::new(|| word!("0x4341adf5a780b4a87939938fd7a032f6e6664c7da553c121d3b4947429639122"));
static GX1_MUL_PRIVATEKEY_LO_HI: Lazy<(U256, U256)> = Lazy::new(|| split_u256(&GX1_MUL_PRIVATEKEY));
static GX1_MUL_PRIVATEKEY_LIMB64: Lazy<[U256; 4]> =
    Lazy::new(|| split_u256_limb64(&GX1_MUL_PRIVATEKEY));

// GX2 * PRIVATEKEY(mod N) = 0x4a43b192ca74cab200d6c086df90fb729abca9e52d38b8fa0beb4eafe70956de
static GX2_MUL_PRIVATEKEY: Lazy<Word> =
    Lazy::new(|| word!("0x4a43b192ca74cab200d6c086df90fb729abca9e52d38b8fa0beb4eafe70956de"));
static GX2_MUL_PRIVATEKEY_LO_HI: Lazy<(U256, U256)> = Lazy::new(|| split_u256(&GX2_MUL_PRIVATEKEY));

// # The circuit layout
// - msg_hash (c)
// - SigR
//
// We don't have to verify `s` and `v` of the signature, because the signature needs to be valid and
// and those values are fixed if `r` is fixed.
// `msg_hash` is calculated and verified in the tx circuit like any other transaction.

#[derive(Debug, Clone)]
pub(crate) struct SignVerifyConfig<F: Field> {
    tx_table: TxTable,

    q_sig_start: Selector,
    q_sig_step: Selector,
    q_sig_end: Selector,
    tag: Column<Fixed>,
    sig: Column<Advice>,
    sig_rlc_acc: Column<Advice>,

    // split u256 into 4 64bit limbs
    q_u64_start: Selector,
    q_u64_step: Selector,
    q_u64_end: Selector,
    sig_u64_acc: Column<Advice>,

    q_check: Selector,
    mul_add: MulAddConfig<F>,
    is_equal_gx2: IsEqualConfig<F>,
}

impl<F: Field> SignVerifyConfig<F> {
    pub(crate) fn configure(
        meta: &mut ConstraintSystem<F>,
        tx_table: TxTable,
        byte_table: ByteTable,
        challenges: &Challenges<Expression<F>>,
    ) -> Self {
        let q_sig_start = meta.complex_selector();
        let q_sig_step = meta.complex_selector();
        let q_sig_end = meta.complex_selector();
        let tag = meta.fixed_column();
        let sig = meta.advice_column();
        let sig_rlc_acc = meta.advice_column_in(SecondPhase);

        let q_u64_start = meta.complex_selector();
        let q_u64_step = meta.complex_selector();
        let q_u64_end = meta.complex_selector();
        let sig_u64_acc = meta.advice_column();

        // RLC of GX1 bytes
        let gx1_rlc = rlc::expr(
            GX1.to_le_bytes()
                .map(|v| Expression::Constant(F::from(v as u64)))
                .as_ref(),
            challenges.evm_word(),
        );
        // RLC of GX2 bytes
        let gx2_rlc = rlc::expr(
            GX2.to_le_bytes()
                .map(|v| Expression::Constant(F::from(v as u64)))
                .as_ref(),
            challenges.evm_word(),
        );

        // Check if R == GX2
        let q_check = meta.complex_selector();
        let is_equal_gx2 = IsEqualChip::configure(
            meta,
            |meta| meta.advice_column_in(SecondPhase),
            |meta| meta.query_selector(q_check),
            |meta| meta.query_advice(sig_rlc_acc, Rotation(63)), // SigR == GX2
            |_| gx2_rlc.expr(),
        );
        // Only enable the mul_add constraints when r == GX2
        let mul_add = MulAddChip::configure(meta, |meta| {
            is_equal_gx2.is_equal_expression.expr() * meta.query_selector(q_check)
        });

        // RLC the signature data (per part) (all bytes except the first one)
        meta.create_gate(
            "sig_rlc_acc[i+1] = sig_rlc_acc[i] * randomness + sig[i+1]",
            |meta| {
                let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);

                let q_sig_step = meta.query_selector(q_sig_step);
                let sig_rlc_acc_next = meta.query_advice(sig_rlc_acc, Rotation::next());
                let sig_rlc_acc = meta.query_advice(sig_rlc_acc, Rotation::cur());
                let sign = meta.query_advice(sig, Rotation::next());
                let randomness = challenges.evm_word();
                cb.require_equal(
                    "sig_rlc_acc[i+1] = sig_rlc_acc[i] * randomness + sign[i+1]",
                    sig_rlc_acc_next,
                    sig_rlc_acc * randomness + sign,
                );
                cb.gate(q_sig_step)
            },
        );
        // RLC the signature data (per part) (first byte)
        meta.create_gate("sig_rlc_acc[0] = sign[0]", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);

            let q_sig_start = meta.query_selector(q_sig_start);
            let sig_rlc_acc = meta.query_advice(sig_rlc_acc, Rotation::cur());
            let sign = meta.query_advice(sig, Rotation::cur());

            cb.require_equal("sig_rlc_acc[0] = sign[0]", sig_rlc_acc, sign);
            cb.gate(q_sig_start)
        });

        // Make sure that `sig_r` and `msg_hash` have the correct value by looking up their RLCd
        // representations in the tx table.
        meta.lookup_any("sig_r or msg_hash in tx_table", |meta| {
            let q_sig_end = meta.query_selector(q_sig_end);

            let tx_id = super::ANCHOR_TX_ID.expr();
            let tag = meta.query_fixed(tag, Rotation::cur());
            let index = 0.expr();
            let value = meta.query_advice(sig_rlc_acc, Rotation::cur());

            [tx_id, tag, index, value]
                .into_iter()
                .zip(tx_table.table_exprs(meta).into_iter())
                .map(|(arg, table)| (q_sig_end.expr() * arg, table))
                .collect::<Vec<_>>()
        });

        // Decode the 4 64bit limbs of msg_hash and R (all bytes except the first one)
        meta.create_gate(
            "sig_u64_acc[i+1] = sig_u64_acc[i] * BYTE_POW_BASE + sig[i+1]",
            |meta| {
                let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);

                let q_u64_step = meta.query_selector(q_u64_step);
                let sig_u64_acc_next = meta.query_advice(sig_u64_acc, Rotation::next());
                let sig_u64_acc = meta.query_advice(sig_u64_acc, Rotation::cur());
                let sig_next = meta.query_advice(sig, Rotation::next());
                cb.require_equal(
                    "sig_u64_acc[i+1] = sig_u64_acc[i] * BYTE_POW_BASE + sig[i+1]",
                    sig_u64_acc_next,
                    sig_u64_acc * BYTE_POW_BASE.expr() + sig_next,
                );
                cb.gate(q_u64_step)
            },
        );
        // Decode the 4 64bit limbs of msg_hash and R (first byte)
        meta.create_gate("sig_u64_acc[start] = sig[start]", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);

            let q_u64_start = meta.query_selector(q_u64_start);
            let sig_u64_acc = meta.query_advice(sig_u64_acc, Rotation::cur());
            let sig = meta.query_advice(sig, Rotation::cur());

            cb.require_equal("sig_u64_acc[start] = sig[start]", sig_u64_acc, sig);
            cb.gate(q_u64_start)
        });

        // Check that R has the expected value
        meta.create_gate(
            "IF r == GX2 THEN a(msg_hash) * b(1) + c(GX1_MUL_PRIVATEKEY) == d(N)",
            |meta| {
                let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);

                // R needs to be either GX1 or Gx2
                let sig_rlc_acc = meta.query_advice(sig_rlc_acc, Rotation(63));
                cb.require_in_set("r in (GX1, GX2)", sig_rlc_acc, vec![gx1_rlc, gx2_rlc]);

                // In mul_add chip, we have a * b + c == d
                // => a == msg_hash
                // => b == 1
                // => c == GX1_MUL_PRIVATEKEY
                // => d == N
                // Check that the inputs a, b, and c into mul_add are correct
                // a == msg_hash
                let a = mul_add.a_limbs_cur(meta);
                cb.require_equal("a.0", a.0, meta.query_advice(sig_u64_acc, Rotation(31)));
                cb.require_equal("a.1", a.1, meta.query_advice(sig_u64_acc, Rotation(23)));
                cb.require_equal("a.2", a.2, meta.query_advice(sig_u64_acc, Rotation(15)));
                cb.require_equal("a.3", a.3, meta.query_advice(sig_u64_acc, Rotation(7)));
                // b == 1
                let b = mul_add.b_limbs_cur(meta);
                let one = split_u256_limb64(&U256::one())
                    .map(|v| Expression::Constant(F::from(v.as_u64())));
                cb.require_equal("b.0", b.0, one[0].expr());
                cb.require_equal("b.1", b.1, one[1].expr());
                cb.require_equal("b.2", b.2, one[2].expr());
                cb.require_equal("b.3", b.3, one[3].expr());
                // c == GX1_MUL_PRIVATEKEY
                let gx1_mul_privatekey_0 =
                    Expression::Constant(F::from_u128(GX1_MUL_PRIVATEKEY_LO_HI.0.as_u128()));
                let gx1_mul_privatekey_1 =
                    Expression::Constant(F::from_u128(GX1_MUL_PRIVATEKEY_LO_HI.1.as_u128()));
                let c = mul_add.c_lo_hi_cur(meta);
                cb.require_equal("c.0", c.0, gx1_mul_privatekey_0);
                cb.require_equal("c.1", c.1, gx1_mul_privatekey_1);

                // Now finally check that d == N
                let n_0 = Expression::Constant(F::from_u128(N_LO_HI.0.as_u128()));
                let n_1 = Expression::Constant(F::from_u128(N_LO_HI.1.as_u128()));
                let d = mul_add.d_lo_hi_cur(meta);
                cb.require_equal("d.0", d.0, n_0);
                cb.require_equal("d.1", d.1, n_1);

                cb.gate(meta.query_selector(q_check))
            },
        );

        // Range constraint all bytes
        meta.lookup_any("ensure all bytes are actually byte values", |meta| {
            let rpi_field_bytes = meta.query_advice(sig, Rotation::cur());
            [rpi_field_bytes]
                .into_iter()
                .zip(byte_table.table_exprs(meta).into_iter())
                .map(|(arg, table)| (arg, table))
                .collect::<Vec<_>>()
        });

        Self {
            tx_table,

            q_sig_start,
            q_sig_step,
            q_sig_end,
            tag,
            sig,
            sig_rlc_acc,

            q_u64_start,
            q_u64_step,
            q_u64_end,
            sig_u64_acc,

            q_check,
            mul_add,
            is_equal_gx2,
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn assign_field(
        &self,
        region: &mut Region<'_, F>,
        _annotation: &'static str,
        offset: &mut usize,
        tag: TxFieldTag,
        value: [u8; 32],
        challenges: &Challenges<Value<F>>,
    ) -> Result<Value<F>, Error> {
        let mut rlc_acc = Value::known(F::ZERO);
        let randomness = challenges.evm_word();

        let mut assign_u64 = |offset: &mut usize, value: &[u8]| -> Result<(), Error> {
            let mut u64_acc = Value::known(F::ZERO);
            for (idx, byte) in value.iter().enumerate() {
                let row_offset = *offset + idx;
                u64_acc = u64_acc * Value::known(F::from(BYTE_POW_BASE))
                    + Value::known(F::from(*byte as u64));
                region.assign_advice(|| "sig_u64_acc", self.sig_u64_acc, row_offset, || u64_acc)?;
                // setup selector
                if idx == 0 {
                    self.q_u64_start.enable(region, row_offset)?;
                }
                // the last offset of field
                if idx == 7 {
                    self.q_u64_end.enable(region, row_offset)?;
                } else {
                    self.q_u64_step.enable(region, row_offset)?;
                }
            }
            *offset += 8;
            Ok(())
        };

        let mut assign_u64_offset = *offset;
        assign_u64(&mut assign_u64_offset, &value[..8])?;
        assign_u64(&mut assign_u64_offset, &value[8..16])?;
        assign_u64(&mut assign_u64_offset, &value[16..24])?;
        assign_u64(&mut assign_u64_offset, &value[24..])?;

        for (idx, byte) in value.iter().enumerate() {
            let row_offset = *offset + idx;
            region.assign_advice(
                || "sig",
                self.sig,
                row_offset,
                || Value::known(F::from(*byte as u64)),
            )?;
            region.assign_fixed(
                || "tag",
                self.tag,
                row_offset,
                || Value::known(F::from(tag as u64)),
            )?;

            rlc_acc = rlc_acc * randomness + Value::known(F::from(*byte as u64));
            region.assign_advice(|| "sig_rlc_acc", self.sig_rlc_acc, row_offset, || rlc_acc)?;
            // setup selector
            if idx == 0 {
                self.q_sig_start.enable(region, row_offset)?;
            }
            // the last offset of field
            if idx == 31 {
                self.q_sig_end.enable(region, row_offset)?;
            } else {
                self.q_sig_step.enable(region, row_offset)?;
            }
        }
        *offset += 32;
        Ok(rlc_acc)
    }

    fn load_mul_add(&self, region: &mut Region<'_, F>, msg_hash: Word) -> Result<(), Error> {
        let chip = MulAddChip::construct(self.mul_add.clone());
        chip.assign(region, 0, [msg_hash, U256::one(), *GX1_MUL_PRIVATEKEY, *N])
    }

    /// Return the minimum number of rows required to prove an input of a
    /// particular size.
    pub(crate) fn min_num_rows() -> usize {
        64 // msg_hash(32B) + sign_r(32B)
    }

    pub(crate) fn assign(
        &self,
        layouter: &mut impl Layouter<F>,
        anchor_tx: &Transaction,
        challenges: &Challenges<Value<F>>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "anchor sign verify",
            |ref mut region| {
                self.q_check.enable(region, 0)?;

                let msg_hash = U256::from_little_endian(&anchor_tx.tx_sign_hash.to_fixed_bytes());
                self.load_mul_add(region, msg_hash)?;
                let mut offset = 0;
                for (annotation, tag, do_check_equal_to_gx2, value) in [
                    (
                        "msg_hash",
                        TxFieldTag::TxSignHash,
                        false,
                        msg_hash.to_be_bytes(),
                    ),
                    ("sig_r", TxFieldTag::SigR, true, anchor_tx.r.to_be_bytes()),
                ] {
                    let rlc_acc =
                        self.assign_field(region, annotation, &mut offset, tag, value, challenges)?;
                    if do_check_equal_to_gx2 {
                        let gx2_rlc = challenges
                            .evm_word()
                            .map(|randomness| rlc::value(&GX2.to_le_bytes(), randomness));
                        let chip = IsEqualChip::construct(self.is_equal_gx2.clone());
                        chip.assign(region, 0, rlc_acc, gx2_rlc)?;
                    }
                }
                Ok(())
            },
        )
    }
}
