use crate::{
    evm_circuit::util::{constraint_builder::BaseConstraintBuilder, not, rlc},
    keccak_circuit::util::compose_rlc,
    table::KeccakTable,
    util::Expr,
};
use eth_types::Field;
use gadgets::util::{and, select, sum, xor};
use halo2_proofs::{
    circuit::{Layouter, Region, SimpleFloorPlanner, Value},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, VirtualCells},
    poly::Rotation,
};
use log::{debug, info};
use std::{env::var, marker::PhantomData, vec};

const NUM_BITS_PER_BYTE: usize = 8;
const NUM_BYTES_PER_WORD: usize = 4;
const NUM_BITS_PER_WORD: usize = NUM_BYTES_PER_WORD * NUM_BITS_PER_BYTE;
const NUM_BITS_PER_WORD_W: usize = NUM_BITS_PER_WORD + 2;
const NUM_BITS_PER_WORD_EXT: usize = NUM_BITS_PER_WORD + 3;
const NUM_ROUNDS: usize = 64;
const RATE: usize = 16 * NUM_BYTES_PER_WORD;
const RATE_IN_BITS: usize = RATE * NUM_BITS_PER_BYTE;
const NUM_WORDS_TO_ABSORB: usize = 16;
const ABSORB_WIDTH_PER_ROW_BYTES: usize = 4;
const NUM_BITS_PADDING_LENGTH: usize = 64;
const NUM_START_ROWS: usize = 4;
const NUM_END_ROWS: usize = 4;

const MAX_DEGREE: usize = 5;

const ROUND_CST: [u32; NUM_ROUNDS] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

const H: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

/// Decodes be bits
pub mod decode {
    use eth_types::Field;
    use gadgets::util::Expr;
    use halo2_proofs::plonk::Expression;

    pub(crate) fn expr<F: Field>(bits: &[Expression<F>]) -> Expression<F> {
        let mut value = 0.expr();
        let mut multiplier = F::one();
        for bit in bits.iter().rev() {
            value = value + bit.expr() * multiplier;
            multiplier *= F::from(2);
        }
        value
    }

    pub(crate) fn value(bits: &[u8]) -> u64 {
        let mut value = 0u64;
        for (idx, &bit) in bits.iter().rev().enumerate() {
            value += (bit as u64) << idx;
        }
        value
    }
}

/// Rotates bits to the right
pub mod rotate {
    use eth_types::Field;
    use halo2_proofs::plonk::Expression;

    pub(crate) fn expr<F: Field>(bits: &[Expression<F>], count: usize) -> Vec<Expression<F>> {
        let mut rotated = bits.to_vec();
        rotated.rotate_right(count);
        rotated
    }

    pub(crate) fn value(value: u64, count: u32) -> u64 {
        ((value as u32).rotate_right(count)) as u64
    }
}

/// Shifts bits to the right
pub mod shift {
    use super::NUM_BITS_PER_WORD;
    use eth_types::Field;
    use gadgets::util::Expr;
    use halo2_proofs::plonk::Expression;

    pub(crate) fn expr<F: Field>(bits: &[Expression<F>], count: usize) -> Vec<Expression<F>> {
        let mut res = vec![0.expr(); count];
        res.extend_from_slice(&bits[0..NUM_BITS_PER_WORD - count]);
        res
    }

    pub(crate) fn value(value: u64, count: u32) -> u64 {
        ((value as u32) >> count) as u64
    }
}

/// Convert be bits to le bytes
pub mod to_le_bytes {
    use crate::keccak_circuit::util::to_bytes;
    use eth_types::Field;
    use halo2_proofs::plonk::Expression;

    pub(crate) fn expr<F: Field>(bits: &[Expression<F>]) -> Vec<Expression<F>> {
        to_bytes::expr(&bits.iter().rev().cloned().collect::<Vec<_>>())
            .into_iter()
            .rev()
            .collect::<Vec<_>>()
    }

    pub(crate) fn value(bits: &[u8]) -> Vec<u8> {
        to_bytes::value(&bits.iter().rev().copied().collect::<Vec<u8>>())
            .into_iter()
            .rev()
            .collect::<Vec<u8>>()
    }
}

/// Converts bytes into bits
fn into_bits(bytes: &[u8]) -> Vec<u8> {
    let mut bits: Vec<u8> = vec![0; bytes.len() * 8];
    for (byte_idx, byte) in bytes.iter().enumerate() {
        for idx in 0u64..8 {
            bits[byte_idx * 8 + (idx as usize)] = (*byte >> (7 - idx)) & 1;
        }
    }
    bits
}

fn get_degree() -> usize {
    var("DEGREE")
        .unwrap_or_else(|_| "8".to_string())
        .parse()
        .expect("Cannot parse DEGREE env var as usize")
}

#[derive(Clone, Debug, PartialEq)]
struct ShaRow<F> {
    w: [bool; NUM_BITS_PER_WORD_W],
    a: [bool; NUM_BITS_PER_WORD_EXT],
    e: [bool; NUM_BITS_PER_WORD_EXT],
    is_final: bool,
    length: usize,
    data_rlc: F,
    hash_rlc: F,
    is_paddings: [bool; ABSORB_WIDTH_PER_ROW_BYTES],
    data_rlcs: [F; ABSORB_WIDTH_PER_ROW_BYTES],
}

/// Sha256BitConfig
#[derive(Clone, Debug)]
pub struct Sha256BitConfig<F> {
    q_enable: Column<Fixed>,
    q_first: Column<Fixed>,
    q_extend: Column<Fixed>,
    q_start: Column<Fixed>,
    q_compression: Column<Fixed>,
    q_end: Column<Fixed>,
    q_padding: Column<Fixed>,
    q_padding_last: Column<Fixed>,
    q_squeeze: Column<Fixed>,
    word_w: [Column<Advice>; NUM_BITS_PER_WORD_W],
    word_a: [Column<Advice>; NUM_BITS_PER_WORD_EXT],
    word_e: [Column<Advice>; NUM_BITS_PER_WORD_EXT],
    is_final: Column<Advice>,
    is_paddings: [Column<Advice>; ABSORB_WIDTH_PER_ROW_BYTES],
    data_rlcs: [Column<Advice>; ABSORB_WIDTH_PER_ROW_BYTES],
    round_cst: Column<Fixed>,
    h_a: Column<Fixed>,
    h_e: Column<Fixed>,
    /// The columns for other circuits to lookup hash results
    pub hash_table: KeccakTable,
    _marker: PhantomData<F>,
}

/// Sha256BitCircuit
#[derive(Default)]
pub struct Sha256BitCircuit<F: Field> {
    witness: Vec<ShaRow<F>>,
    size: usize,
}

impl<F: Field> Sha256BitCircuit<F> {
    fn r() -> F {
        F::from(123456)
    }
}

impl<F: Field> Circuit<F> for Sha256BitCircuit<F> {
    type Config = Sha256BitConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        Sha256BitConfig::configure(meta, Sha256BitCircuit::r())
    }

    fn synthesize(&self, config: Self::Config, layouter: impl Layouter<F>) -> Result<(), Error> {
        config.assign(layouter, self.size, &self.witness)?;
        Ok(())
    }
}

impl<F: Field> Sha256BitCircuit<F> {
    /// Creates a new circuit instance
    pub fn new(size: usize) -> Self {
        Sha256BitCircuit {
            witness: Vec::new(),
            size,
        }
    }

    /// The number of sha256 permutations that can be done in this circuit
    pub fn capacity(&self) -> usize {
        // Subtract one for unusable rows
        self.size / (NUM_ROUNDS + 8) - 1
    }

    /// Sets the witness using the data to be hashed
    pub fn generate_witness(&mut self, inputs: &[Vec<u8>]) {
        self.witness = multi_sha256(inputs, Sha256BitCircuit::r());
    }

    /// Sets the witness using the witness data directly
    fn set_witness(&mut self, witness: &[ShaRow<F>]) {
        self.witness = witness.to_vec();
    }
}

impl<F: Field> Sha256BitConfig<F> {
    pub(crate) fn configure(meta: &mut ConstraintSystem<F>, r: F) -> Self {
        let q_enable = meta.fixed_column();
        let q_first = meta.fixed_column();
        let q_extend = meta.fixed_column();
        let q_start = meta.fixed_column();
        let q_compression = meta.fixed_column();
        let q_end = meta.fixed_column();
        let q_padding = meta.fixed_column();
        let q_padding_last = meta.fixed_column();
        let q_squeeze = meta.fixed_column();
        let word_w = array_init::array_init(|_| meta.advice_column());
        let word_a = array_init::array_init(|_| meta.advice_column());
        let word_e = array_init::array_init(|_| meta.advice_column());
        let is_final = meta.advice_column();
        let is_paddings = array_init::array_init(|_| meta.advice_column());
        let data_rlcs = array_init::array_init(|_| meta.advice_column());
        let round_cst = meta.fixed_column();
        let h_a = meta.fixed_column();
        let h_e = meta.fixed_column();
        let hash_table = KeccakTable::construct(meta);
        let is_enabled = hash_table.is_enabled;
        let length = hash_table.input_len;
        let data_rlc = hash_table.input_rlc;
        let hash_rlc = hash_table.output_rlc;

        // State bits
        let mut w_ext = vec![0u64.expr(); NUM_BITS_PER_WORD_W];
        let mut w_2 = vec![0u64.expr(); NUM_BITS_PER_WORD];
        let mut w_7 = vec![0u64.expr(); NUM_BITS_PER_WORD];
        let mut w_15 = vec![0u64.expr(); NUM_BITS_PER_WORD];
        let mut w_16 = vec![0u64.expr(); NUM_BITS_PER_WORD];
        let mut a = vec![0u64.expr(); NUM_BITS_PER_WORD];
        let mut b = vec![0u64.expr(); NUM_BITS_PER_WORD];
        let mut c = vec![0u64.expr(); NUM_BITS_PER_WORD];
        let mut d = vec![0u64.expr(); NUM_BITS_PER_WORD];
        let mut e = vec![0u64.expr(); NUM_BITS_PER_WORD];
        let mut f = vec![0u64.expr(); NUM_BITS_PER_WORD];
        let mut g = vec![0u64.expr(); NUM_BITS_PER_WORD];
        let mut h = vec![0u64.expr(); NUM_BITS_PER_WORD];
        let mut d_64 = vec![0u64.expr(); NUM_BITS_PER_WORD];
        let mut h_64 = vec![0u64.expr(); NUM_BITS_PER_WORD];
        let mut new_a_ext = vec![0u64.expr(); NUM_BITS_PER_WORD_EXT];
        let mut new_e_ext = vec![0u64.expr(); NUM_BITS_PER_WORD_EXT];
        meta.create_gate("Query state bits", |meta| {
            for k in 0..NUM_BITS_PER_WORD_W {
                w_ext[k] = meta.query_advice(word_w[k], Rotation(-0));
            }
            for i in 0..NUM_BITS_PER_WORD {
                let k = i + NUM_BITS_PER_WORD_W - NUM_BITS_PER_WORD;
                w_2[i] = meta.query_advice(word_w[k], Rotation(-2));
                w_7[i] = meta.query_advice(word_w[k], Rotation(-7));
                w_15[i] = meta.query_advice(word_w[k], Rotation(-15));
                w_16[i] = meta.query_advice(word_w[k], Rotation(-16));
                let k = i + NUM_BITS_PER_WORD_EXT - NUM_BITS_PER_WORD;
                a[i] = meta.query_advice(word_a[k], Rotation(-1));
                b[i] = meta.query_advice(word_a[k], Rotation(-2));
                c[i] = meta.query_advice(word_a[k], Rotation(-3));
                d[i] = meta.query_advice(word_a[k], Rotation(-4));
                e[i] = meta.query_advice(word_e[k], Rotation(-1));
                f[i] = meta.query_advice(word_e[k], Rotation(-2));
                g[i] = meta.query_advice(word_e[k], Rotation(-3));
                h[i] = meta.query_advice(word_e[k], Rotation(-4));
                d_64[i] = meta.query_advice(word_a[k], Rotation(-((NUM_ROUNDS + 4) as i32)));
                h_64[i] = meta.query_advice(word_e[k], Rotation(-((NUM_ROUNDS + 4) as i32)));
            }
            for k in 0..NUM_BITS_PER_WORD_EXT {
                new_a_ext[k] = meta.query_advice(word_a[k], Rotation(0));
                new_e_ext[k] = meta.query_advice(word_e[k], Rotation(0));
            }
            vec![0u64.expr()]
        });
        let w = &w_ext[NUM_BITS_PER_WORD_W - NUM_BITS_PER_WORD..NUM_BITS_PER_WORD_W];
        let new_a = &new_a_ext[NUM_BITS_PER_WORD_EXT - NUM_BITS_PER_WORD..NUM_BITS_PER_WORD_EXT];
        let new_e = &new_e_ext[NUM_BITS_PER_WORD_EXT - NUM_BITS_PER_WORD..NUM_BITS_PER_WORD_EXT];

        let xor = |a: &[Expression<F>], b: &[Expression<F>]| {
            debug_assert_eq!(a.len(), b.len(), "invalid length");
            let mut c = vec![0.expr(); a.len()];
            for (idx, (a, b)) in a.iter().zip(b.iter()).enumerate() {
                c[idx] = xor::expr(a, b);
            }
            c
        };

        let select =
            |c: &[Expression<F>], when_true: &[Expression<F>], when_false: &[Expression<F>]| {
                debug_assert_eq!(c.len(), when_true.len(), "invalid length");
                debug_assert_eq!(c.len(), when_false.len(), "invalid length");
                let mut r = vec![0.expr(); c.len()];
                for (idx, (c, (when_true, when_false))) in c
                    .iter()
                    .zip(when_true.iter().zip(when_false.iter()))
                    .enumerate()
                {
                    r[idx] = select::expr(c.clone(), when_true.clone(), when_false.clone());
                }
                r
            };

        meta.create_gate("input checks", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
            for w in w_ext.iter() {
                cb.require_boolean("w bit boolean", w.clone());
            }
            for a in new_a_ext.iter() {
                cb.require_boolean("a bit boolean", a.clone());
            }
            for e in new_e_ext.iter() {
                cb.require_boolean("e bit boolean", e.clone());
            }
            cb.gate(meta.query_fixed(q_enable, Rotation::cur()))
        });

        meta.create_gate("w extend", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
            let s0 = xor(
                &rotate::expr(&w_15, 7),
                &xor(&rotate::expr(&w_15, 18), &shift::expr(&w_15, 3)),
            );
            let s1 = xor(
                &rotate::expr(&w_2, 17),
                &xor(&rotate::expr(&w_2, 19), &shift::expr(&w_2, 10)),
            );
            let new_w =
                decode::expr(&w_16) + decode::expr(&s0) + decode::expr(&w_7) + decode::expr(&s1);
            cb.require_equal("w", new_w, decode::expr(&w_ext));
            cb.gate(meta.query_fixed(q_extend, Rotation::cur()))
        });

        meta.create_gate("compression", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
            let s1 = xor(
                &rotate::expr(&e, 6),
                &xor(&rotate::expr(&e, 11), &rotate::expr(&e, 25)),
            );
            let ch = select(&e, &f, &g);
            let temp1 = decode::expr(&h)
                + decode::expr(&s1)
                + decode::expr(&ch)
                + meta.query_fixed(round_cst, Rotation::cur())
                + decode::expr(w);

            let s0 = xor(
                &rotate::expr(&a, 2),
                &xor(&rotate::expr(&a, 13), &rotate::expr(&a, 22)),
            );
            let maj = select(&xor(&b, &c), &a, &b);
            let temp2 = decode::expr(&s0) + decode::expr(&maj);
            cb.require_equal(
                "compress a",
                decode::expr(&new_a_ext),
                temp1.clone() + temp2,
            );
            cb.require_equal(
                "compress e",
                decode::expr(&new_e_ext),
                decode::expr(&d) + temp1,
            );
            cb.gate(meta.query_fixed(q_compression, Rotation::cur()))
        });

        meta.create_gate("start", |meta| {
            let is_final = meta.query_advice(is_final, Rotation::cur());
            let h_a = meta.query_fixed(h_a, Rotation::cur());
            let h_e = meta.query_fixed(h_e, Rotation::cur());
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
            cb.require_equal(
                "start a",
                decode::expr(&new_a_ext),
                select::expr(is_final.expr(), h_a, decode::expr(&d)),
            );
            cb.require_equal(
                "start e",
                decode::expr(&new_e_ext),
                select::expr(is_final.expr(), h_e, decode::expr(&h)),
            );
            cb.gate(meta.query_fixed(q_start, Rotation::cur()))
        });

        meta.create_gate("end", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
            cb.require_equal(
                "end a",
                decode::expr(&new_a_ext),
                decode::expr(&d) + decode::expr(&d_64),
            );
            cb.require_equal(
                "end e",
                decode::expr(&new_e_ext),
                decode::expr(&h) + decode::expr(&h_64),
            );
            cb.gate(meta.query_fixed(q_end, Rotation::cur()))
        });

        // Enforce logic for when this block is the last block for a hash
        meta.create_gate("is final", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
            let is_padding = meta.query_advice(
                *is_paddings.last().unwrap(),
                Rotation(-((NUM_END_ROWS + NUM_ROUNDS - NUM_WORDS_TO_ABSORB) as i32) - 2),
            );
            let is_final_prev = meta.query_advice(is_final, Rotation::prev());
            let is_final = meta.query_advice(is_final, Rotation::cur());
            // On the first row is_final needs to be enabled
            cb.condition(meta.query_fixed(q_first, Rotation::cur()), |cb| {
                cb.require_equal(
                    "is_final needs to remain the same",
                    is_final.expr(),
                    1.expr(),
                );
            });
            // Get the correct is_final state from the padding selector
            cb.condition(meta.query_fixed(q_squeeze, Rotation::cur()), |cb| {
                cb.require_equal(
                    "is_final needs to match the padding selector",
                    is_final.expr(),
                    is_padding,
                );
            });
            // Copy the is_final state to the q_start rows
            cb.condition(
                meta.query_fixed(q_start, Rotation::cur())
                    - meta.query_fixed(q_first, Rotation::cur()),
                |cb| {
                    cb.require_equal(
                        "is_final needs to remain the same",
                        is_final.expr(),
                        is_final_prev,
                    );
                },
            );
            cb.gate(1.expr())
        });

        meta.create_gate("is enabled", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
            let q_squeeze = meta.query_fixed(q_squeeze, Rotation::cur());
            let is_final = meta.query_advice(is_final, Rotation::cur());
            let is_enabled = meta.query_advice(is_enabled, Rotation::cur());
            // Only set is_enabled to true when is_final is true and it's a squeeze row
            cb.require_equal(
                "is_enabled := q_squeeze && is_final",
                is_enabled.expr(),
                and::expr(&[q_squeeze.expr(), is_final.expr()]),
            );
            cb.gate(meta.query_fixed(q_enable, Rotation::cur()))
        });

        let start_new_hash = |meta: &mut VirtualCells<F>| {
            // A new hash is started when the previous hash is done or on the first row
            meta.query_advice(is_final, Rotation::cur())
        };

        // Create bytes from input bits
        let input_bytes = to_le_bytes::expr(w);

        // Padding
        meta.create_gate("padding", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
            let prev_is_padding = meta.query_advice(*is_paddings.last().unwrap(), Rotation::prev());
            let q_padding = meta.query_fixed(q_padding, Rotation::cur());
            let q_padding_last = meta.query_fixed(q_padding_last, Rotation::cur());
            let length = meta.query_advice(length, Rotation::cur());
            let is_final_padding_row =
                meta.query_advice(*is_paddings.last().unwrap(), Rotation(-2));
            // All padding selectors need to be boolean
            for is_padding in is_paddings.iter() {
                let is_padding = meta.query_advice(*is_padding, Rotation::cur());
                cb.condition(meta.query_fixed(q_enable, Rotation::cur()), |cb| {
                    cb.require_boolean("is_padding boolean", is_padding);
                });
            }
            // Now for each padding selector
            for idx in 0..is_paddings.len() {
                // Previous padding selector can be on the previous row
                let is_padding_prev = if idx == 0 {
                    prev_is_padding.expr()
                } else {
                    meta.query_advice(is_paddings[idx - 1], Rotation::cur())
                };
                let is_padding = meta.query_advice(is_paddings[idx], Rotation::cur());
                let is_first_padding = is_padding.clone() - is_padding_prev.clone();
                // Check padding transition 0 -> 1 done only once
                cb.condition(q_padding.expr(), |cb| {
                    cb.require_boolean("padding step boolean", is_first_padding.clone());
                });
                // Padding start/intermediate byte, all padding rows except the last one
                cb.condition(
                    and::expr([
                        (q_padding.expr() - q_padding_last.expr()),
                        is_padding.expr(),
                    ]),
                    |cb| {
                        // Input bytes need to be zero, or 128 if this is the first padding byte
                        cb.require_equal(
                            "padding start/intermediate byte",
                            input_bytes[idx].clone(),
                            is_first_padding.expr() * 128.expr(),
                        );
                    },
                );
                // Padding start/intermediate byte, last padding row but not in the final block
                cb.condition(
                    and::expr([
                        q_padding_last.expr(),
                        is_padding.expr(),
                        not::expr(is_final_padding_row.expr()),
                    ]),
                    |cb| {
                        // Input bytes need to be zero, or 128 if this is the first padding byte
                        cb.require_equal(
                            "padding start/intermediate byte",
                            input_bytes[idx].clone(),
                            is_first_padding.expr() * 128.expr(),
                        );
                    },
                );
            }
            // The last row containing input/padding data in the final block needs to
            // contain the length in bits (Only input lengths up to 2**32 - 1
            // bits are supported, which is lower than the spec of 2**64 - 1 bits)
            cb.condition(
                and::expr([q_padding_last.expr(), is_final_padding_row.expr()]),
                |cb| {
                    cb.require_equal("padding length", decode::expr(w), length.expr() * 8.expr());
                },
            );
            cb.gate(1.expr())
        });

        // Length and input data rlc
        meta.create_gate("length and data rlc", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
            let q_padding = meta.query_fixed(q_padding, Rotation::cur());
            let start_new_hash = start_new_hash(meta);
            let length_prev = meta.query_advice(length, Rotation::prev());
            let length = meta.query_advice(length, Rotation::cur());
            let data_rlc_prev = meta.query_advice(data_rlc, Rotation::prev());
            let data_rlc = meta.query_advice(data_rlc, Rotation::cur());
            // Update the length/data_rlc on rows where we absorb data
            cb.condition(q_padding.expr(), |cb| {
                // Length increases by the number of bytes that aren't padding
                // In a new block we have to start from 0 if the previous block was the final
                // one
                cb.require_equal(
                    "update length",
                    length.clone(),
                    length_prev.clone() * not::expr(start_new_hash.expr())
                        + sum::expr(is_paddings.iter().map(|is_padding| {
                            not::expr(meta.query_advice(*is_padding, Rotation::cur()))
                        })),
                );

                // Use intermediate cells to keep the degree low
                let mut new_data_rlc = data_rlc_prev.clone() * not::expr(start_new_hash.expr());
                cb.require_equal(
                    "initial data rlc",
                    meta.query_advice(data_rlcs[0], Rotation::cur()),
                    new_data_rlc,
                );
                new_data_rlc = meta.query_advice(data_rlcs[0], Rotation::cur());
                for (idx, (byte, is_padding)) in
                    input_bytes.iter().zip(is_paddings.iter()).enumerate()
                {
                    new_data_rlc = select::expr(
                        meta.query_advice(*is_padding, Rotation::cur()),
                        new_data_rlc.clone(),
                        new_data_rlc.clone() * r + byte.clone(),
                    );
                    if idx < data_rlcs.len() - 1 {
                        let next_data_rlc = meta.query_advice(data_rlcs[idx + 1], Rotation::cur());
                        cb.require_equal(
                            "intermediate data rlc",
                            next_data_rlc.clone(),
                            new_data_rlc,
                        );
                        new_data_rlc = next_data_rlc;
                    }
                }
                cb.require_equal("update data rlc", data_rlc.clone(), new_data_rlc);
            });
            cb.gate(1.expr())
        });

        // Make sure data is consistent between blocks
        meta.create_gate("cross block data consistency", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
            let start_new_hash = start_new_hash(meta);
            let to_const =
                |value: &String| -> &'static str { Box::leak(value.clone().into_boxed_str()) };
            let mut add = |name: &'static str, column: Column<Advice>| {
                let last_rot =
                    Rotation(-((NUM_END_ROWS + NUM_ROUNDS - NUM_WORDS_TO_ABSORB) as i32));
                let value_to_copy = meta.query_advice(column, last_rot);
                let prev_value = meta.query_advice(column, Rotation::prev());
                let cur_value = meta.query_advice(column, Rotation::cur());
                // On squeeze rows fetch the last used value
                cb.condition(meta.query_fixed(q_squeeze, Rotation::cur()), |cb| {
                    cb.require_equal(
                        to_const(&format!("{} copy check", name)),
                        cur_value.expr(),
                        value_to_copy.expr(),
                    );
                });
                // On first rows keep the length the same, or reset the length when starting a
                // new hash
                cb.condition(
                    meta.query_fixed(q_start, Rotation::cur())
                        - meta.query_fixed(q_first, Rotation::cur()),
                    |cb| {
                        cb.require_equal(
                            to_const(&format!("{} equality check", name)),
                            cur_value.expr(),
                            prev_value.expr() * not::expr(start_new_hash.expr()),
                        );
                    },
                );
                // Set the value to zero on the first row
                cb.condition(meta.query_fixed(q_first, Rotation::cur()), |cb| {
                    cb.require_equal(
                        to_const(&format!("{} initialized to 0", name)),
                        cur_value.clone(),
                        0.expr(),
                    );
                });
            };
            add("length", length);
            add("data_rlc", data_rlc);
            add("last padding", *is_paddings.last().unwrap());
            cb.gate(1.expr())
        });

        // Squeeze
        meta.create_gate("squeeze", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
            // Squeeze out the hash
            let hash_parts = [new_a, &a, &b, &c, new_e, &e, &f, &g];
            let hash_bytes = hash_parts
                .iter()
                .flat_map(|part| to_le_bytes::expr(part))
                .collect::<Vec<_>>();
            let rlc = compose_rlc::expr(&hash_bytes, r);
            cb.condition(start_new_hash(meta), |cb| {
                cb.require_equal(
                    "hash rlc check",
                    rlc,
                    meta.query_advice(hash_rlc, Rotation::cur()),
                );
            });
            cb.gate(meta.query_fixed(q_squeeze, Rotation::cur()))
        });

        info!("degree: {}", meta.degree());

        Sha256BitConfig {
            q_enable,
            q_first,
            q_extend,
            q_start,
            q_compression,
            q_end,
            q_padding,
            q_padding_last,
            q_squeeze,
            hash_table,
            word_w,
            word_a,
            word_e,
            is_final,
            is_paddings,
            data_rlcs,
            round_cst,
            h_a,
            h_e,
            _marker: PhantomData,
        }
    }

    fn assign(
        &self,
        mut layouter: impl Layouter<F>,
        _size: usize,
        witness: &[ShaRow<F>],
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "assign sha256 data",
            |mut region| {
                for (offset, sha256_row) in witness.iter().enumerate() {
                    self.set_row(&mut region, offset, sha256_row)?;
                }
                Ok(())
            },
        )
    }

    fn set_row(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        row: &ShaRow<F>,
    ) -> Result<(), Error> {
        let round = offset % (NUM_ROUNDS + 8);

        // Fixed values
        for (name, column, value) in &[
            ("q_enable", self.q_enable, F::from(true)),
            ("q_first", self.q_first, F::from(offset == 0)),
            (
                "q_extend",
                self.q_extend,
                F::from((4 + 16..4 + NUM_ROUNDS).contains(&round)),
            ),
            ("q_start", self.q_start, F::from(round < 4)),
            (
                "q_compression",
                self.q_compression,
                F::from((4..NUM_ROUNDS + 4).contains(&round)),
            ),
            ("q_end", self.q_end, F::from(round >= NUM_ROUNDS + 4)),
            (
                "q_padding",
                self.q_padding,
                F::from((4..20).contains(&round)),
            ),
            ("q_padding_last", self.q_padding_last, F::from(round == 19)),
            (
                "q_squeeze",
                self.q_squeeze,
                F::from(round == NUM_ROUNDS + 7),
            ),
            (
                "round_cst",
                self.round_cst,
                F::from(if (4..NUM_ROUNDS + 4).contains(&round) {
                    ROUND_CST[round - 4] as u64
                } else {
                    0
                }),
            ),
            (
                "Ha",
                self.h_a,
                F::from(if round < 4 { H[3 - round] as u64 } else { 0 }),
            ),
            (
                "He",
                self.h_e,
                F::from(if round < 4 { H[7 - round] as u64 } else { 0 }),
            ),
        ] {
            region.assign_fixed(
                || format!("assign {} {}", name, offset),
                *column,
                offset,
                || Value::known(*value),
            )?;
        }

        // Advice values
        for (name, columns, values) in [
            ("w bits", self.word_w.as_slice(), row.w.as_slice()),
            ("a bits", self.word_a.as_slice(), row.a.as_slice()),
            ("e bits", self.word_e.as_slice(), row.e.as_slice()),
            (
                "padding selectors",
                self.is_paddings.as_slice(),
                row.is_paddings.as_slice(),
            ),
            (
                "is_final",
                [self.is_final].as_slice(),
                [row.is_final].as_slice(),
            ),
        ] {
            for (idx, (value, column)) in values.iter().zip(columns.iter()).enumerate() {
                region.assign_advice(
                    || format!("assign {} {} {}", name, idx, offset),
                    *column,
                    offset,
                    || Value::known(F::from(*value)),
                )?;
            }
        }

        // Data rlcs
        for (idx, (data_rlc, column)) in row.data_rlcs.iter().zip(self.data_rlcs.iter()).enumerate()
        {
            region.assign_advice(
                || format!("assign data rlcs {} {}", idx, offset),
                *column,
                offset,
                || Value::known(*data_rlc),
            )?;
        }

        // Hash data
        self.hash_table.assign_row(
            region,
            offset,
            [
                F::from(row.is_final && round == NUM_ROUNDS + 7),
                row.data_rlc,
                F::from(row.length as u64),
                row.hash_rlc,
            ],
        )?;

        Ok(())
    }
}

fn sha256<F: Field>(rows: &mut Vec<ShaRow<F>>, bytes: &[u8], r: F) {
    let mut bits = into_bits(bytes);

    // Padding
    let length = bits.len();
    let mut length_in_bits = into_bits(&(length as u64).to_be_bytes());
    assert!(length_in_bits.len() == NUM_BITS_PADDING_LENGTH);
    bits.push(1);
    while (bits.len() + NUM_BITS_PADDING_LENGTH) % RATE_IN_BITS != 0 {
        bits.push(0);
    }
    bits.append(&mut length_in_bits);
    assert!(bits.len() % RATE_IN_BITS == 0);

    // Set the initial state
    let mut hs: [u64; 8] = H
        .iter()
        .map(|v| *v as u64)
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();
    let mut length = 0usize;
    let mut data_rlc = F::zero();
    let mut in_padding = false;

    // Process each block
    let chunks = bits.chunks(RATE_IN_BITS);
    let num_chunks = chunks.len();
    for (idx, chunk) in chunks.enumerate() {
        // Adds a row
        let mut add_row = |w: u64,
                           a: u64,
                           e: u64,
                           is_final,
                           length,
                           data_rlc,
                           hash_rlc,
                           is_paddings,
                           data_rlcs| {
            let word_to_bits = |value: u64, num_bits: usize| {
                into_bits(&value.to_be_bytes())[64 - num_bits..64]
                    .iter()
                    .map(|b| *b != 0)
                    .into_iter()
                    .collect::<Vec<_>>()
            };
            rows.push(ShaRow {
                w: word_to_bits(w, NUM_BITS_PER_WORD_W).try_into().unwrap(),
                a: word_to_bits(a, NUM_BITS_PER_WORD_EXT).try_into().unwrap(),
                e: word_to_bits(e, NUM_BITS_PER_WORD_EXT).try_into().unwrap(),
                is_final,
                length,
                data_rlc,
                hash_rlc,
                is_paddings,
                data_rlcs,
            });
        };

        // Last block for this hash
        let is_final_block = idx == num_chunks - 1;

        // Set the state
        let (mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h) =
            (hs[0], hs[1], hs[2], hs[3], hs[4], hs[5], hs[6], hs[7]);

        // Add start rows
        let mut add_row_start = |a: u64, e: u64, is_final| {
            add_row(
                0,
                a,
                e,
                is_final,
                length,
                data_rlc,
                F::zero(),
                [false, false, false, in_padding],
                [F::zero(); ABSORB_WIDTH_PER_ROW_BYTES],
            )
        };
        add_row_start(d, h, idx == 0);
        add_row_start(c, g, idx == 0);
        add_row_start(b, f, idx == 0);
        add_row_start(a, e, idx == 0);

        let mut ws = Vec::new();
        for (round, round_cst) in ROUND_CST.iter().enumerate() {
            // Padding/Length/Data rlc
            let mut is_paddings = [false; ABSORB_WIDTH_PER_ROW_BYTES];
            let mut data_rlcs = [F::zero(); ABSORB_WIDTH_PER_ROW_BYTES];
            if round < NUM_WORDS_TO_ABSORB {
                // padding/length
                for is_padding in is_paddings.iter_mut() {
                    *is_padding = if length == bytes.len() {
                        true
                    } else {
                        length += 1;
                        false
                    };
                }
                // data rlc
                let input_bytes = to_le_bytes::value(&chunk[round * 32..(round + 1) * 32]);
                data_rlcs[0] = data_rlc;
                for (idx, (byte, padding)) in input_bytes.iter().zip(is_paddings.iter()).enumerate()
                {
                    if !*padding {
                        data_rlc = data_rlc * r + F::from(*byte as u64);
                    }
                    if idx < data_rlcs.len() - 1 {
                        data_rlcs[idx + 1] = data_rlc;
                    }
                }
                in_padding = *is_paddings.last().unwrap();
            }

            // w
            let w_ext = if round < NUM_WORDS_TO_ABSORB {
                decode::value(&chunk[round * 32..(round + 1) * 32])
            } else {
                let get_w = |offset: usize| ws[ws.len() - offset] & 0xFFFFFFFF;
                let s0 = rotate::value(get_w(15), 7)
                    ^ rotate::value(get_w(15), 18)
                    ^ shift::value(get_w(15), 3);
                let s1 = rotate::value(get_w(2), 17)
                    ^ rotate::value(get_w(2), 19)
                    ^ shift::value(get_w(2), 10);
                get_w(16) + s0 + get_w(7) + s1
            };
            let w = w_ext & 0xFFFFFFFF;
            ws.push(w);

            // compression
            let s1 = rotate::value(e, 6) ^ rotate::value(e, 11) ^ rotate::value(e, 25);
            let ch = (e & f) ^ (!e & g);
            let temp1 = h + s1 + ch + (*round_cst as u64) + w;
            let s0 = rotate::value(a, 2) ^ rotate::value(a, 13) ^ rotate::value(a, 22);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let temp2 = s0 + maj;

            h = g;
            g = f;
            f = e;
            e = d + temp1;
            d = c;
            c = b;
            b = a;
            a = temp1 + temp2;

            // Add the row
            add_row(
                w_ext,
                a,
                e,
                false,
                if round < NUM_WORDS_TO_ABSORB {
                    length
                } else {
                    0
                },
                if round < NUM_WORDS_TO_ABSORB {
                    data_rlc
                } else {
                    F::zero()
                },
                F::zero(),
                is_paddings,
                data_rlcs,
            );

            // Truncate the newly calculated values
            a &= 0xFFFFFFFF;
            e &= 0xFFFFFFFF;
        }

        // Accumulate
        hs[0] += a;
        hs[1] += b;
        hs[2] += c;
        hs[3] += d;
        hs[4] += e;
        hs[5] += f;
        hs[6] += g;
        hs[7] += h;

        // Squeeze
        let hash_rlc = if is_final_block {
            let hash_bytes = hs
                .iter()
                .flat_map(|h| (*h as u32).to_be_bytes())
                .collect::<Vec<_>>();
            rlc::value(&hash_bytes, r)
        } else {
            F::zero()
        };

        // Add end rows
        let mut add_row_end = |a: u64, e: u64| {
            add_row(
                0,
                a,
                e,
                false,
                0,
                F::zero(),
                F::zero(),
                [false; ABSORB_WIDTH_PER_ROW_BYTES],
                [F::zero(); ABSORB_WIDTH_PER_ROW_BYTES],
            )
        };
        add_row_end(hs[3], hs[7]);
        add_row_end(hs[2], hs[6]);
        add_row_end(hs[1], hs[5]);
        add_row(
            0,
            hs[0],
            hs[4],
            is_final_block,
            length,
            data_rlc,
            hash_rlc,
            [false, false, false, in_padding],
            [F::zero(); ABSORB_WIDTH_PER_ROW_BYTES],
        );

        // Now truncate the results
        for h in hs.iter_mut() {
            *h &= 0xFFFFFFFF;
        }
    }

    let hash_bytes = hs
        .iter()
        .flat_map(|h| (*h as u32).to_be_bytes())
        .collect::<Vec<_>>();
    debug!("hash: {:x?}", &hash_bytes);
    debug!("data rlc: {:x?}", data_rlc);
}

fn multi_sha256<F: Field>(bytes: &[Vec<u8>], r: F) -> Vec<ShaRow<F>> {
    let mut rows: Vec<ShaRow<F>> = Vec::new();
    for bytes in bytes {
        sha256(&mut rows, bytes, r);
    }
    rows
}

#[cfg(test)]
mod tests {
    use super::*;
    use halo2_proofs::{dev::MockProver, halo2curves::bn256::Fr};

    fn verify<F: Field>(k: u32, inputs: Vec<Vec<u8>>, success: bool) {
        let mut circuit = Sha256BitCircuit::new(2usize.pow(k));
        circuit.generate_witness(&inputs);

        let prover = MockProver::<F>::run(k, &circuit, vec![]).unwrap();
        let verify_result = prover.verify();
        if verify_result.is_ok() != success {
            if let Some(errors) = verify_result.err() {
                for error in errors.iter() {
                    println!("{}", error);
                }
            }
            panic!();
        }
    }

    #[test]
    fn bit_sha256_simple() {
        let k = 10;
        let inputs = vec![
            vec![],
            (0u8..1).collect::<Vec<_>>(),
            (0u8..54).collect::<Vec<_>>(),
            (0u8..55).collect::<Vec<_>>(),
            (0u8..56).collect::<Vec<_>>(),
            (0u8..200).collect::<Vec<_>>(),
        ];
        verify::<Fr>(k, inputs, true);
    }
}
