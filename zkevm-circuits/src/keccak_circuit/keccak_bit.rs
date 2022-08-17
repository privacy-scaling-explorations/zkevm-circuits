use crate::{
    evm_circuit::util::{constraint_builder::BaseConstraintBuilder, not, rlc},
    util::Expr,
};
use eth_types::{Field, ToScalar, Word};
use gadgets::util::{and, select, sum, xor};
use halo2_proofs::{
    circuit::{Layouter, Region, SimpleFloorPlanner},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, TableColumn},
    poly::Rotation,
};
use itertools::Itertools;
use std::{env::var, marker::PhantomData, vec};

const MAX_DEGREE: usize = 5;

const NUM_BITS_PER_BYTE: usize = 8;
const NUM_BYTES_PER_WORD: usize = 8;
const NUM_BITS_PER_WORD: usize = NUM_BYTES_PER_WORD * NUM_BITS_PER_BYTE;
const KECCAK_WIDTH: usize = 5 * 5;
const KECCAK_WIDTH_IN_BITS: usize = KECCAK_WIDTH * NUM_BITS_PER_WORD;
const NUM_ROUNDS: usize = 24;
const NUM_WORDS_TO_ABSORB: usize = 17;
const NUM_WORDS_TO_SQUEEZE: usize = 4;
const ABSORB_WIDTH_PER_ROW: usize = NUM_BITS_PER_WORD;
const ABSORB_WIDTH_PER_ROW_BYTES: usize = ABSORB_WIDTH_PER_ROW / NUM_BITS_PER_BYTE;
const RATE: usize = NUM_WORDS_TO_ABSORB * NUM_BYTES_PER_WORD;
const RATE_IN_BITS: usize = RATE * NUM_BITS_PER_BYTE;
const C_WIDTH: usize = 5 * NUM_BITS_PER_WORD;
const RHOM: [[usize; 5]; 5] = [
    [0, 36, 3, 41, 18],
    [1, 44, 10, 45, 2],
    [62, 6, 43, 15, 61],
    [28, 55, 25, 21, 56],
    [27, 20, 39, 8, 14],
];
const IOTA_ROUND_CST: [u64; NUM_ROUNDS + 1] = [
    0x0000000000000001,
    0x0000000000008082,
    0x800000000000808a,
    0x8000000080008000,
    0x000000000000808b,
    0x0000000080000001,
    0x8000000080008081,
    0x8000000000008009,
    0x000000000000008a,
    0x0000000000000088,
    0x0000000080008009,
    0x000000008000000a,
    0x000000008000808b,
    0x800000000000008b,
    0x8000000000008089,
    0x8000000000008003,
    0x8000000000008002,
    0x8000000000000080,
    0x000000000000800a,
    0x800000008000000a,
    0x8000000080008081,
    0x8000000000008080,
    0x0000000080000001,
    0x8000000080008008,
    0x0000000000000000, // absorb round
];
// Bit positions that have a non-zero value in `IOTA_ROUND_CST`.
const ROUND_CST_BIT_POS: [usize; 7] = [0, 1, 3, 7, 15, 31, 63];
const MAX_INPUT_THETA_LOOKUP: u64 = 5;

fn get_degree() -> usize {
    var("DEGREE")
        .unwrap_or_else(|_| "8".to_string())
        .parse()
        .expect("Cannot parse DEGREE env var as usize")
}

fn get_num_bits_per_theta_lookup() -> usize {
    let degree = get_degree() as u32;
    let mut num_bits = 1;
    while (MAX_INPUT_THETA_LOOKUP + 1).pow(num_bits + 1) <= 2u64.pow(degree) {
        num_bits += 1;
    }
    num_bits as usize
}

#[derive(Clone, Debug, PartialEq)]
struct KeccakRow<F> {
    q_padding: bool,
    q_padding_last: bool,
    state: [u8; KECCAK_WIDTH_IN_BITS],
    theta_c: [u8; C_WIDTH],
    input: [u8; ABSORB_WIDTH_PER_ROW],
    is_paddings: [bool; ABSORB_WIDTH_PER_ROW_BYTES],
    data_rlcs: [F; ABSORB_WIDTH_PER_ROW_BYTES],
    is_final: u64,
    length: usize,
    data_rlc: F,
    hash_rlc: F,
}

/// KeccakBitConfig
#[derive(Clone, Debug)]
pub struct KeccakBitConfig<F> {
    q_enable: Column<Fixed>,
    q_first: Column<Fixed>,
    q_round: Column<Fixed>,
    q_absorb: Column<Fixed>,
    q_padding: Column<Fixed>,
    q_padding_last: Column<Fixed>,
    is_final: Column<Advice>,
    length: Column<Advice>,
    data_rlc: Column<Advice>,
    hash_rlc: Column<Advice>,
    state: [Column<Advice>; KECCAK_WIDTH_IN_BITS],
    theta_c: [Column<Advice>; C_WIDTH],
    input: [Column<Advice>; ABSORB_WIDTH_PER_ROW],
    is_paddings: [Column<Advice>; ABSORB_WIDTH_PER_ROW_BYTES],
    data_rlcs: [Column<Advice>; ABSORB_WIDTH_PER_ROW_BYTES],
    round_cst: [Column<Fixed>; ROUND_CST_BIT_POS.len()],
    theta_c_table: Vec<TableColumn>,
    _marker: PhantomData<F>,
}

/// KeccakBitCircuit
#[derive(Default)]
pub struct KeccakBitCircuit<F: Field> {
    inputs: Vec<KeccakRow<F>>,
    size: usize,
    _marker: PhantomData<F>,
}

impl<F: Field> KeccakBitCircuit<F> {
    fn r() -> F {
        F::from(123456)
    }
}

impl<F: Field> Circuit<F> for KeccakBitCircuit<F> {
    type Config = KeccakBitConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        KeccakBitConfig::configure(meta, KeccakBitCircuit::r())
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        config.load(&mut layouter)?;
        config.assign(layouter, self.size, &self.inputs)?;
        Ok(())
    }
}

impl<F: Field> KeccakBitConfig<F> {
    pub(crate) fn configure(meta: &mut ConstraintSystem<F>, r: F) -> Self {
        let num_bits_per_theta_lookup = get_num_bits_per_theta_lookup();
        println!("num_bits_per_theta_lookup: {}", num_bits_per_theta_lookup);

        let q_enable = meta.fixed_column();
        let q_first = meta.fixed_column();
        let q_round = meta.fixed_column();
        let q_absorb = meta.fixed_column();
        let q_padding = meta.fixed_column();
        let q_padding_last = meta.fixed_column();
        let is_final = meta.advice_column();
        let length = meta.advice_column();
        let data_rlc = meta.advice_column();
        let hash_rlc = meta.advice_column();
        let state = array_init::array_init(|_| meta.advice_column());
        let theta_c = array_init::array_init(|_| meta.advice_column());
        let input = array_init::array_init(|_| meta.advice_column());
        let is_paddings = array_init::array_init(|_| meta.advice_column());
        let data_rlcs = array_init::array_init(|_| meta.advice_column());
        let round_cst = array_init::array_init(|_| meta.fixed_column());

        let mut theta_c_table = Vec::new();
        for _ in 0..1 + num_bits_per_theta_lookup {
            theta_c_table.push(meta.lookup_table_column());
        }

        // State bits
        let mut s = vec![vec![vec![0u64.expr(); 64]; 5]; 5];
        let mut s_next = vec![vec![vec![0u64.expr(); 64]; 5]; 5];
        meta.create_gate("Query state bits", |meta| {
            let mut counter = 0;
            for i in 0..5 {
                for j in 0..5 {
                    for k in 0..64 {
                        s[i][j][k] = meta.query_advice(state[counter], Rotation::cur());
                        s_next[i][j][k] = meta.query_advice(state[counter], Rotation::next());
                        counter += 1;
                    }
                }
            }
            vec![0u64.expr()]
        });
        // Theta c bits
        let mut c = vec![vec![0u64.expr(); 64]; 5];
        meta.create_gate("Query Theta c bits", |meta| {
            let mut counter = 0;
            for c in c.iter_mut() {
                for c in c.iter_mut() {
                    *c = meta.query_advice(theta_c[counter], Rotation::cur());
                    counter += 1;
                }
            }
            vec![0u64.expr()]
        });
        // Input bits
        let mut i = vec![0u64.expr(); 64];
        let mut i_next = vec![vec![0u64.expr(); 64]; 17];
        meta.create_gate("Query absorb inputs", |meta| {
            for k in 0..64 {
                i[k] = meta.query_advice(input[k], Rotation::cur());
            }
            for (i, i_next) in i_next.iter_mut().enumerate() {
                for (k, i_next) in i_next.iter_mut().enumerate() {
                    *i_next = meta.query_advice(input[k], Rotation((i + 1) as i32));
                }
            }
            vec![0u64.expr()]
        });

        // Theta lookups
        let mut theta = Vec::new();
        for (i, c) in c.iter().enumerate() {
            let pi = (5 + i - 1) % 5;
            let ni = (i + 1) % 5;
            for (k, c) in c.iter().enumerate() {
                let pk = (64 + k - 1) % 64;
                let bit = xor::expr(s[pi][0][k].clone(), s[pi][1][k].clone())
                    + xor::expr(s[pi][2][k].clone(), s[pi][3][k].clone())
                    + xor::expr(s[pi][4][k].clone(), s[ni][0][pk].clone())
                    + xor::expr(s[ni][1][pk].clone(), s[ni][2][pk].clone())
                    + xor::expr(s[ni][3][pk].clone(), s[ni][4][pk].clone());
                theta.push((c.clone(), bit));
            }
        }
        let mut lookup_counter = 0;
        for chunk in theta.chunks(num_bits_per_theta_lookup) {
            meta.lookup("Theta c", |_| {
                let mut factor = 1u64;
                let mut input = 0u64.expr();
                let mut tables = Vec::new();
                for (idx, (bit, expr)) in chunk.iter().enumerate() {
                    input = input + expr.clone() * factor.expr();
                    factor *= MAX_INPUT_THETA_LOOKUP;
                    tables.push((bit.clone(), theta_c_table[1 + idx]));
                }
                tables.push((input, theta_c_table[0]));
                tables
            });
            lookup_counter += 1;
        }
        println!("Lookups: {}", lookup_counter);

        meta.create_gate("input checks", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
            // Input bits boolean
            for i in &i {
                cb.require_boolean("boolean state bit", i.clone());
            }
            // is_final boolean
            cb.require_boolean(
                "boolean is_final",
                meta.query_advice(is_final, Rotation::cur()),
            );
            cb.gate(meta.query_fixed(q_enable, Rotation::cur()))
        });

        meta.create_gate("first row", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
            // is_final needs to be true
            cb.require_equal(
                "is_final needs to be enabled on the first row",
                meta.query_advice(is_final, Rotation::cur()),
                1.expr(),
            );
            cb.gate(meta.query_fixed(q_first, Rotation::cur()))
        });

        meta.create_gate("round", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
            let mut s = s.clone();

            // Theta
            let mut os = vec![vec![vec![0u64.expr(); 64]; 5]; 5];
            for i in 0..5 {
                for j in 0..5 {
                    for k in 0..64 {
                        os[i][j][k] = xor::expr(s[i][j][k].clone(), c[i][k].clone());
                    }
                }
            }
            s = os.clone();

            // Rho/Pi
            for (i, b) in s.iter().enumerate() {
                for (j, b) in b.iter().enumerate() {
                    for k in 0..64 {
                        os[j][(2 * i + 3 * j) % 5][k] = b[(64 + k - RHOM[i][j]) % 64].clone();
                    }
                }
            }
            s = os.clone();

            // Chi/Iota
            let mut iota_counter = 0;
            for i in 0..5 {
                for j in 0..5 {
                    for k in 0..64 {
                        if i == 0 && j == 0 && ROUND_CST_BIT_POS.contains(&k) {
                            cb.require_equal(
                                "round state transition with round constant",
                                not::expr(s[(i + 1) % 5][j][k].clone())
                                    * s[(i + 2) % 5][j][k].clone(),
                                xor::expr(
                                    xor::expr(s[i][j][k].clone(), s_next[i][j][k].clone()),
                                    meta.query_fixed(round_cst[iota_counter], Rotation::cur()),
                                ),
                            );
                            iota_counter += 1;
                        } else {
                            cb.require_equal(
                                "round state transition",
                                not::expr(s[(i + 1) % 5][j][k].clone())
                                    * s[(i + 2) % 5][j][k].clone(),
                                xor::expr(s[i][j][k].clone(), s_next[i][j][k].clone()),
                            );
                        }
                    }
                }
            }

            cb.gate(meta.query_fixed(q_round, Rotation::cur()))
        });

        meta.create_gate("absorb", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
            let is_not_final = not::expr(meta.query_advice(is_final, Rotation::cur()));
            let absorb_positions = get_absorb_positions();
            let mut input_slice = 0;
            for j in 0..5 {
                for i in 0..5 {
                    if absorb_positions.contains(&(i, j)) {
                        for k in 0..64 {
                            cb.require_equal(
                                "absorb bit",
                                xor::expr(
                                    s[i][j][k].clone() * is_not_final.clone(),
                                    i_next[input_slice][k].clone(),
                                ),
                                s_next[i][j][k].clone(),
                            );
                        }
                        input_slice += 1;
                    } else {
                        for k in 0..64 {
                            cb.require_equal(
                                "absorb copy",
                                s[i][j][k].clone() * is_not_final.clone(),
                                s_next[i][j][k].clone(),
                            );
                        }
                    }
                }
            }
            cb.gate(meta.query_fixed(q_absorb, Rotation::cur()))
        });

        meta.create_gate("squeeze", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
            // Squeeze out the hash
            let hash_bytes = s
                .into_iter()
                .take(4)
                .map(|a| to_bytes_expr(&a[0]))
                .take(4)
                .concat();
            let rlc = compose_rlc(&hash_bytes, r);
            cb.condition(meta.query_advice(is_final, Rotation::cur()), |cb| {
                cb.require_equal(
                    "hash rlc check",
                    rlc,
                    meta.query_advice(hash_rlc, Rotation::cur()),
                );
            });
            cb.gate(meta.query_fixed(q_enable, Rotation::cur()))
        });

        meta.create_gate("is final", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
            let last_is_padding_in_block = meta.query_advice(
                *is_paddings.last().unwrap(),
                Rotation(-((NUM_ROUNDS + 1 - NUM_WORDS_TO_ABSORB) as i32)),
            );
            cb.require_equal(
                "is_final needs to be the same as the last is_padding in the block",
                meta.query_advice(is_final, Rotation::cur()),
                last_is_padding_in_block.expr(),
            );
            // All absorb rows except the first row
            cb.gate(
                meta.query_fixed(q_absorb, Rotation::cur())
                    - meta.query_fixed(q_first, Rotation::cur()),
            )
        });

        // Create bytes from input bits
        let mut input_bytes = Vec::new();
        meta.create_gate("create input bytes", |meta| {
            let input_bits = input
                .iter()
                .map(|c| meta.query_advice(*c, Rotation::cur()))
                .collect::<Vec<_>>();
            input_bytes = to_bytes_expr(&input_bits);
            vec![0u64.expr()]
        });

        // May be cleaner to do this padding logic in the byte conversion lookup but
        // currently easier to do it like this.
        meta.create_gate("padding", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
            let prev_is_padding = meta.query_advice(*is_paddings.last().unwrap(), Rotation::prev());
            let q_padding = meta.query_fixed(q_padding, Rotation::cur());
            let q_padding_last = meta.query_fixed(q_padding_last, Rotation::cur());

            // All padding selectors need to be boolean
            for is_padding in is_paddings.iter() {
                let is_padding = meta.query_advice(*is_padding, Rotation::cur());
                cb.condition(meta.query_fixed(q_enable, Rotation::cur()), |cb| {
                    cb.require_boolean("is_padding boolean", is_padding);
                });
            }

            // This last padding selector will be used on the first round row so needs to be
            // zero
            cb.condition(meta.query_fixed(q_absorb, Rotation::cur()), |cb| {
                cb.require_zero(
                    "last is_padding should be zero on absorb rows",
                    meta.query_advice(*is_paddings.last().unwrap(), Rotation::cur()),
                );
            });

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

                // Padding start/intermediate/end byte checks
                if idx == is_paddings.len() - 1 {
                    // These can be combined in the future, but currently this would increase the
                    // degree by one Padding start/intermediate byte, all
                    // padding rows except the last one
                    cb.condition(
                        and::expr([
                            (q_padding.expr() - q_padding_last.expr()),
                            is_padding.expr(),
                        ]),
                        |cb| {
                            // Input bytes need to be zero, or one if this is the first padding byte
                            cb.require_equal(
                                "padding start/intermediate byte last byte",
                                input_bytes[idx].clone(),
                                is_first_padding.expr(),
                            );
                        },
                    );
                    // Padding start/end byte, only on the last padding row
                    cb.condition(
                        and::expr([q_padding_last.expr(), is_padding.expr()]),
                        |cb| {
                            // The input byte needs to be 128, unless it's also the first padding
                            // byte and then it's 129
                            cb.require_equal(
                                "padding start/end byte",
                                input_bytes[idx].clone(),
                                is_first_padding.expr() + 128.expr(),
                            );
                        },
                    );
                } else {
                    // Padding start/intermediate byte
                    cb.condition(and::expr([q_padding.expr(), is_padding.expr()]), |cb| {
                        // Input bytes need to be zero, or one if this is the first padding byte
                        cb.require_equal(
                            "padding start/intermediate byte",
                            input_bytes[idx].clone(),
                            is_first_padding.expr(),
                        );
                    });
                }
            }

            cb.gate(1.expr())
        });

        meta.create_gate("length and data rlc", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);

            let q_padding = meta.query_fixed(q_padding, Rotation::cur());
            let is_final_prev = meta.query_advice(is_final, Rotation::prev());
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
                    length_prev.clone() * not::expr(is_final_prev.expr())
                        + sum::expr(is_paddings.iter().map(|is_padding| {
                            not::expr(meta.query_advice(*is_padding, Rotation::cur()))
                        })),
                );

                // Use intermediate cells to keep the degree low
                let mut new_data_rlc = data_rlc_prev.clone() * not::expr(is_final_prev.expr());
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

            // Keep length/data_rlc the same on rows where we don't absorb data
            cb.condition(
                and::expr([
                    meta.query_fixed(q_enable, Rotation::cur())
                        - meta.query_fixed(q_first, Rotation::cur()),
                    not::expr(q_padding),
                ]),
                |cb| {
                    cb.require_equal("length equality check", length.clone(), length_prev.clone());
                    cb.require_equal(
                        "data_rlc equality check",
                        data_rlc.clone(),
                        data_rlc_prev.clone(),
                    );
                },
            );

            cb.gate(1.expr())
        });

        println!("degree: {}", meta.degree());

        KeccakBitConfig {
            q_enable,
            q_first,
            q_round,
            q_absorb,
            q_padding,
            q_padding_last,
            is_final,
            length,
            data_rlc,
            hash_rlc,
            state,
            theta_c,
            input,
            is_paddings,
            data_rlcs,
            round_cst,
            theta_c_table,
            _marker: PhantomData,
        }
    }

    fn assign(
        &self,
        mut layouter: impl Layouter<F>,
        _size: usize,
        witness: &[KeccakRow<F>],
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "assign keccak rounds",
            |mut region| {
                for (offset, keccak_row) in witness.iter().enumerate() {
                    self.set_row(&mut region, offset, keccak_row)?;
                }
                Ok(())
            },
        )
    }

    fn set_row(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        row: &KeccakRow<F>,
    ) -> Result<(), Error> {
        let round = (offset + NUM_ROUNDS) % (NUM_ROUNDS + 1);

        // Fixed selectors
        for (name, column, value) in &[
            ("q_enable", self.q_enable, F::from(true)),
            ("q_first", self.q_first, F::from(offset == 0)),
            ("q_round", self.q_round, F::from(round != 24)),
            ("q_absorb", self.q_absorb, F::from(round == 24)),
            ("q_padding", self.q_padding, F::from(row.q_padding as u64)),
            (
                "q_padding_last",
                self.q_padding_last,
                F::from(row.q_padding_last as u64),
            ),
        ] {
            region.assign_fixed(
                || format!("assign {} {}", name, offset),
                *column,
                offset,
                || Ok(*value),
            )?;
        }

        // Keccak data
        for (name, column, value) in &[
            ("is_final", self.is_final, F::from(row.is_final)),
            ("length", self.length, F::from(row.length as u64)),
            ("data_rlc", self.data_rlc, row.data_rlc),
            ("hash_rlc", self.hash_rlc, row.hash_rlc),
        ] {
            region.assign_advice(
                || format!("assign {} {}", name, offset),
                *column,
                offset,
                || Ok(*value),
            )?;
        }

        // State bits
        for (idx, (bit, column)) in row.state.iter().zip(self.state.iter()).enumerate() {
            region.assign_advice(
                || format!("assign state bit {} {}", idx, offset),
                *column,
                offset,
                || Ok(F::from(*bit as u64)),
            )?;
        }

        // Theta c bits
        for (idx, (bit, column)) in row.theta_c.iter().zip(self.theta_c.iter()).enumerate() {
            region.assign_advice(
                || format!("assign theta c bit {} {}", idx, offset),
                *column,
                offset,
                || Ok(F::from(*bit as u64)),
            )?;
        }

        // Absorb c bits
        for (idx, (bit, column)) in row.input.iter().zip(self.input.iter()).enumerate() {
            region.assign_advice(
                || format!("assign absorb bits {} {}", idx, offset),
                *column,
                offset,
                || Ok(F::from(*bit as u64)),
            )?;
        }

        // Padding selectors
        for (idx, (is_padding, column)) in row
            .is_paddings
            .iter()
            .zip(self.is_paddings.iter())
            .enumerate()
        {
            region.assign_advice(
                || format!("assign padding selector {} {}", idx, offset),
                *column,
                offset,
                || Ok(F::from(*is_padding as u64)),
            )?;
        }

        // Intermediate data rlcs
        for (idx, (data_rlc, column)) in row.data_rlcs.iter().zip(self.data_rlcs.iter()).enumerate()
        {
            region.assign_advice(
                || format!("assign padding selector {} {}", idx, offset),
                *column,
                offset,
                || Ok(*data_rlc),
            )?;
        }

        // Round constant columns
        if round < 24 {
            for (pos, column) in ROUND_CST_BIT_POS.iter().zip(self.round_cst.iter()) {
                region.assign_fixed(
                    || format!("assign round constant bit {} {}", *pos, offset),
                    *column,
                    offset,
                    || Ok(F::from(((IOTA_ROUND_CST[round] >> *pos) & 1) as u64)),
                )?;
            }
        }

        Ok(())
    }

    pub(crate) fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        let num_bits_per_theta_lookup = get_num_bits_per_theta_lookup();
        layouter.assign_table(
            || "c table",
            |mut table| {
                for (offset, perm) in (0..num_bits_per_theta_lookup)
                    .map(|_| 0..=MAX_INPUT_THETA_LOOKUP)
                    .multi_cartesian_product()
                    .enumerate()
                {
                    let mut compressed_value = 0u64;
                    let mut factor = 1u64;
                    for (idx, input) in perm.iter().enumerate() {
                        compressed_value += input * factor;
                        factor *= MAX_INPUT_THETA_LOOKUP;

                        table.assign_cell(
                            || "theta c output",
                            self.theta_c_table[idx + 1],
                            offset,
                            || Ok(F::from(*input & 1)),
                        )?;
                    }

                    table.assign_cell(
                        || "theta c input",
                        self.theta_c_table[0],
                        offset,
                        || Ok(F::from(compressed_value)),
                    )?;
                }
                Ok(())
            },
        )
    }
}

fn get_absorb_positions() -> Vec<(usize, usize)> {
    let mut absorb_positions = Vec::new();
    for j in 0..5 {
        for i in 0..5 {
            if i + j * 5 < 17 {
                absorb_positions.push((i, j));
            }
        }
    }
    absorb_positions
}

fn keccak<F: Field>(rows: &mut Vec<KeccakRow<F>>, bytes: Vec<u8>, r: F) {
    let mut bits = into_bits(&bytes);
    let mut s = [[[0u8; NUM_BITS_PER_WORD]; 5]; 5];
    let absorb_positions = get_absorb_positions();
    let num_bytes_in_last_block = bytes.len() % RATE;

    // Padding
    bits.push(1);
    while (bits.len() + 1) % RATE_IN_BITS != 0 {
        bits.push(0);
    }
    bits.push(1);

    let mut length = 0usize;
    let mut data_rlc = F::zero();
    let chunks = bits.chunks(RATE_IN_BITS);
    let num_chunks = chunks.len();
    for (idx, chunk) in chunks.enumerate() {
        // Last block for this keccak hash
        let is_final_block = idx == num_chunks - 1;

        // Absorb
        let mut counter = 0;
        for &(i, j) in &absorb_positions {
            for k in 0..64 {
                s[i][j][k] ^= chunk[counter];
                counter += 1;
            }
        }

        let mut counter = 0;
        for (round, round_cst) in IOTA_ROUND_CST.iter().enumerate() {
            let mut input = [0u8; 64];
            if counter < RATE_IN_BITS {
                for bit in input.iter_mut() {
                    *bit = chunk[counter];
                    counter += 1;
                }
            }

            // Theta c
            let mut c = [[0u8; 64]; 5];
            for (i, c) in c.iter_mut().enumerate() {
                let pi = (5 + i - 1) % 5;
                let ni = (i + 1) % 5;
                for (k, c) in c.iter_mut().enumerate() {
                    let pk = (64 + k - 1) % 64;
                    *c = (s[pi][0][k]
                        + s[pi][1][k]
                        + s[pi][2][k]
                        + s[pi][3][k]
                        + s[pi][4][k]
                        + s[ni][1][pk]
                        + s[ni][0][pk]
                        + s[ni][2][pk]
                        + s[ni][3][pk]
                        + s[ni][4][pk])
                        & 1;
                }
            }

            // Flatten bits
            let mut counter = 0;
            let mut state = [0u8; KECCAK_WIDTH_IN_BITS];
            for s in s {
                for s in s {
                    for s in s {
                        state[counter] = s;
                        counter += 1;
                    }
                }
            }

            // Flatten bits
            let mut counter = 0;
            let mut theta_c = [0u8; C_WIDTH];
            for c in c {
                for c in c {
                    theta_c[counter] = c;
                    counter += 1;
                }
            }

            // Padding/Length/Data rlc
            let mut is_paddings = [false; ABSORB_WIDTH_PER_ROW_BYTES];
            let mut data_rlcs = [F::zero(); ABSORB_WIDTH_PER_ROW_BYTES];
            if round < NUM_WORDS_TO_ABSORB {
                for (padding_idx, is_padding) in is_paddings.iter_mut().enumerate() {
                    let byte_idx = round * 8 + padding_idx;
                    *is_padding = if is_final_block && byte_idx >= num_bytes_in_last_block {
                        true
                    } else {
                        length += 1;
                        false
                    };
                }

                data_rlcs[0] = data_rlc;
                for (idx, (byte_bits, padding)) in
                    input.chunks(8).zip(is_paddings.iter()).enumerate()
                {
                    if !*padding {
                        let byte_value: F = from_bits(byte_bits).to_scalar().unwrap();
                        data_rlc = data_rlc * r + byte_value;
                    }
                    if idx < data_rlcs.len() - 1 {
                        data_rlcs[idx + 1] = data_rlc;
                    }
                }
            }

            // Last row for this keccak hash
            let is_final = is_final_block && round == 24;

            // Squeeze
            let hash_rlc = if is_final {
                let hash_bytes = s
                    .into_iter()
                    .take(4)
                    .map(|a| to_bytes(&a[0]))
                    .take(4)
                    .concat();
                rlc::value(&hash_bytes, r)
            } else {
                F::zero()
            };

            rows.push(KeccakRow {
                q_padding: round < NUM_WORDS_TO_ABSORB,
                q_padding_last: round == NUM_WORDS_TO_ABSORB - 1,
                state,
                theta_c,
                input,
                is_paddings,
                data_rlcs,
                is_final: is_final as u64,
                length,
                data_rlc,
                hash_rlc,
            });

            if round < 24 {
                // Theta
                for i in 0..5 {
                    for j in 0..5 {
                        for k in 0..64 {
                            s[i][j][k] ^= c[i][k];
                        }
                    }
                }

                // Rho/Pi
                let mut os = s;
                for (i, b) in s.iter().enumerate() {
                    for (j, b) in b.iter().enumerate() {
                        for k in 0..64 {
                            os[j][(2 * i + 3 * j) % 5][k] = b[(64 + k - RHOM[i][j]) % 64]
                        }
                    }
                }
                s = os;

                // Chi
                let mut os = s;
                for i in 0..5 {
                    for j in 0..5 {
                        for k in 0..64 {
                            os[i][j][k] =
                                s[i][j][k] ^ ((1 - s[(i + 1) % 5][j][k]) * s[(i + 2) % 5][j][k]);
                        }
                    }
                }
                s = os;

                // Iota
                for k in ROUND_CST_BIT_POS {
                    s[0][0][k] ^= ((round_cst >> k) & 1) as u8;
                }
            }
        }
    }
    let hash_bytes = s
        .into_iter()
        .take(4)
        .map(|a| to_bytes(&a[0]))
        .take(4)
        .concat();
    println!("Hash: {:x?}", &hash_bytes);
}

fn multi_keccak<F: Field>(bytes: Vec<Vec<u8>>, r: F) -> Vec<KeccakRow<F>> {
    // Dummy first row so that the initial data can be absorbed
    // The initial data doesn't really matter, `is_final` just needs to be enabled.
    let mut rows: Vec<KeccakRow<F>> = vec![KeccakRow {
        q_padding: false,
        q_padding_last: false,
        state: [0u8; KECCAK_WIDTH_IN_BITS],
        theta_c: [0u8; C_WIDTH],
        input: [0u8; ABSORB_WIDTH_PER_ROW],
        is_paddings: [false; ABSORB_WIDTH_PER_ROW_BYTES],
        data_rlcs: [F::zero(); ABSORB_WIDTH_PER_ROW_BYTES],
        is_final: 1u64,
        length: 0usize,
        data_rlc: F::zero(),
        hash_rlc: F::zero(),
    }];
    // Actual keccaks
    for bytes in bytes {
        keccak(&mut rows, bytes, r);
    }
    rows
}

fn into_bits(bytes: &[u8]) -> Vec<u8> {
    let num_bits = bytes.len() * 8;
    let mut bits: Vec<u8> = vec![0; num_bits];

    let mut counter = 0;
    for byte in bytes {
        for idx in 0u64..8 {
            bits[counter] = (*byte >> idx) & 1;
            counter += 1;
        }
    }

    bits
}

fn from_bits(bits: &[u8]) -> Word {
    let mut value = Word::zero();
    for (idx, bit) in bits.iter().enumerate() {
        value += Word::from(*bit as u64) << idx;
    }
    value
}

fn to_bytes(bits: &[u8]) -> Vec<u8> {
    debug_assert!(bits.len() % 8 == 0, "bits not a multiple of 8");

    let mut bytes = Vec::new();
    for byte_bits in bits.chunks(8) {
        let mut value = 0u8;
        for (idx, bit) in byte_bits.iter().enumerate() {
            value += *bit << idx;
        }
        bytes.push(value);
    }
    bytes
}

fn to_bytes_expr<F: Field>(bits: &[Expression<F>]) -> Vec<Expression<F>> {
    debug_assert!(bits.len() % 8 == 0, "bits not a multiple of 8");

    let mut bytes = Vec::new();
    for byte_bits in bits.chunks(8) {
        let mut value = 0.expr();
        let mut multiplier = F::one();
        for byte in byte_bits.iter() {
            value = value + byte.expr() * multiplier;
            multiplier *= F::from(2);
        }
        bytes.push(value);
    }
    bytes
}

fn compose_rlc<F: Field>(expressions: &[Expression<F>], r: F) -> Expression<F> {
    let mut rlc = expressions[0].clone();
    let mut multiplier = r;
    for expression in expressions[1..].iter() {
        rlc = rlc + expression.clone() * multiplier;
        multiplier *= r;
    }
    rlc
}

#[cfg(test)]
mod tests {
    use std::marker::PhantomData;

    use super::*;
    use halo2_proofs::{dev::MockProver, pairing::bn256::Fr};

    fn verify<F: Field>(k: u32, inputs: Vec<KeccakRow<F>>, success: bool) {
        let circuit = KeccakBitCircuit::<F> {
            inputs,
            size: 2usize.pow(k),
            _marker: PhantomData,
        };

        let prover = MockProver::<F>::run(k, &circuit, vec![]).unwrap();
        let err = prover.verify();
        let print_failures = true;
        if err.is_err() && print_failures {
            for e in err.err().iter() {
                for s in e.iter() {
                    println!("{}", s);
                }
            }
        }
        let err = prover.verify();
        assert_eq!(err.is_ok(), success);
    }

    #[test]
    fn bit_keccak_simple() {
        let k = 8;
        let r = KeccakBitCircuit::r();
        let inputs = multi_keccak(
            vec![
                vec![],
                (0u8..1).collect::<Vec<_>>(),
                (0u8..135).collect::<Vec<_>>(),
                (0u8..136).collect::<Vec<_>>(),
                (0u8..200).collect::<Vec<_>>(),
            ],
            r,
        );
        verify::<Fr>(k, inputs, true);
    }
}
