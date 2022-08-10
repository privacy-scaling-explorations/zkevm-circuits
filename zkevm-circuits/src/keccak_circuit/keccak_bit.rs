use crate::{
    evm_circuit::util::{
        constraint_builder::BaseConstraintBuilder, not, rlc, RandomLinearCombination,
    },
    util::Expr,
};
use eth_types::{Field, Word};
use gadgets::util::xor;
use halo2_proofs::{
    circuit::{Layouter, Region, SimpleFloorPlanner},
    plonk::{
        Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, Selector, TableColumn,
    },
    poly::Rotation,
};
use itertools::Itertools;
use keccak256::keccak_arith::Keccak;
use std::{env::var, marker::PhantomData, vec};

const KECCAK_WIDTH: usize = 5 * 5 * 64;
const ABSORB_WIDTH_PER_ROW: usize = 64;
const C_WIDTH: usize = 5 * 64;
const RHOM: [[usize; 5]; 5] = [
    [0, 36, 3, 41, 18],
    [1, 44, 10, 45, 2],
    [62, 6, 43, 15, 61],
    [28, 55, 25, 21, 56],
    [27, 20, 39, 8, 14],
];
const IOTA_ROUND_CST: [u64; 25] = [
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
const IOTA_ROUND_BIT_POS: [usize; 7] = [0, 1, 3, 7, 15, 31, 63];
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
    s_bits: [u8; KECCAK_WIDTH],
    c_bits: [u8; C_WIDTH],
    a_bits: [u8; ABSORB_WIDTH_PER_ROW],
    q_end: u64,
    hash_rlc: F,
}

/// KeccakBitConfig
#[derive(Clone, Debug)]
pub struct KeccakBitConfig<F> {
    q_enable: Selector,
    q_first: Selector,
    q_round: Column<Fixed>,
    q_absorb: Column<Fixed>,
    q_end: Column<Advice>,
    hash_rlc: Column<Advice>,
    s_bits: [Column<Advice>; KECCAK_WIDTH],
    c_bits: [Column<Advice>; C_WIDTH],
    a_bits: [Column<Advice>; ABSORB_WIDTH_PER_ROW],
    iota_bits: [Column<Fixed>; IOTA_ROUND_BIT_POS.len()],
    c_table: Vec<TableColumn>,
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

        let q_enable = meta.selector();
        let q_first = meta.selector();
        let q_round = meta.fixed_column();
        let q_absorb = meta.fixed_column();
        let q_end = meta.advice_column();
        let hash_rlc = meta.advice_column();
        let s_bits = array_init::array_init(|_| meta.advice_column());
        let c_bits = array_init::array_init(|_| meta.advice_column());
        let a_bits = array_init::array_init(|_| meta.advice_column());
        let iota_bits = array_init::array_init(|_| meta.fixed_column());

        let mut c_table = Vec::new();
        for _ in 0..1 + num_bits_per_theta_lookup {
            c_table.push(meta.lookup_table_column());
        }

        let mut b = vec![vec![vec![0u64.expr(); 64]; 5]; 5];
        let mut b_next = vec![vec![vec![0u64.expr(); 64]; 5]; 5];
        meta.create_gate("Query state bits", |meta| {
            let mut counter = 0;
            for i in 0..5 {
                for j in 0..5 {
                    for k in 0..64 {
                        b[i][j][k] = meta.query_advice(s_bits[counter], Rotation::cur());
                        b_next[i][j][k] = meta.query_advice(s_bits[counter], Rotation::next());
                        counter += 1;
                    }
                }
            }
            vec![0u64.expr()]
        });
        let mut c = vec![vec![0u64.expr(); 64]; 5];
        meta.create_gate("Query Theta c bits", |meta| {
            let mut counter = 0;
            for c in c.iter_mut() {
                for c in c.iter_mut() {
                    *c = meta.query_advice(c_bits[counter], Rotation::cur());
                    counter += 1;
                }
            }
            vec![0u64.expr()]
        });
        let mut a = vec![0u64.expr(); 64];
        let mut a_next = vec![vec![0u64.expr(); 64]; 25];
        meta.create_gate("Absorb bits", |meta| {
            for k in 0..64 {
                a[k] = meta.query_advice(a_bits[k], Rotation::cur());
            }
            for (i, a_next) in a_next.iter_mut().enumerate() {
                for (k, a_next) in a_next.iter_mut().enumerate() {
                    *a_next = meta.query_advice(a_bits[k], Rotation((i + 1) as i32));
                }
            }
            vec![0u64.expr()]
        });

        // Theta lookups
        // TODO: pack 4 (or even more) of these in a single lookup
        // => Total number of lookups: 5*64/4 = 80
        let mut theta = Vec::new();
        for (i, c) in c.iter().enumerate() {
            let pi = (5 + i - 1) % 5;
            let ni = (i + 1) % 5;
            for (k, c) in c.iter().enumerate() {
                let pk = (64 + k - 1) % 64;
                /*input = input * 10u64.expr()
                + (b[pi][0][k].clone()
                    + b[pi][1][k].clone()
                    + b[pi][2][k].clone()
                    + b[pi][3][k].clone()
                    + b[pi][4][k].clone()
                    + b[ni][0][pk].clone()
                    + b[ni][1][pk].clone()
                    + b[ni][2][pk].clone()
                    + b[ni][3][pk].clone()
                    + b[ni][4][pk].clone());*/
                let bit = xor::expr(b[pi][0][k].clone(), b[pi][1][k].clone())
                    + xor::expr(b[pi][2][k].clone(), b[pi][3][k].clone())
                    + xor::expr(b[pi][4][k].clone(), b[ni][0][pk].clone())
                    + xor::expr(b[ni][1][pk].clone(), b[ni][2][pk].clone())
                    + xor::expr(b[ni][3][pk].clone(), b[ni][4][pk].clone());
                /*input = input * MAX_INPUT_THETA_LOOKUP.expr()
                + xor::expr(
                    xor::expr(b[pi][0][k].clone(), b[pi][1][k].clone()),
                    xor::expr(b[pi][2][k].clone(), b[pi][3][k].clone()),
                )
                + xor::expr(
                    xor::expr(b[pi][4][k].clone(), b[ni][0][pk].clone()),
                    xor::expr(b[ni][1][pk].clone(), b[ni][2][pk].clone()),
                )
                + xor::expr(b[ni][3][pk].clone(), b[ni][4][pk].clone());*/
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
                    //input = input * MAX_INPUT_THETA_LOOKUP.expr() + expr.clone();
                    input = input + expr.clone() * factor.expr();
                    factor *= MAX_INPUT_THETA_LOOKUP;
                    tables.push((bit.clone(), c_table[1 + idx]));
                }
                tables.push((input, c_table[0]));
                tables
            });
            lookup_counter += 1;
        }
        println!("Lookups: {}", lookup_counter);

        meta.create_gate("boolean checks", |meta| {
            let mut cb = BaseConstraintBuilder::new(5);

            // Absorb bits
            for a in &a {
                cb.require_boolean("boolean state bit", a.clone());
            }

            // q_end
            cb.require_boolean("boolean q_end", meta.query_advice(q_end, Rotation::cur()));

            cb.gate(meta.query_selector(q_enable))
        });

        meta.create_gate("first row", |meta| {
            let mut cb = BaseConstraintBuilder::new(5);

            // q_end
            cb.require_equal(
                "q_end needs to be enabled on the first row",
                meta.query_advice(q_end, Rotation::cur()),
                1.expr(),
            );

            cb.gate(meta.query_selector(q_first))
        });

        meta.create_gate("round", |meta| {
            let mut cb = BaseConstraintBuilder::new(5);

            let mut b = b.clone();

            // Theta
            let mut ob = vec![vec![vec![0u64.expr(); 64]; 5]; 5];
            for i in 0..5 {
                for j in 0..5 {
                    for k in 0..64 {
                        ob[i][j][k] = xor::expr(b[i][j][k].clone(), c[i][k].clone());
                    }
                }
            }
            b = ob.clone();

            // Rho/Pi
            for (i, b) in b.iter().enumerate() {
                for (j, b) in b.iter().enumerate() {
                    for k in 0..64 {
                        ob[j][(2 * i + 3 * j) % 5][k] = b[(64 + k - RHOM[i][j]) % 64].clone();
                    }
                }
            }
            b = ob.clone();

            // Chi/Iota
            let mut iota_counter = 0;
            for i in 0..5 {
                for j in 0..5 {
                    for k in 0..64 {
                        if i == 0 && j == 0 && IOTA_ROUND_BIT_POS.contains(&k) {
                            cb.require_equal(
                                "round state transition with round constant",
                                not::expr(b[(i + 1) % 5][j][k].clone())
                                    * b[(i + 2) % 5][j][k].clone(),
                                xor::expr(
                                    xor::expr(b[i][j][k].clone(), b_next[i][j][k].clone()),
                                    meta.query_fixed(iota_bits[iota_counter], Rotation::cur()),
                                ),
                            );
                            iota_counter += 1;
                        } else {
                            cb.require_equal(
                                "round state transition",
                                not::expr(b[(i + 1) % 5][j][k].clone())
                                    * b[(i + 2) % 5][j][k].clone(),
                                xor::expr(b[i][j][k].clone(), b_next[i][j][k].clone()),
                            );
                        }
                    }
                }
            }

            cb.gate(meta.query_fixed(q_round, Rotation::cur()))
        });

        meta.create_gate("absorb", |meta| {
            let mut cb = BaseConstraintBuilder::new(5);

            let not_q_end = not::expr(meta.query_advice(q_end, Rotation::cur()));

            let absorb_positions = get_absorb_positions();
            let mut a_slice = 0;
            for j in 0..5 {
                for i in 0..5 {
                    if absorb_positions.contains(&(i, j)) {
                        for k in 0..64 {
                            cb.require_equal(
                                "absorb bit",
                                xor::expr(
                                    b[i][j][k].clone() * not_q_end.clone(),
                                    a_next[a_slice][k].clone(),
                                ),
                                b_next[i][j][k].clone(),
                            );
                        }
                        a_slice += 1;
                    } else {
                        for k in 0..64 {
                            cb.require_equal(
                                "absorb copy",
                                b[i][j][k].clone() * not_q_end.clone(),
                                b_next[i][j][k].clone(),
                            );
                        }
                    }
                }
            }

            cb.gate(meta.query_fixed(q_absorb, Rotation::cur()))
        });

        meta.create_gate("hash rlc", |meta| {
            let mut cb = BaseConstraintBuilder::new(5);

            let hash_bytes = b
                .into_iter()
                .take(4)
                .map(|a| to_bytes_expr(&a[0]))
                .collect::<Vec<_>>()[0..4]
                .concat();

            let rlc = compose_rlc(&hash_bytes, r);

            cb.condition(meta.query_advice(q_end, Rotation::cur()), |cb| {
                cb.require_equal(
                    "hash rlc check",
                    rlc,
                    meta.query_advice(hash_rlc, Rotation::cur()),
                );
            });

            cb.gate(meta.query_selector(q_enable))
        });

        println!("degree: {}", meta.degree());

        KeccakBitConfig {
            q_enable,
            q_first,
            q_round,
            q_absorb,
            q_end,
            hash_rlc,
            s_bits,
            c_bits,
            a_bits,
            iota_bits,
            c_table,
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
                    self.set_row(
                        &mut region,
                        offset,
                        keccak_row.q_end,
                        keccak_row.hash_rlc,
                        keccak_row.s_bits,
                        keccak_row.c_bits,
                        keccak_row.a_bits,
                    )?;
                }
                Ok(())
            },
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn set_row(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        q_end: u64,
        hash_rlc: F,
        s_bits: [u8; KECCAK_WIDTH],
        c_bits: [u8; C_WIDTH],
        a_bits: [u8; ABSORB_WIDTH_PER_ROW],
    ) -> Result<(), Error> {
        let round = (offset + 24) % 25;

        self.q_enable.enable(region, offset)?;

        // q_first
        if offset == 0 {
            self.q_first.enable(region, offset)?;
        }

        // q_round
        region.assign_fixed(
            || format!("assign q_round {}", offset),
            self.q_round,
            offset,
            || Ok(F::from(round != 24)),
        )?;
        // q_absorb
        region.assign_fixed(
            || format!("assign q_absorb {}", offset),
            self.q_absorb,
            offset,
            || Ok(F::from(round == 24)),
        )?;
        // q_end
        region.assign_advice(
            || format!("assign q_end {}", offset),
            self.q_end,
            offset,
            || Ok(F::from(q_end)),
        )?;
        // hash_rlc
        region.assign_advice(
            || format!("assign hash_rlc {}", offset),
            self.hash_rlc,
            offset,
            || Ok(hash_rlc),
        )?;

        // State bits
        for (idx, (bit, column)) in s_bits.iter().zip(self.s_bits.iter()).enumerate() {
            region.assign_advice(
                || format!("assign state bit {} {}", idx, offset),
                *column,
                offset,
                || Ok(F::from(*bit as u64)),
            )?;
        }

        // Theta c bits
        for (idx, (bit, column)) in c_bits.iter().zip(self.c_bits.iter()).enumerate() {
            region.assign_advice(
                || format!("assign theta c bit {} {}", idx, offset),
                *column,
                offset,
                || Ok(F::from(*bit as u64)),
            )?;
        }

        // Absorb c bits
        for (idx, (bit, column)) in a_bits.iter().zip(self.a_bits.iter()).enumerate() {
            region.assign_advice(
                || format!("assign absorb bits {} {}", idx, offset),
                *column,
                offset,
                || Ok(F::from(*bit as u64)),
            )?;
        }

        // Iota bit columns
        if round < 24 {
            for (pos, column) in IOTA_ROUND_BIT_POS.iter().zip(self.iota_bits.iter()) {
                region.assign_fixed(
                    || format!("assign iota bit {} {}", *pos, offset),
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
                            self.c_table[idx + 1],
                            offset,
                            || Ok(F::from(*input & 1)),
                        )?;
                    }

                    table.assign_cell(
                        || "theta c input",
                        self.c_table[0],
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

fn keccak_reference<F: Field>(msg: &[u8], r: F) -> F {
    let mut keccak = Keccak::default();
    keccak.update(msg);
    RandomLinearCombination::<F, 32>::random_linear_combine(keccak.digest().try_into().unwrap(), r)
}

fn keccak<F: Field>(rows: &mut Vec<KeccakRow<F>>, bytes: Vec<u8>, r: F) {
    let mut bits = into_bits(&bytes);
    let rate: usize = 136 * 8;

    let mut b = [[[0u8; 64]; 5]; 5];

    let absorb_positions = get_absorb_positions();

    // Padding
    bits.push(1);
    while (bits.len() + 1) % rate != 0 {
        bits.push(0);
    }
    bits.push(1);

    let chunks = bits.chunks(rate);
    let num_chunks = chunks.len();
    for (idx, chunk) in chunks.enumerate() {
        // Absorb
        let mut counter = 0;
        for &(i, j) in &absorb_positions {
            for k in 0..64 {
                b[i][j][k] ^= chunk[counter];
                counter += 1;
            }
        }

        let mut counter = 0;
        for (round, round_cst) in IOTA_ROUND_CST.iter().enumerate() {
            let mut a_bits = [0u8; 64];
            if counter < rate {
                for a_bit in a_bits.iter_mut() {
                    *a_bit = chunk[counter];
                    counter += 1;
                }
            }

            let mut c = [[0u8; 64]; 5];
            for (i, c) in c.iter_mut().enumerate() {
                let pi = (5 + i - 1) % 5;
                let ni = (i + 1) % 5;
                for (k, c) in c.iter_mut().enumerate() {
                    let pk = (64 + k - 1) % 64;
                    *c = (b[pi][0][k]
                        + b[pi][1][k]
                        + b[pi][2][k]
                        + b[pi][3][k]
                        + b[pi][4][k]
                        + b[ni][1][pk]
                        + b[ni][0][pk]
                        + b[ni][2][pk]
                        + b[ni][3][pk]
                        + b[ni][4][pk])
                        & 1;
                }
            }

            // Flatten bits
            let mut counter = 0;
            let mut s_bits = [0u8; KECCAK_WIDTH];
            for b in b {
                for b in b {
                    for b in b {
                        s_bits[counter] = b;
                        counter += 1;
                    }
                }
            }

            // Flatten bits
            let mut counter = 0;
            let mut c_bits = [0u8; C_WIDTH];
            for c in c {
                for c in c {
                    c_bits[counter] = c;
                    counter += 1;
                }
            }

            let q_end = round == 24 && idx == num_chunks - 1;

            let mut hash_rlc = F::zero();
            if q_end {
                let hash_bytes = b
                    .into_iter()
                    .take(4)
                    .map(|a| to_bytes(&a[0]))
                    .take(4)
                    .concat();
                hash_rlc = rlc::value(&hash_bytes, r);
                println!("RLC: {:x?}", hash_rlc);
            }

            rows.push(KeccakRow {
                s_bits,
                c_bits,
                a_bits,
                q_end: q_end as u64,
                hash_rlc,
            });

            if round < 24 {
                // Theta
                for i in 0..5 {
                    for j in 0..5 {
                        for k in 0..64 {
                            b[i][j][k] ^= c[i][k];
                        }
                    }
                }

                // Rho/Pi
                let mut ob = b;
                for (i, b) in b.iter().enumerate() {
                    for (j, b) in b.iter().enumerate() {
                        for k in 0..64 {
                            ob[j][(2 * i + 3 * j) % 5][k] = b[(64 + k - RHOM[i][j]) % 64]
                        }
                    }
                }
                b = ob;

                // Chi
                let mut ob = b;
                for i in 0..5 {
                    for j in 0..5 {
                        for k in 0..64 {
                            ob[i][j][k] =
                                b[i][j][k] ^ ((1 - b[(i + 1) % 5][j][k]) * b[(i + 2) % 5][j][k]);
                        }
                    }
                }
                b = ob;

                // Iota
                for k in IOTA_ROUND_BIT_POS {
                    b[0][0][k] ^= ((round_cst >> k) & 1) as u8;
                }
            }
        }
    }

    let hash_bytes = b
        .into_iter()
        .take(4)
        .map(|a| to_bytes(&a[0]))
        .take(4)
        .concat();
    println!("Hash: {:x?}", &hash_bytes);
    println!("ref RLC: {:x?}", keccak_reference(&bytes, r));
}

fn multi_keccak<F: Field>(bytes: Vec<Vec<u8>>, r: F) -> Vec<KeccakRow<F>> {
    // Dummy first row so that the initial data is absorbed
    // The initial data doesn't really matter, `q_end` just needs to be enabled.
    let mut rows: Vec<KeccakRow<F>> = vec![KeccakRow {
        s_bits: [0u8; KECCAK_WIDTH],
        c_bits: [0u8; C_WIDTH],
        a_bits: [0u8; ABSORB_WIDTH_PER_ROW],
        q_end: 1u64,
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
