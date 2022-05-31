use crate::{evm_circuit::util::constraint_builder::BaseConstraintBuilder, util::Expr};
use eth_types::Word;
use eth_types::{Field, ToScalar};
use halo2_proofs::{
    circuit::{Layouter, Region, SimpleFloorPlanner},
    plonk::{
        Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, Selector, TableColumn,
    },
    poly::Rotation,
};
use itertools::Itertools;
use std::{convert::TryInto, env::var, marker::PhantomData, vec};

const KECCAK_WIDTH: usize = 25;
const C_WIDTH: usize = 5 * 64;
const RHOM: [[usize; 5]; 5] = [
    [0, 36, 3, 41, 18],
    [1, 44, 10, 45, 2],
    [62, 6, 43, 15, 61],
    [28, 55, 25, 21, 56],
    [27, 20, 39, 8, 14],
];
const IOTA_ROUND_CST: [u64; 24] = [
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
];
// Bit positions that have a non-zero value in `IOTA_ROUND_CST`.
const IOTA_ROUND_BIT_POS: [usize; 7] = [0, 1, 3, 7, 15, 31, 63];
//const NUM_BITS_PER_THETA_LOOKUP: usize = 3;
const MAX_INPUT_THETA_LOOKUP: u64 = 5;

const BIT_COUNT: usize = 3;
const BIT_SIZE: usize = 2usize.pow(BIT_COUNT as u32);
const PART_SIZE: usize = 3;

const CHI_LOOKUP_TABLE: [u8; 5] = [0, 1, 1, 0, 0];

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

/// KeccakRow
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct KeccakRow<F: Field> {
    s_bits: [F; KECCAK_WIDTH],
    a_bits: F,
    cell_values: Vec<F>,
    q_end: u64,
}

/// Part
#[derive(Clone, Debug)]
pub(crate) struct Part<F: Field> {
    parts: Vec<Expression<F>>,
    expr: Expression<F>,
    num_bits: usize,
}

/// Part Value
#[derive(Clone, Debug)]
pub(crate) struct PartValue {
    value: Word,
    num_bits: usize,
}

/// KeccakConfig
#[derive(Clone, Debug)]
pub struct KeccakPackedConfig<F> {
    q_enable: Selector,
    q_round: Column<Fixed>,
    q_absorb: Column<Fixed>,
    q_end: Column<Advice>,
    s_bits: [Column<Advice>; KECCAK_WIDTH],
    cell_values: Vec<Column<Advice>>,
    a_bits: Column<Advice>,
    iota_bits: [Column<Fixed>; IOTA_ROUND_BIT_POS.len()],
    normalize_4: [TableColumn; 2],
    normalize_6: [TableColumn; 2],
    chi_table: [TableColumn; 2],
    _marker: PhantomData<F>,
}

/// KeccakBitircuit
#[derive(Default)]
pub struct KeccakPackedCircuit<F: Field> {
    inputs: Vec<KeccakRow<F>>,
    size: usize,
    _marker: PhantomData<F>,
}

impl<F: Field> KeccakPackedCircuit<F> {
    fn r() -> F {
        F::from(123456)
    }
}

impl<F: Field> Circuit<F> for KeccakPackedCircuit<F> {
    type Config = KeccakPackedConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        KeccakPackedConfig::configure(meta)
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

fn decode<F: Field>(parts: Vec<Part<F>>) -> Expression<F> {
    let mut value = 0.expr();
    let mut factor = F::from(1u64);
    for part in parts {
        value = value + part.expr.clone() * factor;
        factor *= F::from(BIT_SIZE as u64).pow(&[part.num_bits as u64, 0, 0, 0]);
    }
    value
}

fn decode_value(parts: Vec<PartValue>) -> Word {
    let mut value = Word::zero();
    let mut factor = Word::one();
    for part in parts {
        value = value + part.value * factor;
        factor *= Word::from(BIT_SIZE as u64).pow(Word::from(part.num_bits));
    }
    value
}

fn split<F: Field>(
    meta: &mut ConstraintSystem<F>,
    cell_values: &mut Vec<Column<Advice>>,
    cb: &mut BaseConstraintBuilder<F>,
    input: Expression<F>,
    pos: usize,
) -> Vec<Part<F>> {
    let offset = (64 - pos) % PART_SIZE;
    let mut num_bits_left = 64;
    let mut parts = Vec::new();
    while num_bits_left > 0 {
        let part_size = if num_bits_left == 64 && offset != 0 {
            offset
        } else if num_bits_left < PART_SIZE {
            num_bits_left
        } else {
            PART_SIZE
        };

        let cell_column = meta.advice_column();
        cell_values.push(cell_column);

        let mut part = 0.expr();
        meta.create_gate("Query parts", |meta| {
            part = meta.query_advice(cell_column, Rotation::cur());
            vec![0u64.expr()]
        });

        parts.push(Part {
            num_bits: part_size,
            parts: vec![part.clone()],
            expr: part.clone(),
        });

        num_bits_left -= part_size;
    }

    // Input parts need to equal original input expression
    cb.require_equal("split", decode(parts.clone()), input);

    parts
}

fn split_value<F: Field>(cell_values: &mut Vec<F>, input: Word, pos: usize) -> Vec<PartValue> {
    let offset = (64 - pos) % PART_SIZE;
    let input_bits = unpack(input);
    assert_eq!(pack(&input_bits), input);

    let mut num_bits_left = 64;
    let mut bit_pos = 0;
    let mut parts = Vec::new();
    while num_bits_left > 0 {
        let part_size = if num_bits_left == 64 && offset != 0 {
            offset
        } else if num_bits_left < PART_SIZE {
            num_bits_left
        } else {
            PART_SIZE
        };

        let mut value = 0u64;
        let mut factor = 1u64;
        for _ in 0..part_size {
            assert!(input_bits[bit_pos] < BIT_SIZE as u8);
            value += (input_bits[bit_pos] as u64) * factor;
            factor *= BIT_SIZE as u64;
            bit_pos += 1;
        }

        cell_values.push(F::from(value));

        parts.push(PartValue {
            num_bits: part_size,
            value: Word::from(value),
        });

        num_bits_left -= part_size;
    }
    assert_eq!(decode_value(parts.clone()), input);
    parts
}

fn get_rotate_count(count: usize) -> usize {
    (count + PART_SIZE - 1) / PART_SIZE
}

fn rotate<F: Field>(parts: Vec<Part<F>>, count: usize) -> Vec<Part<F>> {
    let mut rotated_parts = parts.clone();
    rotated_parts.rotate_left(get_rotate_count(count));
    rotated_parts
}

fn rotate_value(parts: Vec<PartValue>, count: usize) -> Vec<PartValue> {
    let mut rotated_parts = parts.clone();
    rotated_parts.rotate_left(get_rotate_count(count));
    rotated_parts
}

fn transform<F: Field>(
    name: &'static str,
    meta: &mut ConstraintSystem<F>,
    cell_values: &mut Vec<Column<Advice>>,
    lookup_counter: &mut usize,
    input: Vec<Part<F>>,
    transform_table: [TableColumn; 2],
) -> Vec<Part<F>> {
    let mut output = Vec::new();
    for input_part in input {
        let part_column = meta.advice_column();
        cell_values.push(part_column);

        let mut output_part = 0.expr();
        meta.lookup(name, |meta| {
            output_part = meta.query_advice(part_column, Rotation::cur());
            vec![
                (input_part.expr.clone(), transform_table[0]),
                (output_part.clone(), transform_table[1]),
            ]
        });
        *lookup_counter += 1;

        output.push(Part {
            num_bits: input_part.num_bits,
            expr: output_part.clone(),
            parts: vec![output_part.clone()],
        });
    }
    output
}

fn transform_value<F: Field>(
    cell_values: &mut Vec<F>,
    input: Vec<PartValue>,
    f: fn(&u8) -> u8,
) -> Vec<PartValue> {
    let mut output = Vec::new();
    for input_part in input {
        let input_bits = &unpack(input_part.value)[0..input_part.num_bits];
        let output_bits = input_bits.iter().map(f).collect::<Vec<_>>();
        let value = pack(&output_bits);

        cell_values.push(value.to_scalar().unwrap());

        output.push(PartValue {
            num_bits: input_part.num_bits,
            value,
        });
    }
    output
}

// TODO: use this to combine two small parts to a full part to reduce
// lookups/output columns
fn combine_sub_parts<F: Field>(input: Vec<Part<F>>) -> Vec<Part<F>> {
    let mut parts = Vec::new();
    let mut input_iter = input.iter();
    while let Some(input_part) = input_iter.next() {
        if input_part.num_bits == PART_SIZE {
            parts.push(input_part.clone());
        } else {
            if let Some(extra_part) = input_iter.next() {
                assert_eq!(input_part.num_bits + extra_part.num_bits, PART_SIZE);

                let factor = F::from(8u64).pow(&[input_part.num_bits as u64, 0, 0, 0]);
                let expr = input_part.expr.clone() + extra_part.expr.clone() * factor;

                parts.push(Part {
                    num_bits: PART_SIZE,
                    expr,
                    parts: vec![input_part.expr.clone(), extra_part.expr.clone()],
                })
            } else {
                unreachable!();
            }
        }
    }
    parts
}

impl<F: Field> KeccakPackedConfig<F> {
    pub(crate) fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let num_bits_per_theta_lookup = get_num_bits_per_theta_lookup();
        println!("num_bits_per_theta_lookup: {}", num_bits_per_theta_lookup);

        let q_enable = meta.selector();
        let q_round = meta.fixed_column();
        let q_absorb = meta.fixed_column();
        let q_end = meta.advice_column();
        let s_bits = array_init::array_init(|_| meta.advice_column());
        let a_bits = meta.advice_column();
        let iota_bits = array_init::array_init(|_| meta.fixed_column());
        let normalize_4 = array_init::array_init(|_| meta.lookup_table_column());
        let normalize_6 = array_init::array_init(|_| meta.lookup_table_column());
        let chi_table = array_init::array_init(|_| meta.lookup_table_column());

        let mut cell_values = Vec::new();

        let mut all_threes = F::zero();
        let mut factor = F::one();
        for _ in 0..64 {
            all_threes = all_threes + F::from(3u64) * factor;
            factor *= F::from(BIT_SIZE as u64);
        }

        let mut b = vec![vec![0u64.expr(); 5]; 5];
        let mut b_next = vec![vec![0u64.expr(); 5]; 5];
        meta.create_gate("Query state bits", |meta| {
            let mut counter = 0;
            for i in 0..5 {
                for j in 0..5 {
                    b[i][j] = meta.query_advice(s_bits[counter], Rotation::cur());
                    b_next[i][j] = meta.query_advice(s_bits[counter], Rotation::next());
                    counter += 1;
                }
            }
            vec![0u64.expr()]
        });
        let mut a = 0u64.expr();
        let mut a_next = vec![0u64.expr(); 25];
        meta.create_gate("Absorb bits", |meta| {
            a = meta.query_advice(a_bits, Rotation::cur());
            for i in 0..25 {
                a_next[i] = meta.query_advice(a_bits, Rotation((i + 1) as i32));
            }
            vec![0u64.expr()]
        });

        let mut cb = BaseConstraintBuilder::new(5);
        let mut lookup_counter = 0;

        // Theta
        let mut bc = Vec::new();
        for i in 0..5 {
            let c = b[i][0].clone()
                + b[i][1].clone()
                + b[i][2].clone()
                + b[i][3].clone()
                + b[i][4].clone();
            let bc_fat = split(meta, &mut cell_values, &mut cb, c, 1);
            let bc_thin = transform(
                "theta",
                meta,
                &mut cell_values,
                &mut lookup_counter,
                bc_fat.clone(),
                normalize_6,
            );
            bc.push(bc_thin);
        }

        let mut ob = vec![vec![0u64.expr(); 5]; 5];
        for i in 0..5 {
            let t = decode(bc[(i + 4) % 5].clone()) + decode(rotate(bc[(i + 1) % 5].clone(), 1));
            for j in 0..5 {
                ob[i][j] = b[i][j].clone() + t.clone();
            }
        }
        b = ob.clone();

        // Rho/Pi
        let mut ob = vec![vec![0u64.expr(); 5]; 5];
        for i in 0..5 {
            for j in 0..5 {
                let b_fat = split(meta, &mut cell_values, &mut cb, b[i][j].clone(), RHOM[i][j]);
                ob[i][j] = decode(transform(
                    "rho/pi",
                    meta,
                    &mut cell_values,
                    &mut lookup_counter,
                    b_fat.clone(),
                    normalize_4,
                ));
            }
        }
        b = ob.clone();

        // Chi
        let mut ob = vec![vec![0u64.expr(); 5]; 5];
        for i in 0..5 {
            for j in 0..5 {
                let input = Expression::Constant(all_threes) + b[(i + 1) % 5][j].clone()
                    - 2.expr() * b[i][j].clone()
                    - b[(i + 2) % 5][j].clone();
                let fat = split(meta, &mut cell_values, &mut cb, input, 0);
                ob[i][j] = decode(transform(
                    "chi",
                    meta,
                    &mut cell_values,
                    &mut lookup_counter,
                    fat.clone(),
                    chi_table,
                ));
                cb.require_equal("next row check", ob[i][j].clone(), b_next[i][j].clone());
            }
        }
        b = ob.clone();

        meta.create_gate("round", |meta| {
            cb.gate(meta.query_fixed(q_round, Rotation::cur()))
        });

        println!("Degree: {}", meta.degree());
        println!("Lookups: {}", lookup_counter);
        println!("Columns: {}", cell_values.len());

        KeccakPackedConfig {
            q_enable,
            q_round,
            q_absorb,
            q_end,
            s_bits,
            cell_values,
            a_bits,
            iota_bits,
            normalize_4,
            normalize_6,
            chi_table,
            _marker: PhantomData,
        }
    }

    pub(crate) fn assign(
        &self,
        mut layouter: impl Layouter<F>,
        _size: usize,
        witness: &[KeccakRow<F>],
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "assign keccak rounds",
            |mut region| {
                let mut offset = 0;
                for keccak_row in witness.iter() {
                    self.set_row(
                        &mut region,
                        offset,
                        keccak_row.q_end,
                        keccak_row.s_bits,
                        keccak_row.a_bits,
                        keccak_row.cell_values.clone(),
                    )?;
                    offset += 1;
                }
                Ok(())
            },
        )
    }

    fn set_row(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        q_end: u64,
        s_bits: [F; KECCAK_WIDTH],
        a_bits: F,
        cell_values: Vec<F>,
    ) -> Result<(), Error> {
        let round = offset % 25;

        self.q_enable.enable(region, offset)?;

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

        // State bits
        for (idx, (bit, column)) in s_bits.iter().zip(self.s_bits.iter()).enumerate() {
            region.assign_advice(
                || format!("assign state bit {} {}", idx, offset),
                *column,
                offset,
                || Ok(F::from(*bit)),
            )?;
        }

        // Absorb c bits
        region.assign_advice(
            || format!("assign absorb bits {}", offset),
            self.a_bits,
            offset,
            || Ok(F::from(a_bits)),
        )?;

        // Cell values
        for (idx, (bit, column)) in cell_values.iter().zip(self.cell_values.iter()).enumerate() {
            region.assign_advice(
                || format!("assign lookup value {} {}", idx, offset),
                *column,
                offset,
                || Ok(F::from(*bit)),
            )?;
        }

        // Iota bit columns
        /*if round < 24 {
            for (pos, column) in IOTA_ROUND_BIT_POS.iter().zip(self.iota_bits.iter()) {
                region.assign_fixed(
                    || format!("assign iota bit {} {}", *pos, offset),
                    *column,
                    offset,
                    || Ok(F::from(((IOTA_ROUND_CST[round] >> *pos) & 1) as u64)),
                )?;
            }
        }*/

        Ok(())
    }

    pub(crate) fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        let num_bits_per_theta_lookup = /*get_num_bits_per_theta_lookup()*/PART_SIZE;
        layouter.assign_table(
            || "normalize_4 table",
            |mut table| {
                for (offset, perm) in (0..num_bits_per_theta_lookup)
                    .map(|_| 0..=3)
                    .multi_cartesian_product()
                    .enumerate()
                {
                    let mut input = 0u64;
                    let mut output = 0u64;
                    let mut factor = 1u64;
                    for input_part in perm.iter() {
                        input += input_part * factor;
                        output += (input_part & 1) * factor;
                        factor *= BIT_SIZE as u64;
                    }

                    table.assign_cell(
                        || "normalize 4 input",
                        self.normalize_4[0],
                        offset,
                        || Ok(F::from(input)),
                    )?;

                    table.assign_cell(
                        || "normalize 4 output",
                        self.normalize_4[1],
                        offset,
                        || Ok(F::from(output)),
                    )?;
                }
                Ok(())
            },
        )?;

        layouter.assign_table(
            || "normalize_6 table",
            |mut table| {
                for (offset, perm) in (0..num_bits_per_theta_lookup)
                    .map(|_| 0..=5)
                    .multi_cartesian_product()
                    .enumerate()
                {
                    let mut input = 0u64;
                    let mut output = 0u64;
                    let mut factor = 1u64;
                    for input_part in perm.iter() {
                        input += input_part * factor;
                        output += (input_part & 1) * factor;
                        factor *= BIT_SIZE as u64;
                    }

                    table.assign_cell(
                        || "normalize 6 input",
                        self.normalize_6[0],
                        offset,
                        || Ok(F::from(input)),
                    )?;

                    table.assign_cell(
                        || "normalize 6 output",
                        self.normalize_6[1],
                        offset,
                        || Ok(F::from(output)),
                    )?;
                }
                Ok(())
            },
        )?;

        layouter.assign_table(
            || "chi table",
            |mut table| {
                for (offset, perm) in (0..num_bits_per_theta_lookup)
                    .map(|_| 0..CHI_LOOKUP_TABLE.len() as u64)
                    .multi_cartesian_product()
                    .enumerate()
                {
                    let mut input = 0u64;
                    let mut output = 0u64;
                    let mut factor = 1u64;
                    for input_part in perm.iter() {
                        input += input_part * factor;
                        output += (CHI_LOOKUP_TABLE[*input_part as usize] as u64) * factor;
                        factor *= BIT_SIZE as u64;
                    }

                    table.assign_cell(
                        || "chi input",
                        self.chi_table[0],
                        offset,
                        || Ok(F::from(input)),
                    )?;

                    table.assign_cell(
                        || "chi output",
                        self.chi_table[1],
                        offset,
                        || Ok(F::from(output)),
                    )?;
                }
                Ok(())
            },
        )
    }
}

fn get_absorb_positions() -> Vec<(usize, usize)> {
    let mut absorb_positions = Vec::new();
    for i in 0..5 {
        for j in 0..5 {
            if i + j * 5 < 17 {
                absorb_positions.push((i, j));
            }
        }
    }
    absorb_positions
}

fn keccak<F: Field>(bytes: Vec<u8>) -> Vec<KeccakRow<F>> {
    let mut rows: Vec<KeccakRow<F>> = Vec::new();

    let mut bits = to_bits(&bytes);
    let rate: usize = 136 * 8;

    let mut b = [[Word::zero(); 5]; 5];

    let absorb_positions = get_absorb_positions();

    let all_threes = pack(&[3u8; 64]);

    // TODO: correct padding
    while bits.len() % rate != 0 {
        bits.push(0);
    }

    let chunks = bits.chunks(rate);
    let num_chunks = chunks.len();
    println!("num_chunks: {}", num_chunks);
    for (idx, chunk) in chunks.enumerate() {
        // Absorb
        let mut counter = 0;
        if idx == 0 {
            for &(i, j) in &absorb_positions {
                b[i][j] += pack(&chunk[counter * 64..(counter + 1) * 64]);
                counter += 1;
            }
        }

        let mut counter = 0;
        for round in 0..25 {
            let mut cell_values = Vec::new();

            let a_bits = pack(&chunk[counter * 64..(counter + 1) * 64])
                .to_scalar()
                .unwrap();
            if counter + 1 < rate / 64 {
                counter += 1;
            }

            let mut counter = 0;
            let mut s_bits = [F::zero(); 25];
            for i in 0..5 {
                for j in 0..5 {
                    s_bits[counter] = b[i][j].to_scalar().unwrap();
                    counter += 1;
                }
            }

            let pre_b = b.clone();

            // Theta
            let mut bc = Vec::new();
            for i in 0..5 {
                let c = b[i][0].clone()
                    + b[i][1].clone()
                    + b[i][2].clone()
                    + b[i][3].clone()
                    + b[i][4].clone();
                let bc_fat = split_value::<F>(&mut cell_values, c, 1);
                let bc_thin = transform_value(&mut cell_values, bc_fat.clone(), |v| v & 1);
                bc.push(bc_thin);
            }
            let mut ob = [[Word::zero(); 5]; 5];
            for i in 0..5 {
                let t = decode_value(bc[(i + 4) % 5].clone())
                    + decode_value(rotate_value(bc[(i + 1) % 5].clone(), 1));
                for j in 0..5 {
                    ob[i][j] = b[i][j].clone() + t.clone();
                }
            }
            b = ob.clone();

            // Rho/Pi
            let mut ob = [[Word::zero(); 5]; 5];
            for i in 0..5 {
                for j in 0..5 {
                    let b_fat = split_value(&mut cell_values, b[i][j].clone(), RHOM[i][j]);
                    ob[i][j] =
                        decode_value(transform_value(&mut cell_values, b_fat.clone(), |v| v & 1));
                }
            }
            b = ob.clone();

            // Chi
            let mut ob = [[Word::zero(); 5]; 5];
            for i in 0..5 {
                for j in 0..5 {
                    let input = all_threes + b[(i + 1) % 5][j].clone()
                        - Word::from(2u64) * b[i][j].clone()
                        - b[(i + 2) % 5][j].clone();
                    let fat = split_value(&mut cell_values, input, 0);
                    ob[i][j] = decode_value(transform_value(&mut cell_values, fat.clone(), |v| {
                        CHI_LOOKUP_TABLE[*v as usize]
                    }));
                }
            }
            b = ob.clone();

            if round == 24 {
                b = pre_b;
            }

            let q_end = round == 24 && idx == num_chunks - 1;
            rows.push(KeccakRow {
                s_bits,
                a_bits,
                q_end: q_end as u64,
                cell_values,
            });
        }
    }

    rows
}

fn to_bits(bytes: &[u8]) -> Vec<u8> {
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

fn pack(bits: &[u8]) -> Word {
    let mut packed = Word::zero();
    let mut factor = Word::from(1u64);
    for bit in bits {
        packed = packed + Word::from(*bit as u64) * factor;
        factor *= BIT_SIZE;
    }
    packed
}

fn unpack(packed: Word) -> [u8; 64] {
    let mut bits = [0; 64];
    for (idx, bit) in bits.iter_mut().enumerate() {
        *bit = ((packed >> (idx * BIT_COUNT)) & Word::from(BIT_SIZE - 1)).as_u32() as u8;
    }
    assert_eq!(pack(&bits), packed);
    bits
}

fn normalize(bits: &[u8]) -> [u8; 64] {
    let mut normalized = [0; 64];
    for (normalized, bit) in normalized.iter_mut().zip(bits.iter()) {
        *normalized = *bit & 1;
    }
    normalized
}

fn rotate_left(bits: &[u8], count: usize) -> [u8; 64] {
    let mut rotated = bits.to_vec();
    rotated.rotate_left(count);
    rotated.try_into().unwrap()
}

#[cfg(test)]
mod tests {
    use std::marker::PhantomData;

    use super::*;
    use halo2_proofs::{dev::MockProver, pairing::bn256::Fr};

    fn verify<F: Field>(k: u32, inputs: Vec<KeccakRow<F>>, success: bool) {
        let circuit = KeccakPackedCircuit::<F> {
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
    fn packed_keccak_simple() {
        let k = 8;
        let inputs = keccak(vec![0b01011010u8; 200]);
        verify::<Fr>(k, inputs, true);
    }
}
