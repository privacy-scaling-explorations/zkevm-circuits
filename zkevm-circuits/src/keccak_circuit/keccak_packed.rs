use crate::evm_circuit::util::{not, rlc};
use crate::{evm_circuit::util::constraint_builder::BaseConstraintBuilder, util::Expr};
use eth_types::Word;
use eth_types::{Field, ToScalar};
use gadgets::util::select;
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
const NUM_WORDS_TO_ABSORB: usize = 17;
const NUM_WORDS_TO_SQUEEZE: usize = 4;

const RHOM: [[usize; 5]; 5] = [
    [0, 36, 3, 41, 18],
    [1, 44, 10, 45, 2],
    [62, 6, 43, 15, 61],
    [28, 55, 25, 21, 56],
    [27, 20, 39, 8, 14],
];
const ROUND_CST: [u64; 24] = [
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

const ABSORB_LOOKUP_RANGE: usize = 3;
const THETA_C_LOOKUP_RANGE: usize = 6;
const THETA_T_LOOKUP_RANGE: usize = 3;
const RHO_PI_LOOKUP_RANGE: usize = 3;
const CHI_BASE_LOOKUP_RANGE: usize = 5;
const CHI_EXT_LOOKUP_RANGE: usize = 7;

const BIT_COUNT: usize = 3;
const BIT_SIZE: usize = 2usize.pow(BIT_COUNT as u32);

const CHI_BASE_LOOKUP_TABLE: [u8; 5] = [0, 1, 1, 0, 0];
const CHI_EXT_LOOKUP_TABLE: [u8; 7] = [0, 0, 1, 1, 0, 0, 1];

fn get_degree() -> usize {
    var("DEGREE")
        .unwrap_or_else(|_| "8".to_string())
        .parse()
        .expect("Cannot parse DEGREE env var as usize")
}

fn get_mode() -> bool {
    let mode: usize = var("MODE")
        .unwrap_or_else(|_| "1".to_string())
        .parse()
        .expect("Cannot parse MODE env var as usize");
    mode == 1
}

fn get_num_bits_per_lookup(range: usize) -> usize {
    let num_unusable_rows = 31;
    let degree = get_degree() as u32;
    let mut num_bits = 1;
    while range.pow(num_bits + 1) + num_unusable_rows <= 2usize.pow(degree) {
        num_bits += 1;
    }
    num_bits as usize
}

fn get_num_bits_per_absorb_lookup() -> usize {
    get_num_bits_per_lookup(ABSORB_LOOKUP_RANGE)
}

fn get_num_bits_per_theta_c_lookup() -> usize {
    get_num_bits_per_lookup(THETA_C_LOOKUP_RANGE)
}

fn get_num_bits_per_theta_t_lookup() -> usize {
    get_num_bits_per_lookup(THETA_T_LOOKUP_RANGE)
}

fn get_num_bits_per_rho_pi_lookup() -> usize {
    if get_mode() {
        get_num_bits_per_lookup(CHI_BASE_LOOKUP_RANGE.max(RHO_PI_LOOKUP_RANGE))
    } else {
        get_num_bits_per_lookup(RHO_PI_LOOKUP_RANGE)
    }
}

fn get_num_bits_per_base_chi_lookup() -> usize {
    if get_mode() {
        get_num_bits_per_lookup(CHI_BASE_LOOKUP_RANGE.max(RHO_PI_LOOKUP_RANGE))
    } else {
        get_num_bits_per_lookup(CHI_BASE_LOOKUP_RANGE)
    }
}

fn get_num_bits_per_ext_chi_lookup() -> usize {
    get_num_bits_per_lookup(CHI_EXT_LOOKUP_RANGE)
}

/// AbsorbData
#[derive(Clone, Default, Debug, PartialEq)]
pub(crate) struct AbsorbData {
    from: Word,
    absorb: Word,
    result: Word,
}

/// SqueezeData
#[derive(Clone, Default, Debug, PartialEq)]
pub(crate) struct SqueezeData {
    packed: Word,
}

/// KeccakRow
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct KeccakRow<F: Field> {
    state: [F; KECCAK_WIDTH],
    absorb_data: AbsorbData,
    squeeze_data: SqueezeData,
    cell_values: Vec<F>,
    is_final: u64,
    hash_rlc: F,
}

/// Part
#[derive(Clone, Debug)]
pub(crate) struct Part<F: Field> {
    parts: Vec<Expression<F>>,
    expr: Expression<F>,
    num_bits: usize,
}

/// Part Value
#[derive(Clone, Copy, Debug)]
pub(crate) struct PartValue {
    value: Word,
    num_bits: usize,
}

/// KeccakConfig
#[derive(Clone, Debug)]
pub struct KeccakPackedConfig<F> {
    q_enable: Selector,
    q_first: Selector,
    q_round: Column<Fixed>,
    q_absorb: Column<Fixed>,
    q_round_end: Selector,
    is_final: Column<Advice>,
    hash_rlc: Column<Advice>,
    state: [Column<Advice>; KECCAK_WIDTH],
    cell_values: Vec<Column<Advice>>,
    absorb_from: Column<Advice>,
    absorb_data: Column<Advice>,
    absorb_result: Column<Advice>,
    squeeze_packed: Column<Advice>,
    round_cst: Column<Fixed>,
    normalize_3: [TableColumn; 2],
    normalize_4: [TableColumn; 2],
    normalize_6: [TableColumn; 2],
    chi_base_table: [TableColumn; 2],
    chi_ext_table: [TableColumn; 2],
    pack_unpack_table: [TableColumn; 2],
    _marker: PhantomData<F>,
}

/// KeccakPackedCircuit
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
        KeccakPackedConfig::configure(meta, KeccakPackedCircuit::r())
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
        value += part.value * factor;
        factor *= Word::from(BIT_SIZE as u64).pow(Word::from(part.num_bits));
    }
    value
}

fn split<F: Field>(
    meta: &mut ConstraintSystem<F>,
    cell_values: &mut Vec<Column<Advice>>,
    cb: &mut BaseConstraintBuilder<F>,
    input: Expression<F>,
    rot: usize,
    target_part_size: usize,
    normalize: bool,
) -> Vec<Part<F>> {
    let mut parts = Vec::new();
    let word = get_word_parts(target_part_size, rot, normalize);
    for word_part in word.parts {
        let cell_column = meta.advice_column();
        cell_values.push(cell_column);

        let mut part = 0.expr();
        meta.create_gate("Query parts", |meta| {
            part = meta.query_advice(cell_column, Rotation::cur());
            vec![0u64.expr()]
        });

        parts.push(Part {
            num_bits: word_part.bits.len(),
            parts: vec![part.clone()],
            expr: part.clone(),
        });
    }

    // Input parts need to equal original input expression
    cb.require_equal("split", decode(parts.clone()), input);

    parts
}

fn split_value<F: Field>(
    cell_values: &mut Vec<F>,
    input: Word,
    rot: usize,
    target_part_size: usize,
    normalize: bool,
) -> Vec<PartValue> {
    let input_bits = unpack(input);
    assert_eq!(pack(&input_bits), input);

    let mut parts = Vec::new();
    let word = get_word_parts(target_part_size, rot, normalize);
    for word_part in word.parts {
        let mut value = 0u64;
        let mut factor = 1u64;
        for idx in 0..word_part.bits.len() {
            let bit_pos = word_part.bits[idx];
            assert!(input_bits[bit_pos] < BIT_SIZE as u8);
            value += (input_bits[bit_pos] as u64) * factor;
            factor *= BIT_SIZE as u64;
        }
        cell_values.push(F::from(value));
        parts.push(PartValue {
            num_bits: word_part.bits.len(),
            value: Word::from(value),
        });
    }

    assert_eq!(decode_value(parts.clone()), input);
    parts
}

fn get_rotate_count(count: usize, part_size: usize) -> usize {
    (count + part_size - 1) / part_size
}

fn rotate<F: Field>(parts: Vec<Part<F>>, count: usize, part_size: usize) -> Vec<Part<F>> {
    let mut rotated_parts = parts;
    rotated_parts.rotate_right(get_rotate_count(count, part_size));
    rotated_parts
}

fn rotate_value(parts: Vec<PartValue>, count: usize, part_size: usize) -> Vec<PartValue> {
    let mut rotated_parts = parts;
    rotated_parts.rotate_right(get_rotate_count(count, part_size));
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
    do_packing: bool,
    f: fn(&u8) -> u8,
) -> Vec<PartValue> {
    let mut output = Vec::new();
    for input_part in input {
        let input_bits = &unpack(input_part.value)[0..input_part.num_bits];
        let output_bits = input_bits.iter().map(f).collect::<Vec<_>>();
        let value = if do_packing {
            pack(&output_bits)
        } else {
            Word::from(to_bytes(&output_bits)[0])
        };

        cell_values.push(value.to_scalar().unwrap());

        output.push(PartValue {
            num_bits: input_part.num_bits,
            value,
        });
    }
    output
}

fn pack_bit<F: Field>(value: usize, count: usize) -> Expression<F> {
    let mut packed = F::zero();
    let mut factor = F::one();
    for _ in 0..count {
        packed += F::from(value as u64) * factor;
        factor *= F::from(BIT_SIZE as u64);
    }
    Expression::Constant(packed)
}

fn target_part_sizes(part_size: usize) -> Vec<usize> {
    let num_full_chunks = 64 / part_size;
    let partial_chunk_size = 64 % part_size;
    let mut part_sizes = vec![part_size; num_full_chunks];
    if partial_chunk_size > 0 {
        part_sizes.push(partial_chunk_size);
    }
    part_sizes
}

/// Part
#[derive(Clone, Debug)]
pub(crate) struct PartInfo {
    bits: Vec<usize>,
}

/// Part
#[derive(Clone, Debug)]
pub(crate) struct WordParts {
    parts: Vec<PartInfo>,
    rot_idx: usize,
}

fn get_word_parts(part_size: usize, rot: usize, normalize: bool) -> WordParts {
    let mut bits = (0usize..64).collect::<Vec<_>>();
    bits.rotate_right(rot);

    let mut parts = Vec::new();
    let mut rot_idx = 0;

    let mut idx = 0;
    let target_sizes = if normalize {
        target_part_sizes(part_size)
    } else {
        let num_parts_a = rot / part_size;
        let partial_part_a = rot % part_size;

        let num_parts_b = (64 - rot) / part_size;
        let partial_part_b = (64 - rot) % part_size;

        let mut part_sizes = vec![part_size; num_parts_a];
        if partial_part_a > 0 {
            part_sizes.push(partial_part_a);
        }

        part_sizes.extend(vec![part_size; num_parts_b]);
        if partial_part_b > 0 {
            part_sizes.push(partial_part_b);
        }

        part_sizes
    };

    for part_size in target_sizes {
        let mut num_consumed = 0;
        while num_consumed < part_size {
            let mut part_bits: Vec<usize> = Vec::new();
            while num_consumed < part_size {
                if !part_bits.is_empty() && bits[idx] == 0 {
                    break;
                }
                if bits[idx] == 0 {
                    rot_idx = parts.len();
                }
                part_bits.push(bits[idx]);
                idx += 1;
                num_consumed += 1;
            }
            parts.push(PartInfo { bits: part_bits });
        }
    }
    assert_eq!(get_rotate_count(rot, part_size), rot_idx);

    parts.rotate_left(rot_idx);
    assert_eq!(parts[0].bits[0], 0);

    WordParts { parts, rot_idx }
}

fn combine_sub_parts<F: Field>(
    name: &'static str,
    meta: &mut ConstraintSystem<F>,
    lookup_counter: &mut usize,
    input: Vec<Part<F>>,
    part_size: usize,
    range_check_table: TableColumn,
    range_check: bool,
) -> Vec<Part<F>> {
    let target_sizes = target_part_sizes(part_size);
    let mut counter = 0;
    let mut parts = Vec::new();
    let mut input_iter = input.iter();
    while let Some(input_part) = input_iter.next() {
        if input_part.num_bits == target_sizes[counter] {
            parts.push(input_part.clone());
            counter += 1;
        } else if let Some(extra_part) = input_iter.next() {
            assert_eq!(
                input_part.num_bits + extra_part.num_bits,
                target_sizes[counter]
            );

            let factor = F::from(8u64).pow(&[input_part.num_bits as u64, 0, 0, 0]);
            let expr = input_part.expr.clone() + extra_part.expr.clone() * factor;

            // Could do a couple of these together when the parts are small to save some
            // lookups println!("{} + {}", input_part.num_bits,
            // extra_part.num_bits);
            if range_check {
                for part in [input_part, extra_part] {
                    meta.lookup(name, |_| vec![(part.expr.clone(), range_check_table)]);
                    *lookup_counter += 1;
                }
            }

            parts.push(Part {
                num_bits: target_sizes[counter],
                expr,
                parts: vec![input_part.expr.clone(), extra_part.expr.clone()],
            });

            counter += 1;
        } else {
            unreachable!();
        }
    }
    parts
}

fn combine_sub_parts_value(input: Vec<PartValue>, part_size: usize) -> Vec<PartValue> {
    //println!("{:?}", input);

    let target_sizes = target_part_sizes(part_size);

    //println!("{:?}", target_sizes);

    let mut counter = 0;
    let mut parts = Vec::new();
    let mut input_iter = input.iter();
    while let Some(input_part) = input_iter.next() {
        if input_part.num_bits == target_sizes[counter] {
            parts.push(*input_part);
            counter += 1;
        } else if let Some(extra_part) = input_iter.next() {
            assert_eq!(
                input_part.num_bits + extra_part.num_bits,
                target_sizes[counter]
            );

            let factor = 8u64.pow(input_part.num_bits as u32);
            let value = input_part.value + extra_part.value * factor;

            parts.push(PartValue {
                value,
                num_bits: target_sizes[counter],
            });

            counter += 1;
        } else {
            unreachable!();
        }
    }
    parts
}

impl<F: Field> KeccakPackedConfig<F> {
    pub(crate) fn configure(meta: &mut ConstraintSystem<F>, r: F) -> Self {
        let q_enable = meta.selector();
        let q_first = meta.selector();
        let q_round = meta.fixed_column();
        let q_absorb = meta.fixed_column();
        let q_round_end = meta.selector();
        let is_final = meta.advice_column();
        let hash_rlc = meta.advice_column();
        let state = array_init::array_init(|_| meta.advice_column());
        let absorb_from = meta.advice_column();
        let absorb_data = meta.advice_column();
        let absorb_result = meta.advice_column();
        let squeeze_packed = meta.advice_column();
        let round_cst = meta.fixed_column();
        let normalize_3 = array_init::array_init(|_| meta.lookup_table_column());
        let normalize_4 = array_init::array_init(|_| meta.lookup_table_column());
        let normalize_6 = array_init::array_init(|_| meta.lookup_table_column());
        let chi_base_table = array_init::array_init(|_| meta.lookup_table_column());
        let chi_ext_table = array_init::array_init(|_| meta.lookup_table_column());
        let pack_unpack_table = array_init::array_init(|_| meta.lookup_table_column());

        let mut cell_values = Vec::new();

        let mut s = vec![vec![0u64.expr(); 5]; 5];
        let mut s_next = vec![vec![0u64.expr(); 5]; 5];
        let mut round_cst_expr = 0.expr();
        meta.create_gate("Query state bits", |meta| {
            let mut counter = 0;
            for i in 0..5 {
                for j in 0..5 {
                    s[i][j] = meta.query_advice(state[counter], Rotation::cur());
                    s_next[i][j] = meta.query_advice(state[counter], Rotation::next());
                    counter += 1;
                }
            }
            round_cst_expr = meta.query_fixed(round_cst, Rotation::cur());
            vec![0u64.expr()]
        });
        let mut absorb_from_expr = 0u64.expr();
        let mut absorb_data_expr = 0u64.expr();
        let mut absorb_result_expr = 0u64.expr();

        let mut absorb_from_next_expr = vec![0u64.expr(); NUM_WORDS_TO_ABSORB];
        let mut absorb_data_next_expr = vec![0u64.expr(); NUM_WORDS_TO_ABSORB];
        let mut absorb_result_next_expr = vec![0u64.expr(); NUM_WORDS_TO_ABSORB];
        meta.create_gate("Query absorb data", |meta| {
            absorb_from_expr = meta.query_advice(absorb_from, Rotation::cur());
            absorb_data_expr = meta.query_advice(absorb_data, Rotation::cur());
            absorb_result_expr = meta.query_advice(absorb_result, Rotation::cur());

            for i in 0..NUM_WORDS_TO_ABSORB {
                absorb_from_next_expr[i] = meta.query_advice(absorb_from, Rotation((i + 1) as i32));
                absorb_data_next_expr[i] = meta.query_advice(absorb_data, Rotation((i + 1) as i32));
                absorb_result_next_expr[i] =
                    meta.query_advice(absorb_result, Rotation((i + 1) as i32));
            }
            vec![0u64.expr()]
        });

        let mut squeeze_from = 0u64.expr();
        let mut squeeze_from_prev = vec![0u64.expr(); NUM_WORDS_TO_SQUEEZE];
        meta.create_gate("Query absorb data", |meta| {
            squeeze_from = meta.query_advice(squeeze_packed, Rotation::cur());
            for (idx, squeeze_from) in squeeze_from_prev.iter_mut().enumerate() {
                *squeeze_from = meta.query_advice(squeeze_packed, Rotation(-(idx as i32) - 1));
            }
            vec![0u64.expr()]
        });

        let mut cb = BaseConstraintBuilder::new(3);
        let mut total_lookup_counter = 0;

        let pre_s = s.clone();

        // Absorb
        let mut lookup_counter = 0;
        let part_size = get_num_bits_per_absorb_lookup();
        let input = absorb_from_expr + absorb_data_expr;
        let absorb_fat = split(meta, &mut cell_values, &mut cb, input, 0, part_size, false);
        let absorb_res = transform(
            "absorb",
            meta,
            &mut cell_values,
            &mut lookup_counter,
            absorb_fat,
            normalize_3,
        );
        cb.require_equal("absorb result", decode(absorb_res), absorb_result_expr);
        println!("- Post absorb:");
        println!("Lookups: {}", lookup_counter);
        println!("Columns: {}", cell_values.len());
        total_lookup_counter += lookup_counter;

        // Theta
        let mut lookup_counter = 0;
        let part_size_c = get_num_bits_per_theta_c_lookup();
        let part_size_t = get_num_bits_per_theta_t_lookup();
        let mut bc = Vec::new();
        for b in s.iter() {
            let c = b[0].clone() + b[1].clone() + b[2].clone() + b[3].clone() + b[4].clone();
            let bc_fat = split(meta, &mut cell_values, &mut cb, c, 1, part_size_c, false);
            let bc_thin = transform(
                "theta c",
                meta,
                &mut cell_values,
                &mut lookup_counter,
                bc_fat.clone(),
                normalize_6,
            );
            bc.push(bc_thin);
        }

        let mut os = vec![vec![0u64.expr(); 5]; 5];
        for i in 0..5 {
            if get_mode() {
                let t = decode(bc[(i + 4) % 5].clone())
                    + decode(rotate(bc[(i + 1) % 5].clone(), 1, part_size_c));
                for j in 0..5 {
                    os[i][j] = s[i][j].clone() + t.clone();
                }
            } else {
                let t = decode(bc[(i + 4) % 5].clone())
                    + decode(rotate(bc[(i + 1) % 5].clone(), 1, part_size_c));
                let t_fat = split(meta, &mut cell_values, &mut cb, t, 0, part_size_t, false);
                let t_thin = decode(transform(
                    "theta t",
                    meta,
                    &mut cell_values,
                    &mut lookup_counter,
                    t_fat.clone(),
                    normalize_3,
                ));
                for j in 0..5 {
                    os[i][j] = s[i][j].clone() + t_thin.clone();
                }
            }
        }
        s = os.clone();
        println!("- Post theta:");
        println!("Lookups: {}", lookup_counter);
        println!("Columns: {}", cell_values.len());
        total_lookup_counter += lookup_counter;

        // Rho/Pi
        let mut lookup_counter = 0;
        let part_size = get_num_bits_per_base_chi_lookup();
        let mut os = vec![vec![0u64.expr(); 5]; 5];
        let mut os_parts = vec![vec![Vec::new(); 5]; 5];
        let mut num_parts_pre = 0;
        let mut num_parts_post = 0;
        for i in 0..5 {
            for j in 0..5 {
                let s_fat = rotate(
                    split(
                        meta,
                        &mut cell_values,
                        &mut cb,
                        s[i][j].clone(),
                        RHOM[i][j],
                        part_size,
                        true,
                    ),
                    RHOM[i][j],
                    part_size,
                );

                let s_fat = combine_sub_parts(
                    "combine",
                    meta,
                    &mut lookup_counter,
                    s_fat.clone(),
                    part_size,
                    normalize_4[0],
                    true,
                );

                let b_thin = transform(
                    "rho/pi",
                    meta,
                    &mut cell_values,
                    &mut lookup_counter,
                    s_fat.clone(),
                    if get_mode() { normalize_4 } else { normalize_3 },
                );

                //num_parts += b_thin.len();
                if get_mode() {
                    num_parts_pre += b_thin.len();
                    os_parts[j][(2 * i + 3 * j) % 5] = b_thin.clone();
                    num_parts_post += os_parts[j][(2 * i + 3 * j) % 5].len();
                }
                os[j][(2 * i + 3 * j) % 5] = decode(b_thin.clone());
            }
        }

        s = os.clone();
        println!("- Post rho/pi:");
        println!("Lookups: {}", lookup_counter);
        println!("Columns: {}", cell_values.len());
        total_lookup_counter += lookup_counter;

        // Chi
        let mut lookup_counter = 0;
        let part_size_base = get_num_bits_per_base_chi_lookup();
        let part_size_ext = get_num_bits_per_ext_chi_lookup();
        let mut os = vec![vec![0u64.expr(); 5]; 5];
        for i in 0..5 {
            for j in 0..5 {
                if i == 0 && j == 0 {
                    let input = pack_bit(5, 64) + s[(i + 2) % 5][j].clone()
                        - 2.expr() * s[i][j].clone()
                        - s[(i + 1) % 5][j].clone()
                        - 2.expr() * round_cst_expr.clone();
                    let fat = split(
                        meta,
                        &mut cell_values,
                        &mut cb,
                        input,
                        0,
                        part_size_ext,
                        false,
                    );
                    os[i][j] = decode(transform(
                        "chi ext",
                        meta,
                        &mut cell_values,
                        &mut lookup_counter,
                        fat.clone(),
                        chi_ext_table,
                    ));
                    cb.require_equal("next row check", os[i][j].clone(), s_next[i][j].clone());
                } else {
                    let mut fat = Vec::new();
                    if get_mode() {
                        for ((part_a, part_b), part_c) in os_parts[i][j]
                            .iter()
                            .zip(os_parts[(i + 1) % 5][j].iter())
                            .zip(os_parts[(i + 2) % 5][j].iter())
                        {
                            //println!("part size: {}", part.num_bits);
                            let expr = pack_bit(3, part_size_base) + part_b.expr.clone()
                                - 2.expr() * part_a.expr.clone()
                                - part_c.expr.clone();
                            fat.push(Part {
                                num_bits: part_size_base,
                                expr: expr.clone(),
                                parts: vec![expr.clone()],
                            });
                        }
                    } else {
                        let input = pack_bit(3, 64) + s[(i + 1) % 5][j].clone()
                            - 2.expr() * s[i][j].clone()
                            - s[(i + 2) % 5][j].clone();
                        fat = split(
                            meta,
                            &mut cell_values,
                            &mut cb,
                            input,
                            0,
                            part_size_base,
                            false,
                        );
                    }
                    os[i][j] = decode(transform(
                        "chi base",
                        meta,
                        &mut cell_values,
                        &mut lookup_counter,
                        fat.clone(),
                        chi_base_table,
                    ));
                    cb.require_equal("next row check", os[i][j].clone(), s_next[i][j].clone());
                }
            }
        }
        println!("- Post chi:");
        println!("Lookups: {}", lookup_counter);
        println!("Columns: {}", cell_values.len());
        println!("num_parts_pre: {}", num_parts_pre);
        println!("num_parts_post: {}", num_parts_post);
        total_lookup_counter += lookup_counter;

        // Unpack a single word into bytes (for the squeeze)
        // Potential optimization: could potentially do multiple bytes per lookup
        let packed = split(
            meta,
            &mut cell_values,
            &mut cb,
            squeeze_from.clone(),
            0,
            8,
            false,
        );
        transform(
            "squeeze unpack",
            meta,
            &mut cell_values,
            &mut lookup_counter,
            packed,
            pack_unpack_table
                .into_iter()
                .rev()
                .collect::<Vec<_>>()
                .try_into()
                .unwrap(),
        );

        meta.create_gate("input checks", |meta| {
            let mut cb = BaseConstraintBuilder::new(5);
            cb.require_boolean(
                "boolean is_final",
                meta.query_advice(is_final, Rotation::cur()),
            );
            cb.gate(meta.query_selector(q_enable))
        });

        meta.create_gate("first row", |meta| {
            let mut cb = BaseConstraintBuilder::new(5);
            cb.require_equal(
                "is_final needs to be enabled on the first row",
                meta.query_advice(is_final, Rotation::cur()),
                1.expr(),
            );
            cb.gate(meta.query_selector(q_first))
        });

        meta.create_gate("round", |meta| {
            cb.gate(meta.query_fixed(q_round, Rotation::cur()))
        });

        s = pre_s;

        meta.create_gate("absorb", |meta| {
            let mut cb = BaseConstraintBuilder::new(3);

            let is_not_final = not::expr(meta.query_advice(is_final, Rotation::cur()));

            let absorb_positions = get_absorb_positions();
            let mut input_slice = 0;
            for j in 0..5 {
                for i in 0..5 {
                    if absorb_positions.contains(&(i, j)) {
                        cb.condition(is_not_final.clone(), |cb| {
                            cb.require_equal(
                                "absorb verify input",
                                absorb_from_next_expr[input_slice].clone(),
                                s[i][j].clone(),
                            );
                        });
                        cb.require_equal(
                            "absorb result copy",
                            select::expr(
                                is_not_final.clone(),
                                absorb_result_next_expr[input_slice].clone(),
                                absorb_data_next_expr[input_slice].clone(),
                            ),
                            s_next[i][j].clone(),
                        );
                        input_slice += 1;
                    } else {
                        cb.require_equal(
                            "absorb state copy",
                            s[i][j].clone() * is_not_final.clone(),
                            s_next[i][j].clone(),
                        );
                    }
                }
            }

            cb.gate(meta.query_fixed(q_absorb, Rotation::cur()))
        });

        meta.create_gate("squeeze", |meta| {
            let mut cb = BaseConstraintBuilder::new(3);

            let is_final = meta.query_advice(is_final, Rotation::cur());

            // The words to squeeze
            let hash_words: Vec<_> = s
                .into_iter()
                .take(4)
                .map(|a| a[0].clone())
                .take(4)
                .collect();

            // Verify if we converted the correct words to bytes on previous rows
            for (idx, word) in hash_words.iter().enumerate() {
                cb.condition(is_final.clone(), |cb| {
                    cb.require_equal(
                        "squeeze verify packed",
                        word.clone(),
                        squeeze_from_prev[idx].clone(),
                    );
                });
            }

            // Collect the bytes that are spread out over previous rows
            let mut hash_bytes = Vec::new();
            for i in 0..NUM_WORDS_TO_SQUEEZE {
                for b in 0..8 {
                    hash_bytes.push(meta.query_advice(
                        cell_values[cell_values.len() - 8 + b],
                        Rotation(-(i as i32) - 1),
                    ));
                }
            }

            let rlc = compose_rlc(&hash_bytes, r);

            cb.condition(is_final, |cb| {
                cb.require_equal(
                    "hash rlc check",
                    rlc,
                    meta.query_advice(hash_rlc, Rotation::cur()),
                );
            });

            cb.gate(meta.query_selector(q_round_end))
        });
        println!("- Post squeeze:");
        println!("Lookups: {}", lookup_counter);
        println!("Columns: {}", cell_values.len());
        println!("num_parts_pre: {}", num_parts_pre);
        println!("num_parts_post: {}", num_parts_post);
        total_lookup_counter += lookup_counter;

        println!("Degree: {}", meta.degree());
        println!("Minimum rows: {}", meta.minimum_rows());
        println!("Lookups: {}", total_lookup_counter);
        println!("Columns: {}", cell_values.len());
        println!("part_size absorb: {}", get_num_bits_per_absorb_lookup());
        println!("part_size theta: {}", get_num_bits_per_theta_c_lookup());
        println!(
            "part_size theta c: {}",
            get_num_bits_per_lookup(THETA_C_LOOKUP_RANGE)
        );
        println!("part_size theta t: {}", get_num_bits_per_lookup(4));
        println!("part_size rho/pi: {}", get_num_bits_per_rho_pi_lookup());
        println!("part_size chi base: {}", get_num_bits_per_base_chi_lookup());
        println!("part_size chi ext: {}", get_num_bits_per_ext_chi_lookup());
        println!(
            "uniform part sizes: {:?}",
            target_part_sizes(get_num_bits_per_theta_c_lookup())
        );

        KeccakPackedConfig {
            q_enable,
            q_first,
            q_round,
            q_absorb,
            q_round_end,
            is_final,
            hash_rlc,
            state,
            cell_values,
            absorb_from,
            absorb_data,
            absorb_result,
            squeeze_packed,
            round_cst,
            normalize_3,
            normalize_4,
            normalize_6,
            chi_base_table,
            chi_ext_table,
            pack_unpack_table,
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
            || "assign keccak rows",
            |mut region| {
                for (offset, keccak_row) in witness.iter().enumerate() {
                    self.set_row(
                        &mut region,
                        offset,
                        keccak_row.is_final,
                        keccak_row.hash_rlc,
                        keccak_row.state,
                        keccak_row.absorb_data.clone(),
                        keccak_row.squeeze_data.clone(),
                        keccak_row.cell_values.clone(),
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
        is_final: u64,
        hash_rlc: F,
        state: [F; KECCAK_WIDTH],
        absorb_data: AbsorbData,
        squeeze_data: SqueezeData,
        cell_values: Vec<F>,
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
        // q_round_end
        if offset > 0 && round == 24 {
            self.q_round_end.enable(region, offset)?;
        }
        // is_final
        region.assign_advice(
            || format!("assign is_final {}", offset),
            self.is_final,
            offset,
            || Ok(F::from(is_final)),
        )?;
        // hash_rlc
        region.assign_advice(
            || format!("assign hash_rlc {}", offset),
            self.hash_rlc,
            offset,
            || Ok(hash_rlc),
        )?;

        // State bits
        for (idx, (bit, column)) in state.iter().zip(self.state.iter()).enumerate() {
            region.assign_advice(
                || format!("assign state bit {} {}", idx, offset),
                *column,
                offset,
                || Ok(*bit),
            )?;
        }

        // Absorb from
        region.assign_advice(
            || format!("assign absorb frmo {}", offset),
            self.absorb_from,
            offset,
            || Ok(absorb_data.from.to_scalar().unwrap()),
        )?;
        // Absorb data
        region.assign_advice(
            || format!("assign absorb data {}", offset),
            self.absorb_data,
            offset,
            || Ok(absorb_data.absorb.to_scalar().unwrap()),
        )?;
        // Absorb result
        region.assign_advice(
            || format!("assign absorb result {}", offset),
            self.absorb_result,
            offset,
            || Ok(absorb_data.result.to_scalar().unwrap()),
        )?;

        // Squeeze packed
        region.assign_advice(
            || format!("assign squeeze packed {}", offset),
            self.squeeze_packed,
            offset,
            || Ok(squeeze_data.packed.to_scalar().unwrap()),
        )?;

        // Cell values
        for (idx, (bit, column)) in cell_values.iter().zip(self.cell_values.iter()).enumerate() {
            region.assign_advice(
                || format!("assign lookup value {} {}", idx, offset),
                *column,
                offset,
                || Ok(*bit),
            )?;
        }

        // Round constant
        if round < 24 {
            region.assign_fixed(
                || format!("assign round cst {}", offset),
                self.round_cst,
                offset,
                || Ok(pack_u64(ROUND_CST[round]).to_scalar().unwrap()),
            )?;
        }

        Ok(())
    }

    pub(crate) fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        let part_size = get_num_bits_per_lookup(6);
        layouter.assign_table(
            || "normalize_6 table",
            |mut table| {
                for (offset, perm) in (0..part_size)
                    .map(|_| 0u64..6)
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

        let part_size = get_num_bits_per_lookup(4);
        layouter.assign_table(
            || "normalize_4 table",
            |mut table| {
                for (offset, perm) in (0..part_size)
                    .map(|_| 0u64..4)
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

        let part_size = get_num_bits_per_lookup(3);
        layouter.assign_table(
            || "normalize_3 table",
            |mut table| {
                for (offset, perm) in (0..part_size)
                    .map(|_| 0u64..3)
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
                        || "normalize 3 input",
                        self.normalize_3[0],
                        offset,
                        || Ok(F::from(input)),
                    )?;

                    table.assign_cell(
                        || "normalize 3 output",
                        self.normalize_3[1],
                        offset,
                        || Ok(F::from(output)),
                    )?;
                }
                Ok(())
            },
        )?;

        let part_size = get_num_bits_per_base_chi_lookup();
        layouter.assign_table(
            || "chi base table",
            |mut table| {
                for (offset, perm) in (0..part_size)
                    .map(|_| 0..CHI_BASE_LOOKUP_TABLE.len() as u64)
                    .multi_cartesian_product()
                    .enumerate()
                {
                    let mut input = 0u64;
                    let mut output = 0u64;
                    let mut factor = 1u64;
                    for input_part in perm.iter() {
                        input += input_part * factor;
                        output += (CHI_BASE_LOOKUP_TABLE[*input_part as usize] as u64) * factor;
                        factor *= BIT_SIZE as u64;
                    }

                    table.assign_cell(
                        || "chi base input",
                        self.chi_base_table[0],
                        offset,
                        || Ok(F::from(input)),
                    )?;

                    table.assign_cell(
                        || "chi base output",
                        self.chi_base_table[1],
                        offset,
                        || Ok(F::from(output)),
                    )?;
                }
                Ok(())
            },
        )?;

        let part_size = get_num_bits_per_ext_chi_lookup();
        layouter.assign_table(
            || "chi ext table",
            |mut table| {
                for (offset, perm) in (0..part_size)
                    .map(|_| 0..CHI_EXT_LOOKUP_TABLE.len() as u64)
                    .multi_cartesian_product()
                    .enumerate()
                {
                    let mut input = 0u64;
                    let mut output = 0u64;
                    let mut factor = 1u64;
                    for input_part in perm.iter() {
                        input += input_part * factor;
                        output += (CHI_EXT_LOOKUP_TABLE[*input_part as usize] as u64) * factor;
                        factor *= BIT_SIZE as u64;
                    }

                    table.assign_cell(
                        || "chi ext input",
                        self.chi_ext_table[0],
                        offset,
                        || Ok(F::from(input)),
                    )?;

                    table.assign_cell(
                        || "chi ext output",
                        self.chi_ext_table[1],
                        offset,
                        || Ok(F::from(output)),
                    )?;
                }
                Ok(())
            },
        )?;

        layouter.assign_table(
            || "pack unpack table",
            |mut table| {
                for (offset, idx) in (0u64..256).enumerate() {
                    table.assign_cell(
                        || "unpacked",
                        self.pack_unpack_table[0],
                        offset,
                        || Ok(F::from(idx)),
                    )?;

                    let packed: F = pack(&to_bits(&[idx as u8])).to_scalar().unwrap();
                    table.assign_cell(
                        || "packed",
                        self.pack_unpack_table[1],
                        offset,
                        || Ok(packed),
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
            if i + j * 5 < NUM_WORDS_TO_ABSORB {
                absorb_positions.push((i, j));
            }
        }
    }
    absorb_positions
}

fn keccak<F: Field>(rows: &mut Vec<KeccakRow<F>>, bytes: Vec<u8>, r: F) {
    let mut bits = to_bits(&bytes);
    let rate: usize = 136 * 8;

    let mut b = [[Word::zero(); 5]; 5];

    let absorb_positions = get_absorb_positions();

    let all_threes = pack(&[3u8; 64]);
    let all_fives = pack(&[5u8; 64]);

    // Padding
    bits.push(1);
    while (bits.len() + 1) % rate != 0 {
        bits.push(0);
    }
    bits.push(1);

    let chunks = bits.chunks(rate);
    let num_chunks = chunks.len();
    for (idx, chunk) in chunks.enumerate() {
        let mut absorb_rows = Vec::new();
        // Absorb
        for (idx, &(i, j)) in absorb_positions.iter().enumerate() {
            let absorb = pack(&chunk[idx * 64..(idx + 1) * 64]);
            let from = b[i][j];
            b[i][j] = b[i][j] ^ absorb;
            absorb_rows.push(AbsorbData {
                from,
                absorb,
                result: b[i][j],
            });
        }

        let mut hash_words: Vec<Word> = Vec::new();
        for round in 0..25 {
            let mut cell_values = Vec::new();

            let mut absorb_data = AbsorbData::default();
            if round < rate / 64 {
                absorb_data = absorb_rows[round].clone();
            }

            let mut state = [F::zero(); KECCAK_WIDTH];
            for i in 0..5 {
                for j in 0..5 {
                    state[i * 5 + j] = b[i][j].to_scalar().unwrap();
                }
            }

            let pre_b = b;

            // Absorb
            let part_size = get_num_bits_per_absorb_lookup();
            let input = absorb_data.from + absorb_data.absorb;
            let absorb_fat = split_value::<F>(&mut cell_values, input, 0, part_size, false);
            let _absorb_result =
                transform_value(&mut cell_values, absorb_fat.clone(), true, |v| v & 1);

            // Theta
            let part_size_c = get_num_bits_per_theta_c_lookup();
            let part_size_t = get_num_bits_per_theta_t_lookup();
            let mut bc = Vec::new();
            for b in b.iter() {
                let c = b[0] + b[1] + b[2] + b[3] + b[4];
                let bc_fat = split_value::<F>(&mut cell_values, c, 1, part_size_c, false);
                let bc_thin = transform_value(&mut cell_values, bc_fat.clone(), true, |v| v & 1);
                bc.push(bc_thin);
            }
            let mut ob = [[Word::zero(); 5]; 5];
            for i in 0..5 {
                if get_mode() {
                    let t = decode_value(bc[(i + 4) % 5].clone())
                        + decode_value(rotate_value(bc[(i + 1) % 5].clone(), 1, part_size_c));
                    for j in 0..5 {
                        ob[i][j] = b[i][j] + t;
                    }
                } else {
                    let t = decode_value(bc[(i + 4) % 5].clone())
                        + decode_value(rotate_value(bc[(i + 1) % 5].clone(), 1, part_size_c));
                    let t_fat = split_value::<F>(&mut cell_values, t, 0, part_size_t, false);
                    let t_thin = decode_value(transform_value(
                        &mut cell_values,
                        t_fat.clone(),
                        true,
                        |v| v & 1,
                    ));
                    for j in 0..5 {
                        ob[i][j] = b[i][j] + t_thin;
                    }
                }
            }
            b = ob;

            // Rho/Pi
            let part_size = get_num_bits_per_base_chi_lookup();
            let mut ob = [[Word::zero(); 5]; 5];

            let mut ob_parts: [[Vec<PartValue>; 5]; 5] =
                array_init::array_init(|_| array_init::array_init(|_| Vec::new()));
            for i in 0..5 {
                for j in 0..5 {
                    let b_fat = rotate_value(
                        split_value(&mut cell_values, b[i][j], RHOM[i][j], part_size, true),
                        RHOM[i][j],
                        part_size,
                    );
                    let b_fat = combine_sub_parts_value(b_fat.clone(), part_size);
                    let b_thin = transform_value(&mut cell_values, b_fat.clone(), true, |v| v & 1);
                    if get_mode() {
                        ob_parts[j][(2 * i + 3 * j) % 5] = b_thin.clone();
                    }
                    ob[j][(2 * i + 3 * j) % 5] = decode_value(b_thin);
                }
            }
            b = ob;

            // Chi
            let part_size_base = get_num_bits_per_base_chi_lookup();
            let part_size_ext = get_num_bits_per_ext_chi_lookup();
            let mut ob = [[Word::zero(); 5]; 5];
            for i in 0..5 {
                for j in 0..5 {
                    if i == 0 && j == 0 {
                        let input = all_fives + b[(i + 2) % 5][j]
                            - Word::from(2u64) * b[i][j]
                            - b[(i + 1) % 5][j]
                            - Word::from(2u64)
                                * pack_u64(if round < 24 { ROUND_CST[round] } else { 0 });
                        let fat = split_value(&mut cell_values, input, 0, part_size_ext, false);
                        ob[i][j] = decode_value(transform_value(
                            &mut cell_values,
                            fat.clone(),
                            true,
                            |v| CHI_EXT_LOOKUP_TABLE[*v as usize],
                        ));
                    } else {
                        let mut fat = Vec::new();
                        if get_mode() {
                            for ((part_a, part_b), part_c) in ob_parts[i][j]
                                .iter()
                                .zip(ob_parts[(i + 1) % 5][j].iter())
                                .zip(ob_parts[(i + 2) % 5][j].iter())
                            {
                                //println!("part size: {}", part.num_bits);
                                let value = pack(&vec![3u8; part_size_base]) + part_b.value
                                    - Word::from(2u64) * part_a.value
                                    - part_c.value;
                                fat.push(PartValue {
                                    num_bits: part_size_base,
                                    value,
                                });
                            }
                        } else {
                            let input = all_threes + b[(i + 1) % 5][j]
                                - Word::from(2u64) * b[i][j]
                                - b[(i + 2) % 5][j];
                            fat = split_value(&mut cell_values, input, 0, part_size_base, false);
                        }
                        ob[i][j] = decode_value(transform_value(
                            &mut cell_values,
                            fat.clone(),
                            true,
                            |v| CHI_BASE_LOOKUP_TABLE[*v as usize],
                        ));
                    }
                }
            }
            b = ob;

            if round == 24 {
                b = pre_b;
            }

            let is_final = round == 24 && idx == num_chunks - 1;

            // The words to squeeze out
            hash_words = pre_b.into_iter().take(4).map(|a| a[0]).take(4).collect();

            let mut hash_rlc = F::zero();
            if is_final {
                let hash_bytes = b
                    .into_iter()
                    .take(4)
                    .map(|a| to_bytes(&unpack(a[0])))
                    .take(4)
                    .concat();
                hash_rlc = rlc::value(&hash_bytes, r);
                println!("RLC: {:x?}", hash_rlc);
            }

            rows.push(KeccakRow {
                state,
                absorb_data,
                squeeze_data: SqueezeData::default(),
                is_final: is_final as u64,
                hash_rlc,
                cell_values,
            });
        }

        // Now that we know the state at the end of the rounds, set the squeeze data
        let num_rows = rows.len();
        for (idx, word) in hash_words.iter().enumerate() {
            let cell_values = &mut rows[num_rows - 2 - idx].cell_values;
            let packed = split_value::<F>(cell_values, *word, 0, 8, false);
            transform_value(cell_values, packed, false, |v| *v);
            rows[num_rows - 2 - idx].squeeze_data.packed = *word;
        }
    }

    let hash_bytes = b
        .into_iter()
        .take(4)
        .map(|a| from_bits(&unpack(a[0])).as_u64().to_le_bytes().to_vec())
        .take(4)
        .concat();
    println!("Hash: {:x?}", &hash_bytes);
}

fn multi_keccak<F: Field>(bytes: Vec<Vec<u8>>, r: F) -> Vec<KeccakRow<F>> {
    // Dummy first row so that the initial data is absorbed
    // The initial data doesn't really matter, `is_final` just needs to be enabled.
    let mut rows: Vec<KeccakRow<F>> = vec![KeccakRow {
        state: [F::zero(); KECCAK_WIDTH],
        absorb_data: AbsorbData {
            from: Word::zero(),
            absorb: Word::zero(),
            result: Word::zero(),
        },
        squeeze_data: SqueezeData {
            packed: Word::zero(),
        },
        is_final: 1u64,
        hash_rlc: F::zero(),
        cell_values: Vec::new(),
    }];
    // Actual keccaks
    for bytes in bytes {
        keccak(&mut rows, bytes, r);
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

fn from_bits(bits: &[u8]) -> Word {
    let mut value = Word::zero();
    for (idx, bit) in bits.iter().enumerate() {
        value += Word::from(*bit as u64) << idx;
    }
    value
}

fn pack(bits: &[u8]) -> Word {
    let mut packed = Word::zero();
    let mut factor = Word::from(1u64);
    for bit in bits {
        packed += Word::from(*bit as u64) * factor;
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

fn pack_u64(value: u64) -> Word {
    pack(
        &((0..64)
            .map(|i| ((value >> i) & 1) as u8)
            .collect::<Vec<_>>()),
    )
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
        let k = 9;
        let r = KeccakPackedCircuit::r();
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
