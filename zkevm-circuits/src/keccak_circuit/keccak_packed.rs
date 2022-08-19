use super::util::{
    get_absorb_positions, into_bits, pack, pack_u64, BIT_SIZE, CHI_BASE_LOOKUP_TABLE,
    CHI_EXT_LOOKUP_TABLE, KECCAK_WIDTH, NUM_ROUNDS, ROUND_CST,
};
use crate::evm_circuit::util::{not, rlc};
use crate::keccak_circuit::util::{
    compose_rlc, from_bits, rotate, scatter, target_part_sizes, to_bytes, unpack,
    NUM_BITS_PER_WORD, NUM_WORDS_TO_ABSORB, NUM_WORDS_TO_SQUEEZE, RATE, RATE_IN_BITS, RHOM,
};
use crate::{evm_circuit::util::constraint_builder::BaseConstraintBuilder, util::Expr};
use eth_types::Word;
use eth_types::{Field, ToScalar};
use gadgets::util::{and, select, sum};
use halo2_proofs::{
    circuit::{Layouter, Region, SimpleFloorPlanner},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, TableColumn},
    poly::Rotation,
};
use itertools::Itertools;
use std::{convert::TryInto, env::var, marker::PhantomData, vec};

const MAX_DEGREE: usize = 3;

const ABSORB_LOOKUP_RANGE: usize = 3;
const THETA_C_LOOKUP_RANGE: usize = 6;
const THETA_T_LOOKUP_RANGE: usize = 3;
const RHO_PI_LOOKUP_RANGE: usize = 3;
const CHI_BASE_LOOKUP_RANGE: usize = 5;
const CHI_EXT_LOOKUP_RANGE: usize = 7;

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
    q_padding: bool,
    q_padding_last: bool,
    state: [F; KECCAK_WIDTH],
    absorb_data: AbsorbData,
    squeeze_data: SqueezeData,
    cell_values: Vec<F>,
    is_final: bool,
    length: usize,
    data_rlc: F,
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
    q_enable: Column<Fixed>,
    q_first: Column<Fixed>,
    q_round: Column<Fixed>,
    q_absorb: Column<Fixed>,
    q_round_last: Column<Fixed>,
    q_padding: Column<Fixed>,
    q_padding_last: Column<Fixed>,
    is_final: Column<Advice>,
    length: Column<Advice>,
    data_rlc: Column<Advice>,
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
    witness: Vec<KeccakRow<F>>,
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
        config.assign(layouter, self.size, &self.witness)?;
        Ok(())
    }
}

impl<F: Field> KeccakPackedCircuit<F> {
    /// Creates a new circuit instance
    pub fn new(size: usize) -> Self {
        KeccakPackedCircuit {
            witness: Vec::new(),
            size,
            _marker: PhantomData,
        }
    }

    /// The number of keccak_f's that can be done in this circuit
    pub fn capacity(&self) -> usize {
        // Subtract one for unusable rows
        self.size / (NUM_ROUNDS + 1) - 1
    }

    /// Sets the witness using the data to be hashed
    pub fn generate_witness(&mut self, inputs: &[Vec<u8>]) {
        self.witness = multi_keccak(inputs, KeccakPackedCircuit::r());
    }

    /// Sets the witness using the witness data directly
    fn set_witness(&mut self, witness: &[KeccakRow<F>]) {
        self.witness = witness.to_vec();
    }
}

/// Splits a word into parts
mod split {
    use super::{decode, Part, PartValue};
    use crate::keccak_circuit::util::{get_word_parts, pack, unpack, BIT_SIZE};
    use crate::{evm_circuit::util::constraint_builder::BaseConstraintBuilder, util::Expr};
    use eth_types::Field;
    use eth_types::Word;
    use halo2_proofs::{
        plonk::{Advice, Column, ConstraintSystem, Expression},
        poly::Rotation,
    };
    use std::vec;

    pub(crate) fn expr<F: Field>(
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
        cb.require_equal("split", decode::expr(parts.clone()), input);

        parts
    }

    pub(crate) fn value<F: Field>(
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

        assert_eq!(decode::value::<F>(parts.clone()), input);
        parts
    }
}

/// Recombines parts back together
mod decode {
    use super::{Part, PartValue};
    use crate::keccak_circuit::util::BIT_SIZE;
    use crate::util::Expr;
    use eth_types::Field;
    use eth_types::Word;
    use halo2_proofs::plonk::Expression;

    pub(crate) fn expr<F: Field>(parts: Vec<Part<F>>) -> Expression<F> {
        let mut value = 0.expr();
        let mut factor = F::from(1u64);
        for part in parts {
            value = value + part.expr.clone() * factor;
            factor *= F::from(BIT_SIZE as u64).pow_vartime(&[part.num_bits as u64, 0, 0, 0]);
        }
        value
    }

    pub(crate) fn value<F: Field>(parts: Vec<PartValue>) -> Word {
        let mut value = Word::zero();
        let mut factor = Word::one();
        for part in parts {
            value += part.value * factor;
            factor *= Word::from(BIT_SIZE as u64).pow(Word::from(part.num_bits));
        }
        value
    }
}

/// Transforms data using a lookup
mod transform {
    use super::{Part, PartValue};
    use crate::keccak_circuit::util::{pack, to_bytes, unpack};
    use crate::util::Expr;
    use eth_types::Field;
    use eth_types::{ToScalar, Word};
    use halo2_proofs::plonk::TableColumn;
    use halo2_proofs::{
        plonk::{Advice, Column, ConstraintSystem},
        poly::Rotation,
    };
    use std::vec;

    pub(crate) fn expr<F: Field>(
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

    pub(crate) fn value<F: Field>(
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
                Word::from(to_bytes::value(&output_bits)[0])
            };

            cell_values.push(value.to_scalar().unwrap());

            output.push(PartValue {
                num_bits: input_part.num_bits,
                value,
            });
        }
        output
    }
}

/// Combines parts
mod combine {
    use super::{Part, PartValue};
    use crate::keccak_circuit::util::target_part_sizes;
    use crate::keccak_circuit::util::BIT_SIZE;
    use eth_types::Field;
    use halo2_proofs::plonk::ConstraintSystem;
    use halo2_proofs::plonk::TableColumn;
    use std::vec;

    pub(crate) fn expr<F: Field>(
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
                let factor = F::from(8u64).pow_vartime(&[input_part.num_bits as u64, 0, 0, 0]);
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

    pub(crate) fn value<F: Field>(input: Vec<PartValue>, part_size: usize) -> Vec<PartValue> {
        let target_sizes = target_part_sizes(part_size);
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
                let factor = BIT_SIZE.pow(input_part.num_bits as u32);
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
}

impl<F: Field> KeccakPackedConfig<F> {
    pub(crate) fn configure(meta: &mut ConstraintSystem<F>, r: F) -> Self {
        let q_enable = meta.fixed_column();
        let q_first = meta.fixed_column();
        let q_round = meta.fixed_column();
        let q_absorb = meta.fixed_column();
        let q_round_last = meta.fixed_column();
        let q_padding = meta.fixed_column();
        let q_padding_last = meta.fixed_column();
        let is_final = meta.advice_column();
        let length = meta.advice_column();
        let data_rlc = meta.advice_column();
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

        // State data
        let mut s = vec![vec![0u64.expr(); 5]; 5];
        let mut s_next = vec![vec![0u64.expr(); 5]; 5];
        let mut round_cst_expr = 0.expr();
        meta.create_gate("Query state words", |meta| {
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
        // Absorb data
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
        // Squeeze data
        let mut squeeze_from = 0u64.expr();
        let mut squeeze_from_prev = vec![0u64.expr(); NUM_WORDS_TO_SQUEEZE];
        meta.create_gate("Query squeeze data", |meta| {
            squeeze_from = meta.query_advice(squeeze_packed, Rotation::cur());
            for (idx, squeeze_from) in squeeze_from_prev.iter_mut().enumerate() {
                *squeeze_from = meta.query_advice(squeeze_packed, Rotation(-(idx as i32) - 1));
            }
            vec![0u64.expr()]
        });

        let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
        let mut total_lookup_counter = 0;

        let pre_s = s.clone();

        // Absorb
        let mut lookup_counter = 0;
        let part_size = get_num_bits_per_absorb_lookup();
        let input = absorb_from_expr + absorb_data_expr.clone();
        let absorb_fat = split::expr(meta, &mut cell_values, &mut cb, input, 0, part_size, false);
        let absorb_res = transform::expr(
            "absorb",
            meta,
            &mut cell_values,
            &mut lookup_counter,
            absorb_fat,
            normalize_3,
        );
        cb.require_equal(
            "absorb result",
            decode::expr(absorb_res),
            absorb_result_expr,
        );
        println!("- Post absorb:");
        println!("Lookups: {}", lookup_counter);
        println!("Columns: {}", cell_values.len());
        total_lookup_counter += lookup_counter;

        // Padding
        let mut lookup_counter = 0;
        // Unpack a single word into bytes (for the absorption)
        // Potential optimization: could potentially do multiple bytes per lookup
        let packed = split::expr(
            meta,
            &mut cell_values,
            &mut cb,
            absorb_data_expr,
            0,
            8,
            false,
        );
        let input_bytes = transform::expr(
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
        let mut is_padding_columns = Vec::new();
        let mut data_rlc_columns = Vec::new();
        for _ in input_bytes.iter() {
            let cell_column = meta.advice_column();
            is_padding_columns.push(cell_column);
            cell_values.push(cell_column);
            let cell_column = meta.advice_column();
            data_rlc_columns.push(cell_column);
            cell_values.push(cell_column);
        }
        let mut is_paddings = Vec::new();
        let mut data_rlcs = Vec::new();
        meta.create_gate("Query padding data", |meta| {
            for (is_padding_column, data_rlc_column) in
                is_padding_columns.iter().zip(data_rlc_columns.iter())
            {
                is_paddings.push(meta.query_advice(*is_padding_column, Rotation::cur()));
                data_rlcs.push(meta.query_advice(*data_rlc_column, Rotation::cur()));
            }
            vec![0u64.expr()]
        });
        println!("- Post padding:");
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
            let bc_fat = split::expr(meta, &mut cell_values, &mut cb, c, 1, part_size_c, false);
            let bc_thin = transform::expr(
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
                let t = decode::expr(bc[(i + 4) % 5].clone())
                    + decode::expr(rotate(bc[(i + 1) % 5].clone(), 1, part_size_c));
                for j in 0..5 {
                    os[i][j] = s[i][j].clone() + t.clone();
                }
            } else {
                let t = decode::expr(bc[(i + 4) % 5].clone())
                    + decode::expr(rotate(bc[(i + 1) % 5].clone(), 1, part_size_c));
                let t_fat = split::expr(meta, &mut cell_values, &mut cb, t, 0, part_size_t, false);
                let t_thin = decode::expr(transform::expr(
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
                    split::expr(
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
                let s_fat = combine::expr(
                    "combine",
                    meta,
                    &mut lookup_counter,
                    s_fat.clone(),
                    part_size,
                    normalize_4[0],
                    true,
                );
                let b_thin = transform::expr(
                    "rho/pi",
                    meta,
                    &mut cell_values,
                    &mut lookup_counter,
                    s_fat.clone(),
                    if get_mode() { normalize_4 } else { normalize_3 },
                );
                if get_mode() {
                    num_parts_pre += b_thin.len();
                    os_parts[j][(2 * i + 3 * j) % 5] = b_thin.clone();
                    num_parts_post += os_parts[j][(2 * i + 3 * j) % 5].len();
                }
                os[j][(2 * i + 3 * j) % 5] = decode::expr(b_thin.clone());
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
                    let input = scatter::expr(5, NUM_BITS_PER_WORD) + s[(i + 2) % 5][j].clone()
                        - 2.expr() * s[i][j].clone()
                        - s[(i + 1) % 5][j].clone()
                        - 2.expr() * round_cst_expr.clone();
                    let fat = split::expr(
                        meta,
                        &mut cell_values,
                        &mut cb,
                        input,
                        0,
                        part_size_ext,
                        false,
                    );
                    os[i][j] = decode::expr(transform::expr(
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
                            let expr = scatter::expr(3, part_size_base) + part_b.expr.clone()
                                - 2.expr() * part_a.expr.clone()
                                - part_c.expr.clone();
                            fat.push(Part {
                                num_bits: part_size_base,
                                expr: expr.clone(),
                                parts: vec![expr.clone()],
                            });
                        }
                    } else {
                        let input = scatter::expr(3, NUM_BITS_PER_WORD) + s[(i + 1) % 5][j].clone()
                            - 2.expr() * s[i][j].clone()
                            - s[(i + 2) % 5][j].clone();
                        fat = split::expr(
                            meta,
                            &mut cell_values,
                            &mut cb,
                            input,
                            0,
                            part_size_base,
                            false,
                        );
                    }
                    os[i][j] = decode::expr(transform::expr(
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
        let packed = split::expr(
            meta,
            &mut cell_values,
            &mut cb,
            squeeze_from.clone(),
            0,
            8,
            false,
        );
        transform::expr(
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

        meta.create_gate("round", |meta| {
            cb.gate(meta.query_fixed(q_round, Rotation::cur()))
        });

        meta.create_gate("input checks", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
            cb.require_boolean(
                "boolean is_final",
                meta.query_advice(is_final, Rotation::cur()),
            );
            cb.gate(meta.query_fixed(q_enable, Rotation::cur()))
        });

        meta.create_gate("first row", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
            cb.require_equal(
                "is_final needs to be enabled on the first row",
                meta.query_advice(is_final, Rotation::cur()),
                1.expr(),
            );
            cb.gate(meta.query_fixed(q_first, Rotation::cur()))
        });

        s = pre_s;

        meta.create_gate("absorb", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
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
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
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
            let rlc = compose_rlc::expr(&hash_bytes, r);
            cb.condition(is_final, |cb| {
                cb.require_equal(
                    "hash rlc check",
                    rlc,
                    meta.query_advice(hash_rlc, Rotation::cur()),
                );
            });
            cb.gate(meta.query_fixed(q_round_last, Rotation::cur()))
        });
        println!("- Post squeeze:");
        println!("Lookups: {}", lookup_counter);
        println!("Columns: {}", cell_values.len());
        total_lookup_counter += lookup_counter;

        meta.create_gate("is final", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
            let last_is_padding_in_block = meta.query_advice(
                *is_padding_columns.last().unwrap(),
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

        // May be cleaner to do this padding logic in the byte conversion lookup but
        // currently easier to do it like this.
        meta.create_gate("padding", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
            let prev_is_padding =
                meta.query_advice(*is_padding_columns.last().unwrap(), Rotation::prev());
            let q_padding = meta.query_fixed(q_padding, Rotation::cur());
            let q_padding_last = meta.query_fixed(q_padding_last, Rotation::cur());

            // All padding selectors need to be boolean
            for is_padding in is_paddings.iter() {
                cb.condition(meta.query_fixed(q_enable, Rotation::cur()), |cb| {
                    cb.require_boolean("is_padding boolean", is_padding.expr());
                });
            }
            // This last padding selector will be used on the first round row so needs to be
            // zero
            cb.condition(meta.query_fixed(q_absorb, Rotation::cur()), |cb| {
                cb.require_zero(
                    "last is_padding should be zero on absorb rows",
                    is_paddings.last().unwrap().expr(),
                );
            });

            for idx in 0..is_paddings.len() {
                // Previous padding selector can be on the previous row
                let is_padding_prev = if idx == 0 {
                    prev_is_padding.expr()
                } else {
                    is_paddings[idx - 1].expr()
                };
                let is_first_padding = is_paddings[idx].expr() - is_padding_prev.clone();

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
                            is_paddings[idx].expr(),
                        ]),
                        |cb| {
                            // Input bytes need to be zero, or one if this is the first padding byte
                            cb.require_equal(
                                "padding start/intermediate byte last byte",
                                input_bytes[idx].expr.clone(),
                                is_first_padding.expr(),
                            );
                        },
                    );
                    // Padding start/end byte, only on the last padding row
                    cb.condition(
                        and::expr([q_padding_last.expr(), is_paddings[idx].expr()]),
                        |cb| {
                            // The input byte needs to be 128, unless it's also the first padding
                            // byte and then it's 129
                            cb.require_equal(
                                "padding start/end byte",
                                input_bytes[idx].expr.clone(),
                                is_first_padding.expr() + 128.expr(),
                            );
                        },
                    );
                } else {
                    // Padding start/intermediate byte
                    cb.condition(
                        and::expr([q_padding.expr(), is_paddings[idx].expr()]),
                        |cb| {
                            // Input bytes need to be zero, or one if this is the first padding byte
                            cb.require_equal(
                                "padding start/intermediate byte",
                                input_bytes[idx].expr.clone(),
                                is_first_padding.expr(),
                            );
                        },
                    );
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
                        + sum::expr(
                            is_paddings
                                .iter()
                                .map(|is_padding| not::expr(is_padding.expr())),
                        ),
                );

                // Use intermediate cells to keep the degree low
                let mut new_data_rlc = data_rlc_prev.clone() * not::expr(is_final_prev.expr());
                cb.require_equal("initial data rlc", data_rlcs[0].expr(), new_data_rlc);
                new_data_rlc = data_rlcs[0].expr();
                for (idx, (byte, is_padding)) in
                    input_bytes.iter().zip(is_paddings.iter()).enumerate()
                {
                    new_data_rlc = select::expr(
                        is_padding.expr(),
                        new_data_rlc.clone(),
                        new_data_rlc.clone() * r + byte.expr.clone(),
                    );
                    if idx < data_rlcs.len() - 1 {
                        cb.require_equal(
                            "intermediate data rlc",
                            data_rlcs[idx + 1].expr(),
                            new_data_rlc,
                        );
                        new_data_rlc = data_rlcs[idx + 1].expr();
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
            q_round_last,
            q_padding,
            q_padding_last,
            is_final,
            length,
            data_rlc,
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
            ("q_round", self.q_round, F::from(round != NUM_ROUNDS)),
            (
                "q_round_last",
                self.q_round_last,
                F::from(offset > 0 && round == NUM_ROUNDS),
            ),
            ("q_absorb", self.q_absorb, F::from(round == NUM_ROUNDS)),
            ("q_padding", self.q_padding, F::from(row.q_padding)),
            (
                "q_padding_last",
                self.q_padding_last,
                F::from(row.q_padding_last),
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
            (
                "absorb_from",
                self.absorb_from,
                row.absorb_data.from.to_scalar().unwrap(),
            ),
            (
                "absorb_data",
                self.absorb_data,
                row.absorb_data.absorb.to_scalar().unwrap(),
            ),
            (
                "absorb_result",
                self.absorb_result,
                row.absorb_data.result.to_scalar().unwrap(),
            ),
            (
                "squeeze_packed",
                self.squeeze_packed,
                row.squeeze_data.packed.to_scalar().unwrap(),
            ),
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

        // State words
        for (idx, (word, column)) in row.state.iter().zip(self.state.iter()).enumerate() {
            region.assign_advice(
                || format!("assign state word {} {}", idx, offset),
                *column,
                offset,
                || Ok(*word),
            )?;
        }

        // Cell values
        for (idx, (bit, column)) in row
            .cell_values
            .iter()
            .zip(self.cell_values.iter())
            .enumerate()
        {
            region.assign_advice(
                || format!("assign lookup value {} {}", idx, offset),
                *column,
                offset,
                || Ok(*bit),
            )?;
        }

        // Round constant
        region.assign_fixed(
            || format!("assign round cst {}", offset),
            self.round_cst,
            offset,
            || Ok(pack_u64(ROUND_CST[round]).to_scalar().unwrap()),
        )?;

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

                    let packed: F = pack(&into_bits(&[idx as u8])).to_scalar().unwrap();
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

fn keccak<F: Field>(rows: &mut Vec<KeccakRow<F>>, bytes: &[u8], r: F) {
    let mut bits = into_bits(bytes);
    let mut s = [[Word::zero(); 5]; 5];
    let absorb_positions = get_absorb_positions();
    let num_bytes_in_last_block = bytes.len() % RATE;
    let all_threes = pack(&[3u8; 64]);
    let all_fives = pack(&[5u8; 64]);

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
        let is_final_block = idx == num_chunks - 1;

        // Absorb data
        let mut absorb_rows = Vec::new();
        for (idx, &(i, j)) in absorb_positions.iter().enumerate() {
            let absorb = pack(&chunk[idx * 64..(idx + 1) * 64]);
            let from = s[i][j];
            s[i][j] = s[i][j] ^ absorb;
            absorb_rows.push(AbsorbData {
                from,
                absorb,
                result: s[i][j],
            });
        }

        let mut hash_words: Vec<Word> = Vec::new();
        for round in 0..NUM_ROUNDS + 1 {
            let mut cell_values = Vec::new();

            let mut absorb_data = AbsorbData::default();
            if round < NUM_WORDS_TO_ABSORB {
                absorb_data = absorb_rows[round].clone();
            }

            let mut state = [F::zero(); KECCAK_WIDTH];
            for i in 0..5 {
                for j in 0..5 {
                    state[i * 5 + j] = s[i][j].to_scalar().unwrap();
                }
            }

            let pre_s = s;

            // Absorb
            let part_size = get_num_bits_per_absorb_lookup();
            let input = absorb_data.from + absorb_data.absorb;
            let absorb_fat = split::value(&mut cell_values, input, 0, part_size, false);
            let _absorb_result =
                transform::value(&mut cell_values, absorb_fat.clone(), true, |v| v & 1);

            // Padding
            // Unpack a single word into bytes (for the absorption)
            // Potential optimization: could do multiple bytes per lookup
            let packed = split::value(&mut cell_values, absorb_data.absorb, 0, 8, false);
            let input_bytes = transform::value(&mut cell_values, packed, false, |v| *v);
            let mut is_paddings = Vec::new();
            let mut data_rlcs = Vec::new();
            for _ in input_bytes.iter() {
                is_paddings.push(cell_values.len());
                data_rlcs.push(cell_values.len() + 1);
                cell_values.push(F::zero());
                cell_values.push(F::zero());
            }
            if round < NUM_WORDS_TO_ABSORB {
                let mut paddings = Vec::new();
                for (padding_idx, is_padding) in is_paddings.iter_mut().enumerate() {
                    let byte_idx = round * 8 + padding_idx;
                    let padding = if is_final_block && byte_idx >= num_bytes_in_last_block {
                        true
                    } else {
                        length += 1;
                        false
                    };

                    paddings.push(padding);
                    cell_values[*is_padding] = F::from(padding as u64);
                }

                cell_values[data_rlcs[0]] = data_rlc;
                for (idx, (byte, padding)) in input_bytes.iter().zip(paddings.iter()).enumerate() {
                    if !*padding {
                        let byte_value: F = byte.value.to_scalar().unwrap();
                        data_rlc = data_rlc * r + byte_value;
                    }
                    if idx < data_rlcs.len() - 1 {
                        cell_values[data_rlcs[idx + 1]] = data_rlc;
                    }
                }
            }

            // Theta
            let part_size_c = get_num_bits_per_theta_c_lookup();
            let part_size_t = get_num_bits_per_theta_t_lookup();
            let mut bc = Vec::new();
            for s in s.iter() {
                let c = s[0] + s[1] + s[2] + s[3] + s[4];
                let bc_fat = split::value(&mut cell_values, c, 1, part_size_c, false);
                let bc_thin = transform::value(&mut cell_values, bc_fat.clone(), true, |v| v & 1);
                bc.push(bc_thin);
            }
            let mut os = [[Word::zero(); 5]; 5];
            for i in 0..5 {
                if get_mode() {
                    let t = decode::value::<F>(bc[(i + 4) % 5].clone())
                        + decode::value::<F>(rotate(bc[(i + 1) % 5].clone(), 1, part_size_c));
                    for j in 0..5 {
                        os[i][j] = s[i][j] + t;
                    }
                } else {
                    let t = decode::value::<F>(bc[(i + 4) % 5].clone())
                        + decode::value::<F>(rotate(bc[(i + 1) % 5].clone(), 1, part_size_c));
                    let t_fat = split::value(&mut cell_values, t, 0, part_size_t, false);
                    let t_thin = decode::value::<F>(transform::value(
                        &mut cell_values,
                        t_fat.clone(),
                        true,
                        |v| v & 1,
                    ));
                    for j in 0..5 {
                        os[i][j] = s[i][j] + t_thin;
                    }
                }
            }
            s = os;

            // Rho/Pi
            let part_size = get_num_bits_per_base_chi_lookup();
            let mut os = [[Word::zero(); 5]; 5];
            let mut os_parts: [[Vec<PartValue>; 5]; 5] =
                array_init::array_init(|_| array_init::array_init(|_| Vec::new()));
            for i in 0..5 {
                for j in 0..5 {
                    let b_fat = rotate(
                        split::value(&mut cell_values, s[i][j], RHOM[i][j], part_size, true),
                        RHOM[i][j],
                        part_size,
                    );
                    let b_fat = combine::value::<F>(b_fat.clone(), part_size);
                    let b_thin = transform::value(&mut cell_values, b_fat.clone(), true, |v| v & 1);
                    if get_mode() {
                        os_parts[j][(2 * i + 3 * j) % 5] = b_thin.clone();
                    }
                    os[j][(2 * i + 3 * j) % 5] = decode::value::<F>(b_thin);
                }
            }
            s = os;

            // Chi
            let part_size_base = get_num_bits_per_base_chi_lookup();
            let part_size_ext = get_num_bits_per_ext_chi_lookup();
            let mut os = [[Word::zero(); 5]; 5];
            for i in 0..5 {
                for j in 0..5 {
                    if i == 0 && j == 0 {
                        let input = all_fives + s[(i + 2) % 5][j]
                            - Word::from(2u64) * s[i][j]
                            - s[(i + 1) % 5][j]
                            - Word::from(2u64) * pack_u64(ROUND_CST[round]);
                        let fat = split::value(&mut cell_values, input, 0, part_size_ext, false);
                        os[i][j] = decode::value::<F>(transform::value(
                            &mut cell_values,
                            fat.clone(),
                            true,
                            |v| CHI_EXT_LOOKUP_TABLE[*v as usize],
                        ));
                    } else {
                        let mut fat = Vec::new();
                        if get_mode() {
                            for ((part_a, part_b), part_c) in os_parts[i][j]
                                .iter()
                                .zip(os_parts[(i + 1) % 5][j].iter())
                                .zip(os_parts[(i + 2) % 5][j].iter())
                            {
                                let value = pack(&vec![3u8; part_size_base]) + part_b.value
                                    - Word::from(2u64) * part_a.value
                                    - part_c.value;
                                fat.push(PartValue {
                                    num_bits: part_size_base,
                                    value,
                                });
                            }
                        } else {
                            let input = all_threes + s[(i + 1) % 5][j]
                                - Word::from(2u64) * s[i][j]
                                - s[(i + 2) % 5][j];
                            fat = split::value(&mut cell_values, input, 0, part_size_base, false);
                        }
                        os[i][j] = decode::value::<F>(transform::value(
                            &mut cell_values,
                            fat.clone(),
                            true,
                            |v| CHI_BASE_LOOKUP_TABLE[*v as usize],
                        ));
                    }
                }
            }
            s = os;

            if round == NUM_ROUNDS {
                s = pre_s;
            }

            let is_final = is_final_block && round == NUM_ROUNDS;

            // The words to squeeze out
            hash_words = pre_s.into_iter().take(4).map(|a| a[0]).take(4).collect();

            let hash_rlc = if is_final {
                let hash_bytes = s
                    .into_iter()
                    .take(4)
                    .map(|a| to_bytes::value(&unpack(a[0])))
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
                absorb_data,
                squeeze_data: SqueezeData::default(),
                is_final,
                length,
                data_rlc,
                hash_rlc,
                cell_values,
            });
        }

        // Now that we know the state at the end of the rounds, set the squeeze data
        let num_rows = rows.len();
        for (idx, word) in hash_words.iter().enumerate() {
            let cell_values = &mut rows[num_rows - 2 - idx].cell_values;
            let packed = split::value(cell_values, *word, 0, 8, false);
            transform::value(cell_values, packed, false, |v| *v);
            rows[num_rows - 2 - idx].squeeze_data.packed = *word;
        }
    }

    let hash_bytes = s
        .into_iter()
        .take(4)
        .map(|a| from_bits(&unpack(a[0])).as_u64().to_le_bytes().to_vec())
        .take(4)
        .concat();
    println!("hash: {:x?}", &hash_bytes);
    println!("data rlc: {:x?}", data_rlc);
}

fn multi_keccak<F: Field>(bytes: &[Vec<u8>], r: F) -> Vec<KeccakRow<F>> {
    // Dummy first row so that the initial data is absorbed
    // The initial data doesn't really matter, `is_final` just needs to be enabled.
    let mut rows: Vec<KeccakRow<F>> = vec![KeccakRow {
        q_padding: false,
        q_padding_last: false,
        state: [F::zero(); KECCAK_WIDTH],
        absorb_data: AbsorbData {
            from: Word::zero(),
            absorb: Word::zero(),
            result: Word::zero(),
        },
        squeeze_data: SqueezeData {
            packed: Word::zero(),
        },
        is_final: true,
        length: 0usize,
        data_rlc: F::zero(),
        hash_rlc: F::zero(),
        cell_values: Vec::new(),
    }];
    // Actual keccaks
    for bytes in bytes {
        keccak(&mut rows, bytes, r);
    }
    rows
}

#[cfg(test)]
mod tests {
    use super::*;
    use halo2_proofs::{dev::MockProver, pairing::bn256::Fr};

    fn verify<F: Field>(k: u32, inputs: Vec<Vec<u8>>, success: bool) {
        let mut circuit = KeccakPackedCircuit::new(2usize.pow(k));
        circuit.generate_witness(&inputs);

        let prover = MockProver::<F>::run(k, &circuit, vec![]).unwrap();
        let verify_result = prover.verify();
        if verify_result.is_ok() != success {
            for e in verify_result.err().iter() {
                for s in e.iter() {
                    println!("{}", s);
                }
            }
            panic!();
        }
    }

    #[test]
    fn packed_keccak_simple() {
        let k = 9;
        let inputs = vec![
            vec![],
            (0u8..1).collect::<Vec<_>>(),
            (0u8..135).collect::<Vec<_>>(),
            (0u8..136).collect::<Vec<_>>(),
            (0u8..200).collect::<Vec<_>>(),
        ];
        verify::<Fr>(k, inputs, true);
    }
}
