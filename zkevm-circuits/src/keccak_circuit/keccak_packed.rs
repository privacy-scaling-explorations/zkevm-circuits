use super::util::{
    field_xor, get_absorb_positions, get_num_bits_per_lookup, into_bits, load_lookup_table,
    load_normalize_table, load_pack_table, pack, pack_u64, CHI_BASE_LOOKUP_TABLE,
    CHI_EXT_LOOKUP_TABLE, KECCAK_WIDTH, NUM_ROUNDS, ROUND_CST,
};
use crate::evm_circuit::util::{not, rlc};
use crate::keccak_circuit::util::{
    compose_rlc, extract_field, pack_with_base, rotate, scatter, target_part_sizes, to_bytes,
    unpack, NUM_BITS_PER_BYTE, NUM_BITS_PER_WORD, NUM_WORDS_TO_ABSORB, NUM_WORDS_TO_SQUEEZE, RATE,
    RATE_IN_BITS, RHO_MATRIX,
};
use crate::table::KeccakTable;
use crate::util::Challenges;
use crate::{evm_circuit::util::constraint_builder::BaseConstraintBuilder, util::Expr};
use eth_types::Field;
use gadgets::util::{and, select, sum};
use halo2_proofs::plonk::Challenge;
use halo2_proofs::{
    circuit::{Layouter, Region, SimpleFloorPlanner, Value},
    plonk::{
        Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, TableColumn,
        VirtualCells,
    },
    poly::Rotation,
};
use itertools::Itertools;
use log::{debug, info};
use std::{convert::TryInto, env::var, marker::PhantomData, vec};

const MAX_DEGREE: usize = 3;
const ABSORB_LOOKUP_RANGE: usize = 3;
const THETA_C_LOOKUP_RANGE: usize = 6;
const THETA_T_LOOKUP_RANGE: usize = 3;
const RHO_PI_LOOKUP_RANGE: usize = 3;
const CHI_BASE_LOOKUP_RANGE: usize = 5;
const CHI_EXT_LOOKUP_RANGE: usize = 7;

fn get_mode() -> bool {
    let mode: usize = var("MODE")
        .unwrap_or_else(|_| "1".to_string())
        .parse()
        .expect("Cannot parse MODE env var as usize");
    mode == 1
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
pub(crate) struct AbsorbData<F: Field> {
    from: F,
    absorb: F,
    result: F,
}

/// SqueezeData
#[derive(Clone, Default, Debug, PartialEq)]
pub(crate) struct SqueezeData<F: Field> {
    packed: F,
}

/// KeccakRow
#[derive(Clone, Debug)]
pub(crate) struct KeccakRow<F: Field> {
    q_padding: bool,
    q_padding_last: bool,
    state: [F; KECCAK_WIDTH],
    absorb_data: AbsorbData<F>,
    squeeze_data: SqueezeData<F>,
    cell_values: Vec<F>,
    is_final: bool,
    length: usize,
    data_rlc: Value<F>,
    hash_rlc: Value<F>,
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
pub(crate) struct PartValue<F: Field> {
    value: F,
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
    /// The columns for other circuits to lookup Keccak hash results
    pub keccak_table: KeccakTable,
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
    pack_table: [TableColumn; 2],
    _marker: PhantomData<F>,
}

/// KeccakPackedCircuit
#[derive(Default)]
pub struct KeccakPackedCircuit<F: Field> {
    witness: Vec<Vec<u8>>,
    num_rows: usize,
    _marker: PhantomData<F>,
}

impl<F: Field> Circuit<F> for KeccakPackedCircuit<F> {
    type Config = (KeccakPackedConfig<F>, Challenges<Challenge>);
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let challenges = Challenges::construct(meta);
        let challenge_exprs = challenges.exprs(meta);
        (
            KeccakPackedConfig::configure(meta, challenge_exprs),
            challenges,
        )
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        config.0.load(&mut layouter)?;
        let witness = self.generate_witness(config.1.values(&mut layouter));
        config.0.assign(&mut layouter, &witness)?;
        Ok(())
    }
}

impl<F: Field> KeccakPackedCircuit<F> {
    /// Creates a new circuit instance
    pub fn new(num_rows: usize, inputs: &[Vec<u8>]) -> Self {
        KeccakPackedCircuit {
            witness: inputs.to_vec(),
            num_rows,
            _marker: PhantomData,
        }
    }

    /// The number of keccak_f's that can be done in this circuit
    pub fn capacity(&self) -> usize {
        // Subtract two for unusable rows
        self.num_rows / (NUM_ROUNDS + 1) - 2
    }

    /// Sets the witness using the data to be hashed
    pub(crate) fn generate_witness(&self, challenges: Challenges<Value<F>>) -> Vec<KeccakRow<F>> {
        multi_keccak(&self.witness, challenges, Some(self.capacity()))
            .expect("Too many inputs for given capacity")
    }
}

/// Splits a word into parts
mod split {
    use super::{decode, Part, PartValue};
    use crate::keccak_circuit::util::{unpack, WordParts, BIT_SIZE};
    use crate::{evm_circuit::util::constraint_builder::BaseConstraintBuilder, util::Expr};
    use eth_types::Field;
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
        let word = WordParts::new(target_part_size, rot, normalize);
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
        input: F,
        rot: usize,
        target_part_size: usize,
        normalize: bool,
    ) -> Vec<PartValue<F>> {
        let input_bits = unpack(input);
        let mut parts = Vec::new();
        let word = WordParts::new(target_part_size, rot, normalize);
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
                value: F::from(value),
            });
        }
        debug_assert_eq!(decode::value::<F>(parts.clone()), input);
        parts
    }
}

/// Recombines parts back together
mod decode {
    use super::{Part, PartValue};
    use crate::keccak_circuit::util::BIT_SIZE;
    use crate::util::Expr;
    use eth_types::Field;
    use halo2_proofs::plonk::Expression;

    pub(crate) fn expr<F: Field>(parts: Vec<Part<F>>) -> Expression<F> {
        parts.iter().rev().fold(0.expr(), |acc, part| {
            acc * F::from((BIT_SIZE as u32).pow(part.num_bits as u32) as u64) + part.expr.clone()
        })
    }

    pub(crate) fn value<F: Field>(parts: Vec<PartValue<F>>) -> F {
        parts.iter().rev().fold(F::zero(), |acc, part| {
            acc * F::from((BIT_SIZE as u32).pow(part.num_bits as u32) as u64) + part.value
        })
    }
}

/// Transforms data using lookups
mod transform {
    use super::{Part, PartValue};
    use crate::keccak_circuit::util::{pack, to_bytes, unpack};
    use crate::util::Expr;
    use eth_types::Field;
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
        input: Vec<PartValue<F>>,
        do_packing: bool,
        f: fn(&u8) -> u8,
    ) -> Vec<PartValue<F>> {
        let mut output = Vec::new();
        for input_part in input {
            let input_bits = &unpack(input_part.value)[0..input_part.num_bits];
            let output_bits = input_bits.iter().map(f).collect::<Vec<_>>();
            let value = if do_packing {
                pack(&output_bits)
            } else {
                F::from(to_bytes::value(&output_bits)[0] as u64)
            };

            cell_values.push(value);

            output.push(PartValue {
                num_bits: input_part.num_bits,
                value,
            });
        }
        output
    }
}

/// Combines smaller parts when possible
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
                // No merging to be done, part is already the target size
                parts.push(input_part.clone());
                counter += 1;
            } else if let Some(extra_part) = input_iter.next() {
                // Combine the current and next part
                // The size of this new part needs to match the target size exactly
                debug_assert_eq!(
                    input_part.num_bits + extra_part.num_bits,
                    target_sizes[counter]
                );
                let expr = input_part.expr.clone()
                    + extra_part.expr.clone()
                        * F::from((BIT_SIZE as u32).pow(input_part.num_bits as u32) as u64);
                // Could do a couple of these together when the parts are small to save some
                // lookups
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

    pub(crate) fn value<F: Field>(input: Vec<PartValue<F>>, part_size: usize) -> Vec<PartValue<F>> {
        let target_sizes = target_part_sizes(part_size);
        let mut counter = 0;
        let mut parts = Vec::new();
        let mut input_iter = input.iter();
        while let Some(input_part) = input_iter.next() {
            if input_part.num_bits == target_sizes[counter] {
                parts.push(*input_part);
                counter += 1;
            } else if let Some(extra_part) = input_iter.next() {
                debug_assert_eq!(
                    input_part.num_bits + extra_part.num_bits,
                    target_sizes[counter]
                );
                let value = input_part.value
                    + extra_part.value
                        * F::from((BIT_SIZE as u32).pow(input_part.num_bits as u32) as u64);
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
    pub(crate) fn configure(
        meta: &mut ConstraintSystem<F>,
        challenges: Challenges<Expression<F>>,
    ) -> Self {
        let q_enable = meta.fixed_column();
        let q_first = meta.fixed_column();
        let q_round = meta.fixed_column();
        let q_absorb = meta.fixed_column();
        let q_round_last = meta.fixed_column();
        let q_padding = meta.fixed_column();
        let q_padding_last = meta.fixed_column();

        let keccak_table = KeccakTable::construct(meta);
        let is_final = keccak_table.is_enabled;
        let length = keccak_table.input_len;
        let data_rlc = keccak_table.input_rlc;
        let hash_rlc = keccak_table.output_rlc;

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
        let pack_table = array_init::array_init(|_| meta.lookup_table_column());

        let mut cell_values = Vec::new();
        let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
        let mut total_lookup_counter = 0;

        let start_new_hash = |meta: &mut VirtualCells<F>, rot| {
            // A new hash is started when the previous hash is done or on the first row
            meta.query_fixed(q_first, rot) + meta.query_advice(is_final, rot)
        };

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

        // Store the pre-state
        let pre_s = s.clone();

        // Absorb
        // The absorption happening at the start of the 24 rounds is done spread out
        // over those 24 rounds. In a single round (in 17 of the 24 rounds) a
        // single word is absorbed so the work is spread out. The absorption is
        // done simply by doing state + data and then normalizing the result to [0,1].
        // We also need to convert the input data into bytes to calculate the input data
        // rlc.
        let mut lookup_counter = 0;
        let part_size = get_num_bits_per_absorb_lookup();
        let absorbed = absorb_from_expr + absorb_data_expr.clone();
        let absorb_fat = split::expr(
            meta,
            &mut cell_values,
            &mut cb,
            absorbed,
            0,
            part_size,
            false,
        );
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
        info!("- Post absorb:");
        info!("Lookups: {}", lookup_counter);
        info!("Columns: {}", cell_values.len());
        total_lookup_counter += lookup_counter;

        // Absorb data in bytes
        // Now make the input data available as bytes
        let mut lookup_counter = 0;
        // Potential optimization: could do multiple bytes per lookup
        let packed_parts = split::expr(
            meta,
            &mut cell_values,
            &mut cb,
            absorb_data_expr,
            0,
            NUM_BITS_PER_BYTE,
            false,
        );
        let input_bytes = transform::expr(
            "absorb unpack",
            meta,
            &mut cell_values,
            &mut lookup_counter,
            packed_parts,
            pack_table
                .into_iter()
                .rev()
                .collect::<Vec<_>>()
                .try_into()
                .unwrap(),
        );

        // Padding data
        let mut is_padding_columns = Vec::new();
        let mut data_rlc_columns = Vec::new();
        for _ in input_bytes.iter() {
            cell_values.push(meta.advice_column());
            is_padding_columns.push(*cell_values.last().unwrap());
            cell_values.push(meta.advice_column());
            data_rlc_columns.push(*cell_values.last().unwrap());
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
        info!("- Post padding:");
        info!("Lookups: {}", lookup_counter);
        info!("Columns: {}", cell_values.len());
        total_lookup_counter += lookup_counter;

        // Theta
        // Calculate
        // - `c[i] = s[i][0] + s[i][1] + s[i][2] + s[i][3] + s[i][4]`
        // - `bc[i] = normalize(c)`.
        // - `t[i] = bc[(i + 4) % 5] + rot(bc[(i + 1)% 5], 1)`
        // This is done by splitting the bc values in parts in a way
        // that allows us to also calculate the rotated value "for free".
        let mut lookup_counter = 0;
        let part_size_c = get_num_bits_per_theta_c_lookup();
        let part_size_t = get_num_bits_per_theta_t_lookup();
        let mut bc = Vec::new();
        for s in s.iter() {
            // Calculate `c`
            let c = s[0].clone() + s[1].clone() + s[2].clone() + s[3].clone() + s[4].clone();
            // Calculate `bc` by normalizing `c` by first splitting it into parts
            let bc_fat = split::expr(meta, &mut cell_values, &mut cb, c, 1, part_size_c, false);
            let bc_norm = transform::expr(
                "theta c",
                meta,
                &mut cell_values,
                &mut lookup_counter,
                bc_fat.clone(),
                normalize_6,
            );
            bc.push(bc_norm);
        }
        // Now do `t[i] = bc[(i + 4) % 5] + rot(bc[(i + 1) % 5], 1)` and add it to the
        // state.
        let mut os = vec![vec![0u64.expr(); 5]; 5];
        for i in 0..5 {
            let t = decode::expr(bc[(i + 4) % 5].clone())
                + decode::expr(rotate(bc[(i + 1) % 5].clone(), 1, part_size_c));
            if get_mode() {
                // We don't normalize the result here. We do it as part of the rho/pi step, even
                // though we would only have to normalize 5 values instead of 25, because of the
                // way the rho/pi and chi steps can be combined it's more efficient to
                // do it there (the max value for chi is 4 already so that's the
                // limiting factor).
                for j in 0..5 {
                    os[i][j] = s[i][j].clone() + t.clone();
                }
            } else {
                // Do normalize `t` here already.
                let t_parts =
                    split::expr(meta, &mut cell_values, &mut cb, t, 0, part_size_t, false);
                let t_norm = decode::expr(transform::expr(
                    "theta t",
                    meta,
                    &mut cell_values,
                    &mut lookup_counter,
                    t_parts.clone(),
                    normalize_3,
                ));
                for j in 0..5 {
                    os[i][j] = s[i][j].clone() + t_norm.clone();
                }
            }
        }
        s = os.clone();
        info!("- Post theta:");
        info!("Lookups: {}", lookup_counter);
        info!("Columns: {}", cell_values.len());
        total_lookup_counter += lookup_counter;

        // Rho/Pi
        // For the rotation of rho/pi we split up the words like expected, but in a way
        // that allows reusing the same parts in an optimal way for the chi step.
        // We can save quite a few columns by not recombining the parts after rho/pi and
        // re-splitting the words again before chi. Instead we do chi directly
        // on the output parts of rho/pi. For rho/pi specically we do
        // `s[j][2 * i + 3 * j) % 5] = normalize(rot(s[i][j], RHOM[i][j]))`.
        let mut lookup_counter = 0;
        let part_size = get_num_bits_per_base_chi_lookup();
        let mut os = vec![vec![0u64.expr(); 5]; 5];
        let mut os_parts = vec![vec![Vec::new(); 5]; 5];
        for i in 0..5 {
            for j in 0..5 {
                // Split s into parts and rotate
                let s_parts = rotate(
                    split::expr(
                        meta,
                        &mut cell_values,
                        &mut cb,
                        s[i][j].clone(),
                        RHO_MATRIX[i][j],
                        part_size,
                        true,
                    ),
                    RHO_MATRIX[i][j],
                    part_size,
                );
                // Combine smaller parts that can be transformed together
                let s_parts = combine::expr(
                    "rho/pi combine",
                    meta,
                    &mut lookup_counter,
                    s_parts.clone(),
                    part_size,
                    normalize_4[0],
                    true,
                );
                // Normalize the result
                let s_parts = transform::expr(
                    "rho/pi normalize",
                    meta,
                    &mut cell_values,
                    &mut lookup_counter,
                    s_parts.clone(),
                    if get_mode() { normalize_4 } else { normalize_3 },
                );
                os_parts[j][(2 * i + 3 * j) % 5] = s_parts.clone();
                os[j][(2 * i + 3 * j) % 5] = decode::expr(s_parts.clone());
            }
        }
        s = os.clone();
        info!("- Post rho/pi:");
        info!("Lookups: {}", lookup_counter);
        info!("Columns: {}", cell_values.len());
        total_lookup_counter += lookup_counter;

        // Chi
        // Calculate `s[i][j] = s[i][j] ^ ((~s[(i+1)%5][j]) & s[(i+2)%5][j])`, except
        // for `s[0][0]` where we have to calculate `s[i][j] = s[i][j] ^
        // ((~s[(i+1)%5][j]) & s[(i+2)%5][j]) ^ round_cst`. This is calculated
        // by making use of `CHI_BASE_LOOKUP_TABLE` and `CHI_EXT_LOOKUP_TABLE`.
        let mut lookup_counter = 0;
        let part_size_base = get_num_bits_per_base_chi_lookup();
        let part_size_ext = get_num_bits_per_ext_chi_lookup();
        let mut os = vec![vec![0u64.expr(); 5]; 5];
        for i in 0..5 {
            for j in 0..5 {
                if i == 0 && j == 0 {
                    // Calculate `a ^ ((~b) & c) ^ d` by doing `lookup[5 - 2*a - b + c - 2*d]`
                    let next_s = scatter::expr(5, NUM_BITS_PER_WORD)
                        - 2.expr() * s[i][j].clone()
                        - s[(i + 1) % 5][j].clone()
                        + s[(i + 2) % 5][j].clone()
                        - 2.expr() * round_cst_expr.clone();
                    // Split into parts
                    let next_s_parts = split::expr(
                        meta,
                        &mut cell_values,
                        &mut cb,
                        next_s,
                        0,
                        part_size_ext,
                        false,
                    );
                    // Normalize the data and decode the result
                    os[i][j] = decode::expr(transform::expr(
                        "chi ext",
                        meta,
                        &mut cell_values,
                        &mut lookup_counter,
                        next_s_parts.clone(),
                        chi_ext_table,
                    ));
                    // Make sure the state stored the next row is updated like expected
                    cb.require_equal("next row check", os[i][j].clone(), s_next[i][j].clone());
                } else {
                    // Calculate `a ^ ((~b) & c)` by doing `lookup[3 - 2*a + b - c]`
                    let s_parts = if get_mode() {
                        // Work directly on the Rho/Pi output parts
                        let mut s_parts = Vec::new();
                        for ((part_a, part_b), part_c) in os_parts[i][j]
                            .iter()
                            .zip(os_parts[(i + 1) % 5][j].iter())
                            .zip(os_parts[(i + 2) % 5][j].iter())
                        {
                            let expr = scatter::expr(3, part_size_base)
                                - 2.expr() * part_a.expr.clone()
                                + part_b.expr.clone()
                                - part_c.expr.clone();
                            s_parts.push(Part {
                                num_bits: part_size_base,
                                expr: expr.clone(),
                                parts: vec![expr.clone()],
                            });
                        }
                        s_parts
                    } else {
                        // Work on the decoded words, and split in parts again
                        let input = scatter::expr(3, NUM_BITS_PER_WORD)
                            - 2.expr() * s[i][j].clone()
                            + s[(i + 1) % 5][j].clone()
                            - s[(i + 2) % 5][j].clone();
                        split::expr(
                            meta,
                            &mut cell_values,
                            &mut cb,
                            input,
                            0,
                            part_size_base,
                            false,
                        )
                    };
                    // Normalize the parts and reconstruct the word
                    os[i][j] = decode::expr(transform::expr(
                        "chi base",
                        meta,
                        &mut cell_values,
                        &mut lookup_counter,
                        s_parts.clone(),
                        chi_base_table,
                    ));
                    // Make sure the state stored the next row is updated like expected
                    cb.require_equal("next row check", os[i][j].clone(), s_next[i][j].clone());
                }
            }
        }
        info!("- Post chi:");
        info!("Lookups: {}", lookup_counter);
        info!("Columns: {}", cell_values.len());
        total_lookup_counter += lookup_counter;

        // Squeeze
        // The squeeze happening at the end of the 24 rounds is done spread out
        // over those 24 rounds. In a single round (in 4 of the 24 rounds) a
        // single word is converted to bytes.
        // Potential optimization: could do multiple bytes per lookup
        let packed = split::expr(
            meta,
            &mut cell_values,
            &mut cb,
            squeeze_from.clone(),
            0,
            NUM_BITS_PER_BYTE,
            false,
        );
        transform::expr(
            "squeeze unpack",
            meta,
            &mut cell_values,
            &mut lookup_counter,
            packed,
            pack_table
                .into_iter()
                .rev()
                .collect::<Vec<_>>()
                .try_into()
                .unwrap(),
        );

        // The round constraints that we've been building up till now
        meta.create_gate("round", |meta| {
            cb.gate(meta.query_fixed(q_round, Rotation::cur()))
        });

        // Some general input checks
        meta.create_gate("input checks", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
            cb.require_boolean(
                "boolean is_final",
                meta.query_advice(is_final, Rotation::cur()),
            );
            cb.gate(meta.query_fixed(q_enable, Rotation::cur()))
        });

        // Enforce fixed values on the first row
        meta.create_gate("first row", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
            cb.require_zero(
                "is_final needs to be disabled on the first row",
                meta.query_advice(is_final, Rotation::cur()),
            );
            cb.gate(meta.query_fixed(q_first, Rotation::cur()))
        });

        // Absorb
        meta.create_gate("absorb", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
            let continue_hash = not::expr(start_new_hash(meta, Rotation::cur()));
            let absorb_positions = get_absorb_positions();
            let mut input_slice = 0;
            for j in 0..5 {
                for i in 0..5 {
                    if absorb_positions.contains(&(i, j)) {
                        cb.condition(continue_hash.clone(), |cb| {
                            cb.require_equal(
                                "absorb verify input",
                                absorb_from_next_expr[input_slice].clone(),
                                pre_s[i][j].clone(),
                            );
                        });
                        cb.require_equal(
                            "absorb result copy",
                            select::expr(
                                continue_hash.clone(),
                                absorb_result_next_expr[input_slice].clone(),
                                absorb_data_next_expr[input_slice].clone(),
                            ),
                            s_next[i][j].clone(),
                        );
                        input_slice += 1;
                    } else {
                        cb.require_equal(
                            "absorb state copy",
                            pre_s[i][j].clone() * continue_hash.clone(),
                            s_next[i][j].clone(),
                        );
                    }
                }
            }
            cb.gate(meta.query_fixed(q_absorb, Rotation::cur()))
        });

        // Squeeze
        meta.create_gate("squeeze", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
            let start_new_hash = start_new_hash(meta, Rotation::cur());
            // The words to squeeze
            let hash_words: Vec<_> = pre_s
                .into_iter()
                .take(4)
                .map(|a| a[0].clone())
                .take(4)
                .collect();
            // Verify if we converted the correct words to bytes on previous rows
            for (idx, word) in hash_words.iter().enumerate() {
                cb.condition(start_new_hash.clone(), |cb| {
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
            let hash_bytes_le = hash_bytes.into_iter().rev().collect::<Vec<_>>();
            let rlc = compose_rlc::expr(&hash_bytes_le, challenges.evm_word());
            cb.condition(start_new_hash, |cb| {
                cb.require_equal(
                    "hash rlc check",
                    rlc,
                    meta.query_advice(hash_rlc, Rotation::cur()),
                );
            });
            cb.gate(meta.query_fixed(q_round_last, Rotation::cur()))
        });
        info!("- Post squeeze:");
        info!("Lookups: {}", lookup_counter);
        info!("Columns: {}", cell_values.len());
        total_lookup_counter += lookup_counter;

        // Enforce logic for when this block is the last block for a hash
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

        // Padding
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
            // Now for each padding selector
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
                            // byte then it's 129
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

        // Length and input data rlc
        meta.create_gate("length and data rlc", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);

            let q_padding = meta.query_fixed(q_padding, Rotation::cur());
            let start_new_hash_prev = start_new_hash(meta, Rotation::prev());
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
                    length_prev.clone() * not::expr(start_new_hash_prev.expr())
                        + sum::expr(
                            is_paddings
                                .iter()
                                .map(|is_padding| not::expr(is_padding.expr())),
                        ),
                );

                // Use intermediate cells to keep the degree low
                let mut new_data_rlc =
                    data_rlc_prev.clone() * not::expr(start_new_hash_prev.expr());
                cb.require_equal("initial data rlc", data_rlcs[0].expr(), new_data_rlc);
                new_data_rlc = data_rlcs[0].expr();
                for (idx, (byte, is_padding)) in
                    input_bytes.iter().zip(is_paddings.iter()).enumerate()
                {
                    new_data_rlc = select::expr(
                        is_padding.expr(),
                        new_data_rlc.clone(),
                        new_data_rlc.clone() * challenges.keccak_input() + byte.expr.clone(),
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

        info!("Degree: {}", meta.degree());
        info!("Minimum rows: {}", meta.minimum_rows());
        info!("Lookups: {}", total_lookup_counter);
        info!("Columns: {}", cell_values.len());
        info!("part_size absorb: {}", get_num_bits_per_absorb_lookup());
        info!("part_size theta: {}", get_num_bits_per_theta_c_lookup());
        info!(
            "part_size theta c: {}",
            get_num_bits_per_lookup(THETA_C_LOOKUP_RANGE)
        );
        info!("part_size theta t: {}", get_num_bits_per_lookup(4));
        info!("part_size rho/pi: {}", get_num_bits_per_rho_pi_lookup());
        info!("part_size chi base: {}", get_num_bits_per_base_chi_lookup());
        info!("part_size chi ext: {}", get_num_bits_per_ext_chi_lookup());
        info!(
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
            keccak_table,
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
            pack_table,
            _marker: PhantomData,
        }
    }

    /// Sets the witness using the data to be hashed
    pub fn assign_from_witness(
        &self,
        layouter: &mut impl Layouter<F>,
        inputs: &[Vec<u8>],
        challenges: Challenges<Value<F>>,
        capacity: Option<usize>,
    ) -> Result<(), Error> {
        let witness = multi_keccak(inputs, challenges, capacity)?;
        self.assign(layouter, &witness)
    }

    pub(crate) fn assign(
        &self,
        layouter: &mut impl Layouter<F>,
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
                || Value::known(*value),
            )?;
        }

        // Keccak data
        for (name, column, value) in &[
            ("absorb_from", self.absorb_from, row.absorb_data.from),
            ("absorb_data", self.absorb_data, row.absorb_data.absorb),
            ("absorb_result", self.absorb_result, row.absorb_data.result),
            (
                "squeeze_packed",
                self.squeeze_packed,
                row.squeeze_data.packed,
            ),
        ] {
            region.assign_advice(
                || format!("assign {} {}", name, offset),
                *column,
                offset,
                || Value::known(*value),
            )?;
        }

        self.keccak_table.assign_row(
            region,
            offset,
            [
                Value::known(F::from(row.is_final)),
                row.data_rlc,
                Value::known(F::from(row.length as u64)),
                row.hash_rlc,
            ],
        )?;

        // State words
        for (idx, (word, column)) in row.state.iter().zip(self.state.iter()).enumerate() {
            region.assign_advice(
                || format!("assign state word {} {}", idx, offset),
                *column,
                offset,
                || Value::known(*word),
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
                || Value::known(*bit),
            )?;
        }

        // Round constant
        region.assign_fixed(
            || format!("assign round cst {}", offset),
            self.round_cst,
            offset,
            || Value::known(pack_u64::<F>(ROUND_CST[round])),
        )?;

        Ok(())
    }

    pub(crate) fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        load_normalize_table(layouter, "normalize_6", &self.normalize_6, 6u64)?;
        load_normalize_table(layouter, "normalize_4", &self.normalize_4, 4u64)?;
        load_normalize_table(layouter, "normalize_3", &self.normalize_3, 3u64)?;
        load_lookup_table(
            layouter,
            "chi base",
            &self.chi_base_table,
            get_num_bits_per_base_chi_lookup(),
            &CHI_BASE_LOOKUP_TABLE,
        )?;
        load_lookup_table(
            layouter,
            "chi ext",
            &self.chi_ext_table,
            get_num_bits_per_ext_chi_lookup(),
            &CHI_EXT_LOOKUP_TABLE,
        )?;
        load_pack_table(layouter, &self.pack_table)
    }
}

fn keccak<F: Field>(rows: &mut Vec<KeccakRow<F>>, bytes: &[u8], challenges: Challenges<Value<F>>) {
    let mut bits = into_bits(bytes);
    let mut s = [[F::zero(); 5]; 5];
    let absorb_positions = get_absorb_positions();
    let num_bytes_in_last_block = bytes.len() % RATE;
    let all_threes: F = pack(&[3u8; 64]);
    let all_fives: F = pack(&[5u8; 64]);
    let two = F::from(2u64);

    // Padding
    bits.push(1);
    while (bits.len() + 1) % RATE_IN_BITS != 0 {
        bits.push(0);
    }
    bits.push(1);

    let mut length = 0usize;
    let mut data_rlc = Value::known(F::zero());
    let chunks = bits.chunks(RATE_IN_BITS);
    let num_chunks = chunks.len();
    for (idx, chunk) in chunks.enumerate() {
        let is_final_block = idx == num_chunks - 1;

        // Absorb data
        let mut absorb_rows = Vec::new();
        for (idx, &(i, j)) in absorb_positions.iter().enumerate() {
            let absorb = pack(&chunk[idx * 64..(idx + 1) * 64]);
            let from = s[i][j];
            s[i][j] = field_xor(s[i][j], absorb);
            absorb_rows.push(AbsorbData {
                from,
                absorb,
                result: s[i][j],
            });
        }

        let mut hash_words: Vec<F> = Vec::new();
        for round in 0..NUM_ROUNDS + 1 {
            let mut cell_values = Vec::new();

            let mut absorb_data = AbsorbData::default();
            if round < NUM_WORDS_TO_ABSORB {
                absorb_data = absorb_rows[round].clone();
            }

            let mut state = [F::zero(); KECCAK_WIDTH];
            for i in 0..5 {
                for j in 0..5 {
                    state[i * 5 + j] = s[i][j];
                }
            }

            // Absorb
            let part_size = get_num_bits_per_absorb_lookup();
            let input = absorb_data.from + absorb_data.absorb;
            let absorb_fat = split::value(&mut cell_values, input, 0, part_size, false);
            let _absorb_result =
                transform::value(&mut cell_values, absorb_fat.clone(), true, |v| v & 1);

            // Absorb data in bytes
            let packed = split::value(
                &mut cell_values,
                absorb_data.absorb,
                0,
                NUM_BITS_PER_BYTE,
                false,
            );
            let input_bytes = transform::value(&mut cell_values, packed, false, |v| *v);

            // Padding
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

                cell_values[data_rlcs[0]] = extract_field(data_rlc);
                for (idx, (byte, padding)) in input_bytes.iter().zip(paddings.iter()).enumerate() {
                    if !*padding {
                        let byte_value = Value::known(byte.value);
                        data_rlc = data_rlc * challenges.keccak_input() + byte_value;
                    }
                    if idx < data_rlcs.len() - 1 {
                        cell_values[data_rlcs[idx + 1]] = extract_field(data_rlc);
                    }
                }
            }

            if round != NUM_ROUNDS {
                // Theta
                let part_size_c = get_num_bits_per_theta_c_lookup();
                let part_size_t = get_num_bits_per_theta_t_lookup();
                let mut bc = Vec::new();
                for s in s.iter() {
                    let c = s[0] + s[1] + s[2] + s[3] + s[4];
                    let bc_fat = split::value(&mut cell_values, c, 1, part_size_c, false);
                    let bc_norm =
                        transform::value(&mut cell_values, bc_fat.clone(), true, |v| v & 1);
                    bc.push(bc_norm);
                }
                let mut os = [[F::zero(); 5]; 5];
                for i in 0..5 {
                    let t = decode::value::<F>(bc[(i + 4) % 5].clone())
                        + decode::value::<F>(rotate(bc[(i + 1) % 5].clone(), 1, part_size_c));
                    if get_mode() {
                        for j in 0..5 {
                            os[i][j] = s[i][j] + t;
                        }
                    } else {
                        let t_parts = split::value(&mut cell_values, t, 0, part_size_t, false);
                        let t_norm = decode::value::<F>(transform::value(
                            &mut cell_values,
                            t_parts.clone(),
                            true,
                            |v| v & 1,
                        ));
                        for j in 0..5 {
                            os[i][j] = s[i][j] + t_norm;
                        }
                    }
                }
                s = os;

                // Rho/Pi
                let part_size = get_num_bits_per_base_chi_lookup();
                let mut os = [[F::zero(); 5]; 5];
                let mut os_parts: [[Vec<PartValue<F>>; 5]; 5] =
                    array_init::array_init(|_| array_init::array_init(|_| Vec::new()));
                for i in 0..5 {
                    for j in 0..5 {
                        let s_parts = rotate(
                            split::value(
                                &mut cell_values,
                                s[i][j],
                                RHO_MATRIX[i][j],
                                part_size,
                                true,
                            ),
                            RHO_MATRIX[i][j],
                            part_size,
                        );
                        let s_parts = combine::value::<F>(s_parts.clone(), part_size);
                        let s_parts =
                            transform::value(&mut cell_values, s_parts.clone(), true, |v| v & 1);
                        if get_mode() {
                            os_parts[j][(2 * i + 3 * j) % 5] = s_parts.clone();
                        }
                        os[j][(2 * i + 3 * j) % 5] = decode::value::<F>(s_parts);
                    }
                }
                s = os;

                // Chi
                let part_size_base = get_num_bits_per_base_chi_lookup();
                let part_size_ext = get_num_bits_per_ext_chi_lookup();
                let three_packed = pack::<F>(&vec![3u8; part_size_base]);
                let round_cst_packed = pack_u64::<F>(ROUND_CST[round]);
                let mut os = [[F::zero(); 5]; 5];
                for i in 0..5 {
                    for j in 0..5 {
                        if i == 0 && j == 0 {
                            let next_s = all_fives + s[(i + 2) % 5][j]
                                - two * s[i][j]
                                - s[(i + 1) % 5][j]
                                - two * round_cst_packed;
                            let next_s_parts =
                                split::value(&mut cell_values, next_s, 0, part_size_ext, false);
                            os[i][j] = decode::value::<F>(transform::value(
                                &mut cell_values,
                                next_s_parts.clone(),
                                true,
                                |v| CHI_EXT_LOOKUP_TABLE[*v as usize],
                            ));
                        } else {
                            let s_parts = if get_mode() {
                                let mut s_parts = Vec::new();
                                for ((part_a, part_b), part_c) in os_parts[i][j]
                                    .iter()
                                    .zip(os_parts[(i + 1) % 5][j].iter())
                                    .zip(os_parts[(i + 2) % 5][j].iter())
                                {
                                    let value = three_packed + part_b.value
                                        - two * part_a.value
                                        - part_c.value;
                                    s_parts.push(PartValue {
                                        num_bits: part_size_base,
                                        value,
                                    });
                                }
                                s_parts
                            } else {
                                let input = all_threes + s[(i + 1) % 5][j]
                                    - two * s[i][j]
                                    - s[(i + 2) % 5][j];
                                split::value(&mut cell_values, input, 0, part_size_base, false)
                            };
                            os[i][j] = decode::value::<F>(transform::value(
                                &mut cell_values,
                                s_parts,
                                true,
                                |v| CHI_BASE_LOOKUP_TABLE[*v as usize],
                            ));
                        }
                    }
                }
                s = os;
            }

            // The words to squeeze out
            hash_words = s.into_iter().take(4).map(|a| a[0]).take(4).collect();

            // The rlc of the hash
            let is_final = is_final_block && round == NUM_ROUNDS;
            let hash_rlc = if is_final {
                let hash_bytes_le = s
                    .into_iter()
                    .take(4)
                    .flat_map(|a| to_bytes::value(&unpack(a[0])))
                    .rev()
                    .collect::<Vec<_>>();
                challenges
                    .evm_word()
                    .map(|evm_word| rlc::value(&hash_bytes_le, evm_word))
            } else {
                Value::known(F::zero())
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

        // Squeeze
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
        .map(|a| {
            pack_with_base::<F>(&unpack(a[0]), 2)
                .to_repr()
                .into_iter()
                .take(8)
                .collect::<Vec<_>>()
                .to_vec()
        })
        .take(4)
        .concat();
    debug!("hash: {:x?}", &hash_bytes);
    debug!("data rlc: {:x?}", data_rlc);
}

fn multi_keccak<F: Field>(
    bytes: &[Vec<u8>],
    challenges: Challenges<Value<F>>,
    capacity: Option<usize>,
) -> Result<Vec<KeccakRow<F>>, Error> {
    // Dummy first row so that the initial data is absorbed
    // The initial data doesn't really matter, `is_final` just needs to be disabled.
    let mut rows: Vec<KeccakRow<F>> = vec![KeccakRow {
        q_padding: false,
        q_padding_last: false,
        state: [F::zero(); KECCAK_WIDTH],
        absorb_data: AbsorbData {
            from: F::zero(),
            absorb: F::zero(),
            result: F::zero(),
        },
        squeeze_data: SqueezeData { packed: F::zero() },
        is_final: false,
        length: 0usize,
        data_rlc: Value::known(F::zero()),
        hash_rlc: Value::known(F::zero()),
        cell_values: Vec::new(),
    }];
    // Actual keccaks
    for bytes in bytes {
        keccak(&mut rows, bytes, challenges);
    }
    if let Some(capacity) = capacity {
        // Pad with no data hashes to the expected capacity
        while rows.len() < (1 + capacity * (NUM_ROUNDS + 1)) {
            keccak(&mut rows, &[], challenges);
        }
        // Check that we are not over capacity
        if rows.len() > (1 + capacity * (NUM_ROUNDS + 1)) {
            return Err(Error::BoundsFailure);
        }
    }
    Ok(rows)
}

#[cfg(test)]
mod tests {
    use super::*;
    use halo2_proofs::{dev::MockProver, halo2curves::bn256::Fr};

    fn verify<F: Field>(k: u32, inputs: Vec<Vec<u8>>, success: bool) {
        let circuit = KeccakPackedCircuit::new(2usize.pow(k), inputs.as_slice());
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
