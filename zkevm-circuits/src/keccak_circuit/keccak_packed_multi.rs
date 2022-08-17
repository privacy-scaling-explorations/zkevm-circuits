use crate::evm_circuit::util::{not, rlc};
use crate::{evm_circuit::util::constraint_builder::BaseConstraintBuilder, util::Expr};
use eth_types::Word;
use eth_types::{Field, ToScalar};
use gadgets::util::{select, sum};
use halo2_proofs::arithmetic::FieldExt;
use halo2_proofs::plonk::{Selector, VirtualCells};
use halo2_proofs::{
    circuit::{Layouter, Region, SimpleFloorPlanner},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, TableColumn},
    poly::Rotation,
};
use itertools::Itertools;
use std::{env::var, marker::PhantomData, vec};

const MAX_DEGREE: usize = 3;

const KECCAK_WIDTH: usize = 25;
const NUM_ROUNDS: usize = 24;
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
const RHO_PI_LOOKUP_RANGE: usize = 4;
const CHI_BASE_LOOKUP_RANGE: usize = 5;

const BIT_COUNT: usize = 3;
const BIT_SIZE: usize = 2usize.pow(BIT_COUNT as u32);

// `a ^ ((~b) & c)` is calculated by doing `lookup[3 - 2*a + b - c]`
const CHI_BASE_LOOKUP_TABLE: [u8; 5] = [0, 1, 1, 0, 0];

fn get_degree() -> usize {
    var("DEGREE")
        .unwrap_or_else(|_| "8".to_string())
        .parse()
        .expect("Cannot parse DEGREE env var as usize")
}

fn get_num_rows_per_round() -> usize {
    var("ROWS")
        .unwrap_or_else(|_| "5".to_string())
        .parse()
        .expect("Cannot parse ROWS env var as usize")
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

fn get_num_bits_per_rho_pi_lookup() -> usize {
    get_num_bits_per_lookup(CHI_BASE_LOOKUP_RANGE.max(RHO_PI_LOOKUP_RANGE))
}

fn get_num_bits_per_base_chi_lookup() -> usize {
    get_num_bits_per_lookup(CHI_BASE_LOOKUP_RANGE.max(RHO_PI_LOOKUP_RANGE))
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
    q_enable: bool,
    q_round: bool,
    q_absorb: bool,
    q_round_end: bool,
    q_padding: bool,
    q_padding_last: bool,
    round_cst: F,
    is_final: u64,
    cell_values: Vec<F>,
    length: usize,
    data_rlc: F,
    hash_rlc: F,
}

/// Part
#[derive(Clone, Debug)]
pub(crate) struct Part<F: Field> {
    cell: Cell<F>,
    expr: Expression<F>,
    num_bits: usize,
}

/// Part Value
#[derive(Clone, Copy, Debug)]
pub(crate) struct PartValue {
    value: Word,
    rot: i32,
    num_bits: usize,
}

#[derive(Clone, Debug)]
pub(crate) struct KeccakRegion<F> {
    pub(crate) rows: Vec<Vec<F>>,
}

impl<F: FieldExt> KeccakRegion<F> {
    pub(crate) fn new() -> Self {
        Self { rows: Vec::new() }
    }

    pub(crate) fn assign(&mut self, column: usize, offset: usize, value: F) {
        while offset >= self.rows.len() {
            self.rows.push(Vec::new());
        }
        let row = &mut self.rows[offset];
        while column >= row.len() {
            row.push(F::zero());
        }
        row[column] = value;
    }
}

#[derive(Clone, Debug)]
pub(crate) struct Cell<F> {
    expression: Expression<F>,
    column_expression: Expression<F>,
    column: Option<Column<Advice>>,
    column_idx: usize,
    rotation: i32,
}

impl<F: FieldExt> Cell<F> {
    pub(crate) fn new(
        meta: &mut VirtualCells<F>,
        column: Column<Advice>,
        column_idx: usize,
        rotation: i32,
    ) -> Self {
        Self {
            expression: meta.query_advice(column, Rotation(rotation)),
            column_expression: meta.query_advice(column, Rotation::cur()),
            column: Some(column),
            column_idx,
            rotation,
        }
    }

    pub(crate) fn new_value(column_idx: usize, rotation: i32) -> Self {
        Self {
            expression: 0.expr(),
            column_expression: 0.expr(),
            column: None,
            column_idx,
            rotation,
        }
    }

    pub(crate) fn at_offset(&self, meta: &mut ConstraintSystem<F>, offset: i32) -> Self {
        let mut expression = 0.expr();
        meta.create_gate("Query cell", |meta| {
            expression = meta.query_advice(self.column.unwrap(), Rotation(self.rotation + offset));
            vec![0.expr()]
        });

        Self {
            expression,
            column_expression: self.column_expression.clone(),
            column: self.column,
            column_idx: self.column_idx,
            rotation: self.rotation + offset,
        }
    }

    pub(crate) fn assign(&self, region: &mut KeccakRegion<F>, offset: i32, value: F) {
        region.assign(
            self.column_idx,
            ((offset as i32) + self.rotation) as usize,
            value,
        );
    }
}

impl<F: FieldExt> Expr<F> for Cell<F> {
    fn expr(&self) -> Expression<F> {
        self.expression.clone()
    }
}

impl<F: FieldExt> Expr<F> for &Cell<F> {
    fn expr(&self) -> Expression<F> {
        self.expression.clone()
    }
}

/// CellColumn
#[derive(Clone, Debug)]
pub(crate) struct CellColumn<F> {
    advice: Column<Advice>,
    expr: Expression<F>,
}

/// CellManager
#[derive(Clone, Debug)]
pub(crate) struct CellManager<F> {
    height: usize,
    columns: Vec<CellColumn<F>>,
    rows: Vec<usize>,
    num_unused_cells: usize,
}

impl<F: FieldExt> CellManager<F> {
    pub(crate) fn new(height: usize) -> Self {
        Self {
            height,
            columns: Vec::new(),
            rows: vec![0; height],
            num_unused_cells: 0,
        }
    }

    pub(crate) fn query_cell(&mut self, meta: &mut ConstraintSystem<F>) -> Cell<F> {
        let (row_idx, column_idx) = self.get_position();
        self.query_cell_at_pos(meta, row_idx as i32, column_idx)
    }

    pub(crate) fn query_cell_at_row(
        &mut self,
        meta: &mut ConstraintSystem<F>,
        row_idx: i32,
    ) -> Cell<F> {
        let column_idx = self.rows[row_idx as usize];
        self.rows[row_idx as usize] += 1;
        self.query_cell_at_pos(meta, row_idx, column_idx)
    }

    pub(crate) fn query_cell_at_pos(
        &mut self,
        meta: &mut ConstraintSystem<F>,
        row_idx: i32,
        column_idx: usize,
    ) -> Cell<F> {
        let column = if column_idx < self.columns.len() {
            self.columns[column_idx].advice
        } else {
            let advice = meta.advice_column();
            let mut expr = 0.expr();
            meta.create_gate("Query column", |meta| {
                expr = meta.query_advice(advice, Rotation::cur());
                vec![0.expr()]
            });
            self.columns.push(CellColumn { advice, expr });
            advice
        };

        let mut cells = Vec::new();
        meta.create_gate("Query cell", |meta| {
            cells.push(Cell::new(meta, column, column_idx, row_idx));
            vec![0.expr()]
        });
        cells[0].clone()
    }

    pub(crate) fn query_cell_value(&mut self) -> Cell<F> {
        let (row_idx, column_idx) = self.get_position();
        self.query_cell_value_at_pos(row_idx as i32, column_idx)
    }

    pub(crate) fn query_cell_value_at_row(&mut self, row_idx: i32) -> Cell<F> {
        let column_idx = self.rows[row_idx as usize];
        self.rows[row_idx as usize] += 1;
        self.query_cell_value_at_pos(row_idx, column_idx)
    }

    pub(crate) fn query_cell_value_at_pos(&mut self, row_idx: i32, column_idx: usize) -> Cell<F> {
        Cell::new_value(column_idx, row_idx)
    }

    fn get_position(&mut self) -> (usize, usize) {
        let mut best_row_idx = 0usize;
        let mut best_row_pos = 100000usize;
        for (row_idx, row) in self.rows.iter().enumerate() {
            if *row < best_row_pos {
                best_row_pos = *row;
                best_row_idx = row_idx;
            }
        }
        self.rows[best_row_idx] += 1;
        (best_row_idx, best_row_pos)
    }

    pub(crate) fn get_width(&self) -> usize {
        self.rows.iter().cloned().max().unwrap()
    }

    pub(crate) fn start_region(&mut self) -> usize {
        // Make sure all rows start at the same column
        let width = self.get_width();
        for row in self.rows.iter_mut() {
            self.num_unused_cells += width - *row;
            *row = width;
        }
        width
    }

    pub(crate) fn columns(&self) -> &[CellColumn<F>] {
        &self.columns
    }

    pub(crate) fn get_num_unused_cells(&self) -> usize {
        self.num_unused_cells
    }
}

/// KeccakConfig
#[derive(Clone, Debug)]
pub struct KeccakPackedConfig<F> {
    q_enable: Column<Fixed>,
    q_first: Column<Fixed>,
    q_round: Column<Fixed>,
    q_absorb: Column<Fixed>,
    q_round_end: Selector,
    q_padding: Column<Fixed>,
    q_padding_last: Column<Fixed>,
    is_final: Column<Advice>,
    length: Column<Advice>,
    data_rlc: Column<Advice>,
    hash_rlc: Column<Advice>,
    cell_manager: CellManager<F>,
    round_cst: Column<Fixed>,
    normalize_3: [TableColumn; 2],
    normalize_4: [TableColumn; 2],
    normalize_6: [TableColumn; 2],
    chi_base_table: [TableColumn; 2],
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

#[allow(clippy::too_many_arguments)]
fn split<F: Field>(
    meta: &mut ConstraintSystem<F>,
    cell_manager: &mut CellManager<F>,
    cb: &mut BaseConstraintBuilder<F>,
    input: Expression<F>,
    rot: usize,
    target_part_size: usize,
    normalize: bool,
    row: Option<usize>,
) -> Vec<Part<F>> {
    let mut parts = Vec::new();
    let word = get_word_parts(target_part_size, rot, normalize);
    for word_part in word.parts {
        let cell = if let Some(row) = row {
            cell_manager.query_cell_at_row(meta, row as i32)
        } else {
            cell_manager.query_cell(meta)
        };

        parts.push(Part {
            num_bits: word_part.bits.len(),
            cell: cell.clone(),
            expr: cell.expr(),
        });
    }

    // Input parts need to equal original input expression
    cb.require_equal("split", decode(parts.clone()), input);

    parts
}

fn split_value<F: Field>(
    cell_manager: &mut CellManager<F>,
    region: &mut KeccakRegion<F>,
    input: Word,
    rot: usize,
    target_part_size: usize,
    normalize: bool,
    row: Option<usize>,
) -> Vec<PartValue> {
    let input_bits = unpack(input);
    assert_eq!(pack(&input_bits), input);

    let mut parts = Vec::new();
    let word = get_word_parts(target_part_size, rot, normalize);
    for word_part in word.parts {
        let value = decode_part(&input_bits, &word_part);
        let cell = if let Some(row) = row {
            cell_manager.query_cell_value_at_row(row as i32)
        } else {
            cell_manager.query_cell_value()
        };
        cell.assign(region, 0, F::from(value));
        parts.push(PartValue {
            num_bits: word_part.bits.len(),
            rot: cell.rotation,
            value: Word::from(value),
        });
    }

    assert_eq!(decode_value(parts.clone()), input);
    parts
}

// Split into parts, but storing the parts in the specific way to have the same
// table layout in `output_cells` regardless of rotation.
#[allow(clippy::too_many_arguments)]
fn split_special<F: Field>(
    meta: &mut ConstraintSystem<F>,
    output_cells: &[Cell<F>],
    cell_manager: &mut CellManager<F>,
    cb: &mut BaseConstraintBuilder<F>,
    input: Expression<F>,
    rot: usize,
    target_part_size: usize,
    normalize: bool,
) -> Vec<Part<F>> {
    let mut input_parts = Vec::new();
    let mut output_parts = Vec::new();
    let word = get_word_parts(target_part_size, rot, normalize);

    let word = rotate_parts(word.parts, rot, target_part_size);

    let target_sizes = target_part_sizes(target_part_size);
    let mut word_iter = word.iter();
    let mut counter = 0;
    while let Some(word_part) = word_iter.next() {
        if word_part.bits.len() == target_sizes[counter] {
            // Input and output part are the same
            let part = Part {
                num_bits: target_sizes[counter],
                cell: output_cells[counter].clone(),
                expr: output_cells[counter].expr(),
            };
            input_parts.push(part.clone());
            output_parts.push(part);
            counter += 1;
        } else if let Some(extra_part) = word_iter.next() {
            // The two parts combined need to have the expected combined length
            assert_eq!(
                word_part.bits.len() + extra_part.bits.len(),
                target_sizes[counter]
            );

            // Needs two cells here to store the parts
            let part_a = cell_manager.query_cell(meta);
            let part_b = cell_manager.query_cell(meta);

            // Make sure the parts combined equal the value in the uniform output
            let factor = F::from(BIT_SIZE as u64).pow(&[word_part.bits.len() as u64, 0, 0, 0]);
            let expr = part_a.expr() + part_b.expr() * factor;
            cb.require_equal("rot part", expr, output_cells[counter].expr());

            // Input needs the two parts because it needs to be able to undo the rotation
            input_parts.push(Part {
                num_bits: word_part.bits.len(),
                cell: part_a.clone(),
                expr: part_a.expr(),
            });
            input_parts.push(Part {
                num_bits: extra_part.bits.len(),
                cell: part_b.clone(),
                expr: part_b.expr(),
            });

            // Output only has the combined cell
            output_parts.push(Part {
                num_bits: target_sizes[counter],
                cell: output_cells[counter].clone(),
                expr: output_cells[counter].expr(),
            });

            counter += 1;
        } else {
            unreachable!();
        }
    }

    let input_parts = r_rotate(input_parts, rot, target_part_size);

    // Input parts need to equal original input expression
    cb.require_equal("split", decode(input_parts), input);

    // Uniform output
    output_parts
}

fn split_special_value<F: Field>(
    output_cells: &[Cell<F>],
    cell_manager: &mut CellManager<F>,
    region: &mut KeccakRegion<F>,
    input: Word,
    rot: usize,
    target_part_size: usize,
    normalize: bool,
) -> Vec<PartValue> {
    let input_bits = unpack(input);
    assert_eq!(pack(&input_bits), input);

    let mut input_parts = Vec::new();
    let mut output_parts = Vec::new();
    let word = get_word_parts(target_part_size, rot, normalize);

    let word = rotate_parts(word.parts, rot, target_part_size);

    let target_sizes = target_part_sizes(target_part_size);
    let mut word_iter = word.iter();
    let mut counter = 0;
    while let Some(word_part) = word_iter.next() {
        if word_part.bits.len() == target_sizes[counter] {
            let value = decode_part(&input_bits, word_part);
            output_cells[counter].assign(region, 0, F::from(value));
            input_parts.push(PartValue {
                num_bits: word_part.bits.len(),
                rot: output_cells[counter].rotation,
                value: Word::from(value),
            });
            output_parts.push(PartValue {
                num_bits: word_part.bits.len(),
                rot: output_cells[counter].rotation,
                value: Word::from(value),
            });
            counter += 1;
        } else if let Some(extra_part) = word_iter.next() {
            assert_eq!(
                word_part.bits.len() + extra_part.bits.len(),
                target_sizes[counter]
            );

            let part_a = cell_manager.query_cell_value();
            let part_b = cell_manager.query_cell_value();

            let value_a = decode_part(&input_bits, word_part);
            let value_b = decode_part(&input_bits, extra_part);

            part_a.assign(region, 0, F::from(value_a));
            part_b.assign(region, 0, F::from(value_b));

            let factor = (BIT_SIZE as u64).pow(word_part.bits.len() as u32);
            let value = value_a + value_b * factor;

            output_cells[counter].assign(region, 0, F::from(value));

            input_parts.push(PartValue {
                num_bits: word_part.bits.len(),
                value: Word::from(value_a),
                rot: part_a.rotation,
            });

            input_parts.push(PartValue {
                num_bits: extra_part.bits.len(),
                value: Word::from(value_b),
                rot: part_b.rotation,
            });

            output_parts.push(PartValue {
                num_bits: target_sizes[counter],
                value: Word::from(value),
                rot: output_cells[counter].rotation,
            });

            counter += 1;
        } else {
            unreachable!();
        }
    }

    let input_parts = r_rotate_value(input_parts, rot, target_part_size);

    assert_eq!(decode_value(input_parts), input);

    output_parts
}

fn decode_part(input_bits: &[u8], part: &PartInfo) -> u64 {
    let mut value = 0u64;
    let mut factor = 1u64;
    for idx in 0..part.bits.len() {
        let bit_pos = part.bits[idx];
        assert!(input_bits[bit_pos] < BIT_SIZE as u8);
        value += (input_bits[bit_pos] as u64) * factor;
        factor *= BIT_SIZE as u64;
    }
    value
}

fn get_rotate_count(count: usize, part_size: usize) -> usize {
    (count + part_size - 1) / part_size
}

fn rotate<F: Field>(parts: Vec<Part<F>>, count: usize, part_size: usize) -> Vec<Part<F>> {
    let mut rotated_parts = parts;
    rotated_parts.rotate_right(get_rotate_count(count, part_size));
    rotated_parts
}

fn r_rotate<F: Field>(parts: Vec<Part<F>>, count: usize, part_size: usize) -> Vec<Part<F>> {
    let mut rotated_parts = parts;
    rotated_parts.rotate_left(get_rotate_count(count, part_size));
    rotated_parts
}

fn rotate_parts(parts: Vec<PartInfo>, count: usize, part_size: usize) -> Vec<PartInfo> {
    let mut rotated_parts = parts;
    rotated_parts.rotate_right(get_rotate_count(count, part_size));
    rotated_parts
}

fn rotate_value(parts: Vec<PartValue>, count: usize, part_size: usize) -> Vec<PartValue> {
    let mut rotated_parts = parts;
    rotated_parts.rotate_right(get_rotate_count(count, part_size));
    rotated_parts
}

fn r_rotate_value(parts: Vec<PartValue>, count: usize, part_size: usize) -> Vec<PartValue> {
    let mut rotated_parts = parts;
    rotated_parts.rotate_left(get_rotate_count(count, part_size));
    rotated_parts
}

fn transform<F: Field>(
    name: &'static str,
    meta: &mut ConstraintSystem<F>,
    cell_manager: &mut CellManager<F>,
    lookup_counter: &mut usize,
    input: Vec<Part<F>>,
    transform_table: [TableColumn; 2],
    uniform_lookup: bool,
) -> Vec<Part<F>> {
    let mut cells = Vec::new();
    for input_part in input.iter() {
        cells.push(if uniform_lookup {
            cell_manager.query_cell_at_row(meta, input_part.cell.rotation)
        } else {
            cell_manager.query_cell(meta)
        });
    }
    transform_to_cells(
        name,
        meta,
        &cells,
        lookup_counter,
        input,
        transform_table,
        uniform_lookup,
    )
}

fn transform_value<F: Field>(
    cell_manager: &mut CellManager<F>,
    region: &mut KeccakRegion<F>,
    input: Vec<PartValue>,
    do_packing: bool,
    f: fn(&u8) -> u8,
    uniform_lookup: bool,
) -> Vec<PartValue> {
    let mut cells = Vec::new();
    for input_part in input.iter() {
        cells.push(if uniform_lookup {
            cell_manager.query_cell_value_at_row(input_part.rot)
        } else {
            cell_manager.query_cell_value()
        });
    }
    transform_to_cells_value(&cells, region, input, do_packing, f)
}

fn transform_to_cells<F: Field>(
    name: &'static str,
    meta: &mut ConstraintSystem<F>,
    cells: &[Cell<F>],
    lookup_counter: &mut usize,
    input: Vec<Part<F>>,
    transform_table: [TableColumn; 2],
    uniform_lookup: bool,
) -> Vec<Part<F>> {
    let mut output = Vec::new();
    for (idx, input_part) in input.iter().enumerate() {
        let output_part = cells[idx].clone();

        if !uniform_lookup || input_part.cell.rotation == 0 {
            meta.lookup(name, |_| {
                vec![
                    (input_part.expr.clone(), transform_table[0]),
                    (output_part.expr(), transform_table[1]),
                ]
            });
            *lookup_counter += 1;
        }

        output.push(Part {
            num_bits: input_part.num_bits,
            cell: output_part.clone(),
            expr: output_part.expr(),
        });
    }
    output
}

fn transform_to_cells_value<F: Field>(
    cells: &[Cell<F>],
    region: &mut KeccakRegion<F>,
    input: Vec<PartValue>,
    do_packing: bool,
    f: fn(&u8) -> u8,
) -> Vec<PartValue> {
    let mut output = Vec::new();
    for (idx, input_part) in input.iter().enumerate() {
        let input_bits = &unpack(input_part.value)[0..input_part.num_bits];
        let output_bits = input_bits.iter().map(f).collect::<Vec<_>>();

        let value = if do_packing {
            pack(&output_bits)
        } else {
            Word::from(to_bytes(&output_bits)[0])
        };

        let output_part = cells[idx].clone();
        output_part.assign(region, 0, value.to_scalar().unwrap());

        output.push(PartValue {
            num_bits: input_part.num_bits,
            rot: output_part.rotation,
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

/// WordParts
#[derive(Clone, Debug)]
pub(crate) struct WordParts {
    parts: Vec<PartInfo>,
}

fn get_word_parts(part_size: usize, rot: usize, normalize: bool) -> WordParts {
    let mut bits = (0usize..64).collect::<Vec<_>>();
    bits.rotate_right(rot);

    let mut parts = Vec::new();
    let mut rot_idx = 0;

    let mut idx = 0;
    let target_sizes = if normalize {
        // After the rotation we want the parts of all the words to be at the same
        // positions
        target_part_sizes(part_size)
    } else {
        // Here we only care about minimizing the number of parts
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
    // Split into parts bit by bit
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

    WordParts { parts }
}

impl<F: Field> KeccakPackedConfig<F> {
    pub(crate) fn configure(meta: &mut ConstraintSystem<F>, r: F) -> Self {
        let q_enable = meta.fixed_column();
        let q_first = meta.fixed_column();
        let q_round = meta.fixed_column();
        let q_absorb = meta.fixed_column();
        let q_round_end = meta.selector();
        let q_padding = meta.fixed_column();
        let q_padding_last = meta.fixed_column();
        let is_final = meta.advice_column();
        let round_cst = meta.fixed_column();
        let length = meta.advice_column();
        let data_rlc = meta.advice_column();
        let hash_rlc = meta.advice_column();
        let normalize_3 = array_init::array_init(|_| meta.lookup_table_column());
        let normalize_4 = array_init::array_init(|_| meta.lookup_table_column());
        let normalize_6 = array_init::array_init(|_| meta.lookup_table_column());
        let chi_base_table = array_init::array_init(|_| meta.lookup_table_column());
        let pack_unpack_table = array_init::array_init(|_| meta.lookup_table_column());

        // Round constant
        let mut round_cst_expr = 0.expr();
        meta.create_gate("Query round cst", |meta| {
            round_cst_expr = meta.query_fixed(round_cst, Rotation::cur());
            vec![0u64.expr()]
        });

        let mut cell_manager = CellManager::new(get_num_rows_per_round());

        let mut b = vec![vec![0u64.expr(); 5]; 5];
        let mut b_next = vec![vec![0u64.expr(); 5]; 5];

        // Main state cells
        for i in 0..5 {
            for j in 0..5 {
                let cell = cell_manager.query_cell(meta);
                b[i][j] = cell.expr();
                b_next[i][j] = cell.at_offset(meta, get_num_rows_per_round() as i32).expr();
            }
        }

        // Absorb cells
        let absorb_from = cell_manager.query_cell(meta);
        let absorb_data = cell_manager.query_cell(meta);
        let absorb_result = cell_manager.query_cell(meta);
        let mut absorb_from_next = vec![0u64.expr(); NUM_WORDS_TO_ABSORB];
        let mut absorb_data_next = vec![0u64.expr(); NUM_WORDS_TO_ABSORB];
        let mut absorb_result_next = vec![0u64.expr(); NUM_WORDS_TO_ABSORB];
        for i in 0..NUM_WORDS_TO_ABSORB {
            let rot = ((i + 1) * get_num_rows_per_round()) as i32;
            absorb_from_next[i] = absorb_from.at_offset(meta, rot).expr();
            absorb_data_next[i] = absorb_data.at_offset(meta, rot).expr();
            absorb_result_next[i] = absorb_result.at_offset(meta, rot).expr();
        }

        let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
        let mut total_lookup_counter = 0;

        let pre_b = b.clone();

        // Absorb
        // The absorption happening at the start of the 24 rounds is done spread out
        // over those 24 rounds. In a single round (in 17 of the 24 rounds) a
        // single word is absorbed so the work is spread out. The absorption is
        // done simply by doing state + data and then normalizing the result to [0,1].
        cell_manager.start_region();
        let mut lookup_counter = 0;
        let part_size = get_num_bits_per_absorb_lookup();
        let input = absorb_from.expr() + absorb_data.expr();
        let absorb_fat = split(
            meta,
            &mut cell_manager,
            &mut cb,
            input,
            0,
            part_size,
            false,
            None,
        );
        cell_manager.start_region();
        let absorb_res = transform(
            "absorb",
            meta,
            &mut cell_manager,
            &mut lookup_counter,
            absorb_fat,
            normalize_3,
            true,
        );
        cb.require_equal("absorb result", decode(absorb_res), absorb_result.expr());
        println!("- Post absorb:");
        println!("Lookups: {}", lookup_counter);
        println!("Columns: {}", cell_manager.get_width());
        total_lookup_counter += lookup_counter;

        // Padding
        cell_manager.start_region();
        let mut lookup_counter = 0;
        // Unpack a single word into bytes (for the absorption)
        // Potential optimization: could potentially do multiple bytes per lookup
        let packed = split(
            meta,
            &mut cell_manager,
            &mut cb,
            absorb_data.expr(),
            0,
            8,
            false,
            None,
        );
        cell_manager.start_region();
        let input_bytes = transform(
            "squeeze unpack",
            meta,
            &mut cell_manager,
            &mut lookup_counter,
            packed,
            pack_unpack_table
                .into_iter()
                .rev()
                .collect::<Vec<_>>()
                .try_into()
                .unwrap(),
            true,
        );
        cell_manager.start_region();
        let mut is_paddings = Vec::new();
        let mut data_rlcs = Vec::new();
        for _ in input_bytes.iter() {
            is_paddings.push(cell_manager.query_cell(meta));
            data_rlcs.push(cell_manager.query_cell(meta));
        }
        println!("- Post padding:");
        println!("Lookups: {}", lookup_counter);
        println!("Columns: {}", cell_manager.get_width());
        total_lookup_counter += lookup_counter;

        // Theta
        // We calculate `bc[i] = normalize(b[i][0] + b[i][1] + b[i][2] + b[i][3] +
        // b[i][4])`. This is done by splitting the bc values in parts a way
        // that allows us to also calculate the rotated value "for free":
        //`bc[(i + 4) % 5] + rot(bc[(i + 1)% 5], 1)`
        cell_manager.start_region();
        let mut lookup_counter = 0;
        let part_size_c = get_num_bits_per_theta_c_lookup();
        let mut bcf = Vec::new();
        for b in b.iter() {
            let c = b[0].clone() + b[1].clone() + b[2].clone() + b[3].clone() + b[4].clone();
            let bc_fat = split(
                meta,
                &mut cell_manager,
                &mut cb,
                c,
                1,
                part_size_c,
                false,
                None,
            );
            bcf.push(bc_fat);
        }
        cell_manager.start_region();
        let mut bc = Vec::new();
        for bc_fat in bcf {
            let bc_thin = transform(
                "theta c",
                meta,
                &mut cell_manager,
                &mut lookup_counter,
                bc_fat.clone(),
                normalize_6,
                true,
            );
            bc.push(bc_thin);
        }

        // Now do `bc[(i + 4) % 5] + rot(bc[(i + 1) % 5], 1)` using just expressions.
        // We don't normalize the result here. We do it as part of the rho/pi step, even
        // though we would only have to normalize 5 values instead of 25, because of the
        // way the rho/pi and chi steps can be combined it's more efficient to
        // do it there (the max value for chi is 4 already so that's the
        // limiting factor).
        let mut ob = vec![vec![0u64.expr(); 5]; 5];
        for i in 0..5 {
            let t = decode(bc[(i + 4) % 5].clone())
                + decode(rotate(bc[(i + 1) % 5].clone(), 1, part_size_c));
            for j in 0..5 {
                ob[i][j] = b[i][j].clone() + t.clone();
            }
        }
        b = ob.clone();
        println!("- Post theta:");
        println!("Lookups: {}", lookup_counter);
        println!("Columns: {}", cell_manager.get_width());
        total_lookup_counter += lookup_counter;

        // Rho/Pi
        // For the rotation of rho/pi we split up the words like expected, but in a way
        // that allows reusing the same parts in an optimal way for the chi step.
        // We can save quite a few columns by not recombining the parts after rho/pi and
        // re-splitting the words again before chi. Instead we do chi directly
        // on the output parts of rho/pi. For rho/pi specically we do
        // `normalize(b[i][j] + bc[(i + 4) % 5] + rot(bc[(i + 1) % 5], 1))`.
        cell_manager.start_region();
        let mut lookup_counter = 0;
        let part_size = get_num_bits_per_base_chi_lookup();

        // To combine the rho/pi/chi steps we have to ensure a specific layout so
        // query those cells here first.
        // For chi we have to do `b[i][j] ^ ((~b[(i+1)%5][j]) & b[(i+2)%5][j])`. `j`
        // remains static but `i` is accessed in a wrap around manner. To do this using
        // multiple rows with lookups in a way that doesn't require any
        // extra additional cells or selectors we have to put all `b[i]`'s on the same
        // row. This isn't that strong of a requirement actually because we the
        // words are split into multipe parts, and so only the parts at the same
        // position of those words need to be on the same row.
        let target_word_sizes = target_part_sizes(part_size);
        let num_word_parts = target_word_sizes.len();
        let mut rho_pi_chi_cells: [[[Vec<Cell<F>>; 5]; 5]; 3] = array_init::array_init(|_| {
            array_init::array_init(|_| array_init::array_init(|_| Vec::new()))
        });
        let mut num_columns = 0;
        let mut column_starts = [0usize; 3];
        for p in 0..3 {
            column_starts[p] = cell_manager.start_region();
            let mut row_idx = 0;
            num_columns = 0;
            for j in 0..5 {
                for _ in 0..num_word_parts {
                    for i in 0..5 {
                        rho_pi_chi_cells[p][i][j]
                            .push(cell_manager.query_cell_at_row(meta, row_idx));
                    }
                    if row_idx == 0 {
                        num_columns += 1;
                    }
                    row_idx = (((row_idx as usize) + 1) % get_num_rows_per_round()) as i32;
                }
            }
        }

        // Do the transformation, resulting in the word parts also being normalized.
        let pi_region_start = cell_manager.start_region();
        let mut ob_parts = vec![vec![Vec::new(); 5]; 5];
        for (j, ob_part) in ob_parts.iter_mut().enumerate() {
            for i in 0..5 {
                let b_fat = split_special(
                    meta,
                    &rho_pi_chi_cells[0][j][(2 * i + 3 * j) % 5],
                    &mut cell_manager,
                    &mut cb,
                    b[i][j].clone(),
                    RHOM[i][j],
                    part_size,
                    true,
                );

                let b_thin = transform_to_cells(
                    "rho/pi",
                    meta,
                    &rho_pi_chi_cells[1][j][(2 * i + 3 * j) % 5],
                    &mut lookup_counter,
                    b_fat.clone(),
                    normalize_4,
                    true,
                );

                ob_part[(2 * i + 3 * j) % 5] = b_thin.clone();
            }
        }
        let pi_region_end = cell_manager.start_region();

        // Pi parts range checks
        // To make the uniform stuff work we had to combine some parts together
        // in a new cell. Here we make sure those parts are range checked.
        // Potential improvement: Could combine multiple smaller parts in a single
        // lookup but doesn't save that much.
        for c in pi_region_start..pi_region_end {
            meta.lookup("pi part range check", |_| {
                vec![(cell_manager.columns()[c].expr.clone(), normalize_4[0])]
            });
            lookup_counter += 1;
        }

        println!("- Post rho/pi:");
        println!("Lookups: {}", lookup_counter);
        println!("Columns: {}", cell_manager.get_width());
        total_lookup_counter += lookup_counter;

        // Chi
        // In groups of 5 columns, we have to do `b[i][j] ^ ((~b[(i+1)%5][j]) &
        // b[(i+2)%5][j])` five times, on each row (no selector needed).
        let mut lookup_counter = 0;
        let part_size_base = get_num_bits_per_base_chi_lookup();
        for idx in 0..num_columns {
            let mut input: [Expression<F>; 5] = array_init::array_init(|_| 0.expr());
            let mut output: [Expression<F>; 5] = array_init::array_init(|_| 0.expr());
            for c in 0..5 {
                input[c] = cell_manager.columns()[column_starts[1] + idx * 5 + c]
                    .expr
                    .clone();
                output[c] = cell_manager.columns()[column_starts[2] + idx * 5 + c]
                    .expr
                    .clone();
            }
            for i in 0..5 {
                let input = pack_bit(3, part_size_base) - 2.expr() * input[i].clone()
                    + input[(i + 1) % 5].clone()
                    - input[(i + 2) % 5].clone().clone();
                let output = output[i].clone();

                meta.lookup("chi base", |_| {
                    vec![
                        (input.clone(), chi_base_table[0]),
                        (output.clone(), chi_base_table[1]),
                    ]
                });
                lookup_counter += 1;
            }
        }
        // Now just decode the parts after the chi transformation done with the lookups
        // above.
        let mut ob = vec![vec![0u64.expr(); 5]; 5];
        for (i, ob) in ob.iter_mut().enumerate() {
            for (j, ob) in ob.iter_mut().enumerate() {
                let mut thin = Vec::new();
                for idx in 0..num_word_parts {
                    thin.push(Part {
                        num_bits: part_size_base,
                        cell: rho_pi_chi_cells[2][i][j][idx].clone(),
                        expr: rho_pi_chi_cells[2][i][j][idx].expr(),
                    });
                }
                *ob = decode(thin);
            }
        }
        b = ob.clone();

        // iota
        // Simply do the single xor on state [0][0].
        cell_manager.start_region();
        let part_size = get_num_bits_per_absorb_lookup();
        let input = b[0][0].clone() + round_cst_expr.clone();
        let iota_fat = split(
            meta,
            &mut cell_manager,
            &mut cb,
            input,
            0,
            part_size,
            false,
            None,
        );
        cell_manager.start_region();
        // Could share columns with absorb which may end up using 1 lookup/column
        // fewer...
        b[0][0] = decode(transform(
            "iota",
            meta,
            &mut cell_manager,
            &mut lookup_counter,
            iota_fat,
            normalize_3,
            true,
        ));

        // Final results stored in the next row
        for i in 0..5 {
            for j in 0..5 {
                cb.require_equal("next row check", b[i][j].clone(), b_next[i][j].clone());
            }
        }

        println!("- Post chi:");
        println!("Lookups: {}", lookup_counter);
        println!("Columns: {}", cell_manager.get_width());
        total_lookup_counter += lookup_counter;

        let mut lookup_counter = 0;
        cell_manager.start_region();

        // Squeeze cells
        let squeeze_from = cell_manager.query_cell(meta);
        let mut squeeze_from_prev = vec![0u64.expr(); NUM_WORDS_TO_SQUEEZE];
        for (idx, squeeze_from_prev) in squeeze_from_prev.iter_mut().enumerate() {
            let rot = (-(idx as i32) - 1) * get_num_rows_per_round() as i32;
            *squeeze_from_prev = squeeze_from.at_offset(meta, rot).expr();
        }

        cell_manager.start_region();
        // Unpack a single word into bytes (for the squeeze)
        // Potential optimization: could potentially do multiple bytes per lookup
        let packed = split(
            meta,
            &mut cell_manager,
            &mut cb,
            squeeze_from.expr(),
            0,
            8,
            false,
            None,
        );
        cell_manager.start_region();
        let squeeze_bytes = transform(
            "squeeze unpack",
            meta,
            &mut cell_manager,
            &mut lookup_counter,
            packed,
            pack_unpack_table
                .into_iter()
                .rev()
                .collect::<Vec<_>>()
                .try_into()
                .unwrap(),
            true,
        );

        println!("- Post squeeze:");
        println!("Lookups: {}", lookup_counter);
        println!("Columns: {}", cell_manager.get_width());
        total_lookup_counter += lookup_counter;

        meta.create_gate("round", |meta| {
            cb.gate(meta.query_fixed(q_round, Rotation::cur()))
        });

        meta.create_gate("absorb", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);

            b = pre_b.clone();
            let is_not_final = not::expr(meta.query_advice(is_final, Rotation::cur()));

            let absorb_positions = get_absorb_positions();
            let mut a_slice = 0;
            for j in 0..5 {
                for i in 0..5 {
                    if absorb_positions.contains(&(i, j)) {
                        cb.condition(is_not_final.clone(), |cb| {
                            cb.require_equal(
                                "absorb verify input",
                                absorb_from_next[a_slice].clone(),
                                b[i][j].clone(),
                            );
                        });
                        cb.require_equal(
                            "absorb result copy",
                            select::expr(
                                is_not_final.clone(),
                                absorb_result_next[a_slice].clone(),
                                absorb_data_next[a_slice].clone(),
                            ),
                            b_next[i][j].clone(),
                        );
                        a_slice += 1;
                    } else {
                        cb.require_equal(
                            "absorb state copy",
                            b[i][j].clone() * is_not_final.clone(),
                            b_next[i][j].clone(),
                        );
                    }
                }
            }

            cb.gate(meta.query_fixed(q_absorb, Rotation::cur()))
        });

        // Collect the bytes that are spread out over previous rows
        let mut hash_bytes = Vec::new();
        for i in 0..NUM_WORDS_TO_SQUEEZE {
            for byte in squeeze_bytes.iter() {
                let rot = (-(i as i32) - 1) * get_num_rows_per_round() as i32;
                hash_bytes.push(byte.cell.at_offset(meta, rot).expr());
            }
        }

        meta.create_gate("squeeze", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);

            let is_final = meta.query_advice(is_final, Rotation::cur());

            // The words to squeeze
            let hash_words: Vec<_> = pre_b
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

        let last_is_padding_in_block = is_paddings.last().unwrap().at_offset(
            meta,
            -(((NUM_ROUNDS + 1 - NUM_WORDS_TO_ABSORB) * get_num_rows_per_round()) as i32),
        );
        meta.create_gate("is final", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);
            cb.require_equal(
                "is_final needs to be the same as the last is_padding in the block",
                meta.query_advice(is_final, Rotation::cur()),
                last_is_padding_in_block.expr(),
            );
            cb.gate(
                meta.query_fixed(q_absorb, Rotation::cur())
                    * not::expr(meta.query_fixed(q_first, Rotation::cur())),
            )
        });

        // May be cleaner to do this padding logic in the byte conversion lookup but
        // currently easier to do it like this.
        let prev_is_padding = is_paddings
            .last()
            .unwrap()
            .at_offset(meta, -(get_num_rows_per_round() as i32));
        meta.create_gate("padding", |meta| {
            let mut cb = BaseConstraintBuilder::new(MAX_DEGREE);

            let q_padding = meta.query_fixed(q_padding, Rotation::cur());
            let q_padding_last = meta.query_fixed(q_padding_last, Rotation::cur());

            // All padding selectors need to be boolean
            for is_padding in is_paddings.iter() {
                cb.condition(meta.query_fixed(q_enable, Rotation::cur()), |cb| {
                    cb.require_boolean("is_padding boolean", is_padding.expr());
                });
            }

            // This last padding selector will be used on the first round row
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
                    // These can be combined in the future, but currently would increase the degree
                    // by one Padding start/intermediate byte
                    cb.condition(
                        (q_padding.expr() - q_padding_last.expr()) * is_paddings[idx].expr(),
                        |cb| {
                            cb.require_equal(
                                "padding start/intermediate byte last byte",
                                input_bytes[idx].expr.clone(),
                                is_first_padding.expr(),
                            );
                        },
                    );
                    // Padding start/end byte
                    cb.condition(q_padding_last.expr() * is_paddings[idx].expr(), |cb| {
                        cb.require_equal(
                            "padding start/end byte",
                            input_bytes[idx].expr.clone(),
                            is_first_padding.expr() + 128.expr(),
                        );
                    });
                } else {
                    // Padding start/intermediate byte
                    cb.condition(q_padding.expr() * is_paddings[idx].expr(), |cb| {
                        cb.require_equal(
                            "padding start/intermediate byte",
                            input_bytes[idx].expr.clone(),
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
            let is_final_prev =
                meta.query_advice(is_final, Rotation(-(get_num_rows_per_round() as i32)));
            let length_prev =
                meta.query_advice(length, Rotation(-(get_num_rows_per_round() as i32)));
            let length = meta.query_advice(length, Rotation::cur());
            let data_rlc_prev =
                meta.query_advice(data_rlc, Rotation(-(get_num_rows_per_round() as i32)));
            let data_rlc = meta.query_advice(data_rlc, Rotation::cur());

            // Update the length/data_rlc on rows where we absorb data
            cb.condition(q_padding.expr(), |cb| {
                // Length increases by the number of bytes that aren't padding
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
                (meta.query_fixed(q_enable, Rotation::cur())
                    - meta.query_fixed(q_first, Rotation::cur()))
                    * not::expr(q_padding),
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
        println!("Total Lookups: {}", total_lookup_counter);
        println!("Total Columns: {}", cell_manager.get_width());
        println!("num unused cells: {}", cell_manager.get_num_unused_cells());
        println!("part_size absorb: {}", get_num_bits_per_absorb_lookup());
        println!("part_size theta: {}", get_num_bits_per_theta_c_lookup());
        println!(
            "part_size theta c: {}",
            get_num_bits_per_lookup(THETA_C_LOOKUP_RANGE)
        );
        println!("part_size theta t: {}", get_num_bits_per_lookup(4));
        println!("part_size rho/pi: {}", get_num_bits_per_rho_pi_lookup());
        println!("part_size chi base: {}", get_num_bits_per_base_chi_lookup());
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
            q_padding,
            q_padding_last,
            is_final,
            length,
            data_rlc,
            hash_rlc,
            cell_manager,
            round_cst,
            normalize_3,
            normalize_4,
            normalize_6,
            chi_base_table,
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
        // q_enable
        region.assign_fixed(
            || format!("assign q_enable {}", offset),
            self.q_enable,
            offset,
            || Ok(F::from(row.q_enable)),
        )?;
        // q_first
        region.assign_fixed(
            || format!("assign q_first {}", offset),
            self.q_first,
            offset,
            || Ok(F::from((offset == 0) as u64)),
        )?;
        // q_round
        region.assign_fixed(
            || format!("assign q_round {}", offset),
            self.q_round,
            offset,
            || Ok(F::from(row.q_round)),
        )?;
        // q_absorb
        region.assign_fixed(
            || format!("assign q_absorb {}", offset),
            self.q_absorb,
            offset,
            || Ok(F::from(row.q_absorb)),
        )?;
        // q_round_end
        if row.q_round_end {
            self.q_round_end.enable(region, offset)?;
        }
        // q_padding
        region.assign_fixed(
            || format!("assign q_padding {}", offset),
            self.q_padding,
            offset,
            || Ok(F::from(row.q_padding as u64)),
        )?;
        // q_padding_last
        region.assign_fixed(
            || format!("assign q_padding_last {}", offset),
            self.q_padding_last,
            offset,
            || Ok(F::from(row.q_padding_last as u64)),
        )?;
        // is_final
        region.assign_advice(
            || format!("assign is_final {}", offset),
            self.is_final,
            offset,
            || Ok(F::from(row.is_final)),
        )?;
        // length
        region.assign_advice(
            || format!("assign length {}", offset),
            self.length,
            offset,
            || Ok(F::from(row.length as u64)),
        )?;
        // data_rlc
        region.assign_advice(
            || format!("assign data_rlc {}", offset),
            self.data_rlc,
            offset,
            || Ok(row.data_rlc),
        )?;
        // hash_rlc
        region.assign_advice(
            || format!("assign hash_rlc {}", offset),
            self.hash_rlc,
            offset,
            || Ok(row.hash_rlc),
        )?;

        // Cell values
        for (idx, (bit, column)) in row
            .cell_values
            .iter()
            .zip(self.cell_manager.columns())
            .enumerate()
        {
            region.assign_advice(
                || format!("assign lookup value {} {}", idx, offset),
                column.advice,
                offset,
                || Ok(*bit),
            )?;
        }

        // Round constant
        region.assign_fixed(
            || format!("assign round cst {}", offset),
            self.round_cst,
            offset,
            || Ok(row.round_cst),
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
    let data_rlc_target = rlc::value(&bytes.clone().into_iter().rev().collect::<Vec<_>>(), r);
    println!("data_rlc_target: {:x?}", data_rlc_target);

    let mut bits = to_bits(&bytes);
    let rate: usize = 136 * 8;

    let mut b = [[Word::zero(); 5]; 5];

    let absorb_positions = get_absorb_positions();

    let num_bytes_in_last_block = bytes.len() % (rate / 8);

    // Padding
    bits.push(1);
    while (bits.len() + 1) % rate != 0 {
        bits.push(0);
    }
    bits.push(1);

    let mut length = 0usize;
    let mut data_rlc = F::zero();
    let chunks = bits.chunks(rate);
    let num_chunks = chunks.len();
    for (idx, chunk) in chunks.enumerate() {
        let is_final_block = idx == num_chunks - 1;

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

        let mut cell_managers = Vec::new();
        let mut regions = Vec::new();

        let mut round_lengths = Vec::new();
        let mut round_data_rlcs = Vec::new();
        let mut hash_rlc = F::zero();
        for round in 0..25 {
            let mut cell_manager = CellManager::new(get_num_rows_per_round());
            let mut region = KeccakRegion::new();

            let mut absorb_row = AbsorbData::default();
            if round < rate / 64 {
                absorb_row = absorb_rows[round].clone();
            }

            // State cells
            for b in &b {
                for b in b {
                    let cell = cell_manager.query_cell_value();
                    cell.assign(&mut region, 0, b.to_scalar().unwrap());
                }
            }

            // Absorb cells
            let absorb_from = cell_manager.query_cell_value();
            let absorb_data = cell_manager.query_cell_value();
            let absorb_result = cell_manager.query_cell_value();
            absorb_from.assign(&mut region, 0, absorb_row.from.to_scalar().unwrap());
            absorb_data.assign(&mut region, 0, absorb_row.absorb.to_scalar().unwrap());
            absorb_result.assign(&mut region, 0, absorb_row.result.to_scalar().unwrap());

            cell_manager.start_region();

            // Absorb
            let part_size = get_num_bits_per_absorb_lookup();
            let input = absorb_row.from + absorb_row.absorb;
            let absorb_fat = split_value::<F>(
                &mut cell_manager,
                &mut region,
                input,
                0,
                part_size,
                false,
                None,
            );
            cell_manager.start_region();
            let _absorb_result = transform_value(
                &mut cell_manager,
                &mut region,
                absorb_fat.clone(),
                true,
                |v| v & 1,
                true,
            );

            // Padding
            cell_manager.start_region();
            // Unpack a single word into bytes (for the absorption)
            // Potential optimization: could potentially do multiple bytes per lookup
            let packed = split_value::<F>(
                &mut cell_manager,
                &mut region,
                absorb_row.absorb,
                0,
                8,
                false,
                None,
            );
            cell_manager.start_region();
            let input_bytes =
                transform_value(&mut cell_manager, &mut region, packed, false, |v| *v, true);
            cell_manager.start_region();
            let mut is_paddings = Vec::new();
            let mut data_rlcs = Vec::new();
            for _ in input_bytes.iter() {
                is_paddings.push(cell_manager.query_cell_value());
                data_rlcs.push(cell_manager.query_cell_value());
            }

            /*if round < NUM_WORDS_TO_ABSORB {
                for byte in input_bytes.iter() {
                    println!("{} - byte: {}", round, byte.value.as_u32())
                }
            }*/

            let mut paddings = Vec::new();
            for (padding_idx, is_padding) in is_paddings.iter_mut().enumerate() {
                let padding = if is_final_block && round < NUM_WORDS_TO_ABSORB {
                    let byte_idx = round * 8 + padding_idx;
                    if byte_idx < num_bytes_in_last_block {
                        length += 1;
                        false
                    } else {
                        true
                    }
                } else {
                    if round < NUM_WORDS_TO_ABSORB {
                        length += 1;
                    }
                    false
                };
                //println!("padding {}-{}: {}", idx, round, padding);
                paddings.push(padding);
                is_padding.assign(&mut region, 0, if padding { F::one() } else { F::zero() });
            }

            cell_manager.start_region();

            let is_final = is_final_block && round == 24;

            // The words to squeeze out
            hash_words = b.into_iter().take(4).map(|a| a[0]).take(4).collect();

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
            //println!("length: {}", length);
            round_lengths.push(length);

            if round < NUM_WORDS_TO_ABSORB {
                data_rlcs[0].assign(&mut region, 0, data_rlc);
                for (idx, (byte, padding)) in input_bytes.iter().zip(paddings.iter()).enumerate() {
                    if !*padding {
                        let byte_value: F = byte.value.to_scalar().unwrap();
                        data_rlc = data_rlc * r + byte_value;
                    }
                    if idx < data_rlcs.len() - 1 {
                        data_rlcs[idx + 1].assign(&mut region, 0, data_rlc);
                    }
                }
            }

            round_data_rlcs.push(data_rlc);

            if round != 24 {
                // Theta
                let part_size = get_num_bits_per_theta_c_lookup();
                let mut bcf = Vec::new();
                for b in &b {
                    let c = b[0] + b[1] + b[2] + b[3] + b[4];
                    let bc_fat = split_value::<F>(
                        &mut cell_manager,
                        &mut region,
                        c,
                        1,
                        part_size,
                        false,
                        None,
                    );
                    bcf.push(bc_fat);
                }

                cell_manager.start_region();

                let mut bc = Vec::new();
                for bc_fat in bcf {
                    let bc_thin = transform_value(
                        &mut cell_manager,
                        &mut region,
                        bc_fat.clone(),
                        true,
                        |v| v & 1,
                        true,
                    );
                    bc.push(bc_thin);
                }

                cell_manager.start_region();

                let mut ob = [[Word::zero(); 5]; 5];
                for i in 0..5 {
                    let t = decode_value(bc[(i + 4) % 5].clone())
                        + decode_value(rotate_value(bc[(i + 1) % 5].clone(), 1, part_size));
                    for j in 0..5 {
                        ob[i][j] = b[i][j] + t;
                    }
                }
                b = ob;

                cell_manager.start_region();

                // Rho/Pi
                let part_size = get_num_bits_per_base_chi_lookup();
                let target_word_sizes = target_part_sizes(part_size);
                let num_word_parts = target_word_sizes.len();
                let mut rho_pi_chi_cells: [[[Vec<Cell<F>>; 5]; 5]; 3] =
                    array_init::array_init(|_| {
                        array_init::array_init(|_| array_init::array_init(|_| Vec::new()))
                    });
                let mut column_starts = [0usize; 3];
                for p in 0..3 {
                    column_starts[p] = cell_manager.start_region();
                    let mut row_idx = 0;
                    for j in 0..5 {
                        for _ in 0..num_word_parts {
                            for i in 0..5 {
                                rho_pi_chi_cells[p][i][j]
                                    .push(cell_manager.query_cell_value_at_row(row_idx as i32));
                            }
                            row_idx = (row_idx + 1) % get_num_rows_per_round();
                        }
                    }
                }

                cell_manager.start_region();

                let mut ob_parts: [[Vec<PartValue>; 5]; 5] =
                    array_init::array_init(|_| array_init::array_init(|_| Vec::new()));
                for (j, ob_part) in ob_parts.iter_mut().enumerate() {
                    for i in 0..5 {
                        let b_fat = split_special_value(
                            &rho_pi_chi_cells[0][j][(2 * i + 3 * j) % 5],
                            &mut cell_manager,
                            &mut region,
                            b[i][j],
                            RHOM[i][j],
                            part_size,
                            true,
                        );

                        let b_thin = transform_to_cells_value(
                            &rho_pi_chi_cells[1][j][(2 * i + 3 * j) % 5],
                            &mut region,
                            b_fat.clone(),
                            true,
                            |v| v & 1,
                        );
                        ob_part[(2 * i + 3 * j) % 5] = b_thin.clone();
                    }
                }

                cell_manager.start_region();

                // Chi
                let part_size_base = get_num_bits_per_base_chi_lookup();
                let mut ob = [[Word::zero(); 5]; 5];
                for j in 0..5 {
                    for i in 0..5 {
                        let mut fat = Vec::new();
                        for ((part_a, part_b), part_c) in ob_parts[i][j]
                            .iter()
                            .zip(ob_parts[(i + 1) % 5][j].iter())
                            .zip(ob_parts[(i + 2) % 5][j].iter())
                        {
                            let value = pack(&vec![3u8; part_size_base])
                                - Word::from(2u64) * part_a.value
                                + part_b.value
                                - part_c.value;
                            fat.push(PartValue {
                                num_bits: part_size_base,
                                rot: j as i32,
                                value,
                            });
                        }
                        ob[i][j] = decode_value(transform_to_cells_value(
                            &rho_pi_chi_cells[2][i][j],
                            &mut region,
                            fat.clone(),
                            true,
                            |v| CHI_BASE_LOOKUP_TABLE[*v as usize],
                        ));
                    }
                }
                b = ob;

                cell_manager.start_region();

                // iota
                let part_size = get_num_bits_per_absorb_lookup();
                let input = b[0][0] + pack_u64(if round < 24 { ROUND_CST[round] } else { 0 });
                let iota_fat = split_value::<F>(
                    &mut cell_manager,
                    &mut region,
                    input,
                    0,
                    part_size,
                    false,
                    None,
                );
                cell_manager.start_region();
                b[0][0] = decode_value(transform_value(
                    &mut cell_manager,
                    &mut region,
                    iota_fat.clone(),
                    true,
                    |v| v & 1,
                    true,
                ));
            }

            cell_managers.push(cell_manager);
            regions.push(region);
        }

        // Now that we know the state at the end of the rounds, set the squeeze data
        let num_rounds = cell_managers.len();
        for (idx, word) in hash_words.iter().enumerate() {
            let cell_manager = &mut cell_managers[num_rounds - 2 - idx];
            let region = &mut regions[num_rounds - 2 - idx];

            cell_manager.start_region();
            let squeeze_packed = cell_manager.query_cell_value();
            squeeze_packed.assign(region, 0, word.to_scalar().unwrap());

            cell_manager.start_region();
            let packed = split_value::<F>(cell_manager, region, *word, 0, 8, false, None);
            cell_manager.start_region();
            transform_value(cell_manager, region, packed, false, |v| *v, true);
        }

        if is_final_block {
            println!("data_rlc: {:x?}", round_data_rlcs[24]);
        }

        for round in 0..25 {
            let is_final = is_final_block && round == 24;
            let round_cst = if round < 24 {
                pack_u64(ROUND_CST[round]).to_scalar().unwrap()
            } else {
                F::zero()
            };

            for row_idx in 0..get_num_rows_per_round() {
                rows.push(KeccakRow {
                    q_enable: row_idx == 0,
                    q_round: row_idx == 0 && round < 24,
                    q_absorb: row_idx == 0 && round == 24,
                    q_round_end: row_idx == 0 && round == 24,
                    q_padding: row_idx == 0 && round < NUM_WORDS_TO_ABSORB,
                    q_padding_last: row_idx == 0 && round == NUM_WORDS_TO_ABSORB - 1,
                    round_cst,
                    is_final: is_final as u64,
                    length: round_lengths[round],
                    data_rlc: round_data_rlcs[round],
                    hash_rlc,
                    cell_values: regions[round].rows[row_idx].clone(),
                });
            }
        }
    }

    let hash_bytes = b
        .into_iter()
        .take(4)
        .map(|a| from_bits(&unpack(a[0])).as_u64().to_le_bytes())
        .collect::<Vec<_>>();
    println!("Hash: {:x?}", &(hash_bytes[0..4].concat()));
}

fn multi_keccak<F: Field>(bytes: Vec<Vec<u8>>, r: F) -> Vec<KeccakRow<F>> {
    let mut rows: Vec<KeccakRow<F>> = Vec::new();
    // Dummy first row so that the initial data is absorbed
    // The initial data doesn't really matter, `is_final` just needs to be enabled.
    for idx in 0..get_num_rows_per_round() {
        rows.push(KeccakRow {
            q_enable: idx == 0,
            q_round: false,
            q_absorb: idx == 0,
            q_round_end: false,
            q_padding: false,
            q_padding_last: false,
            round_cst: F::zero(),
            is_final: 1u64,
            length: 0usize,
            data_rlc: F::zero(),
            hash_rlc: F::zero(),
            cell_values: Vec::new(),
        });
    }
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
    fn packed_multi_keccak_simple() {
        let k = 10;
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
