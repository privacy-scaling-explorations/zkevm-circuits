use crate::arith_helpers::{convert_b13_coef, convert_b9_coef, f_from_radix_be, B13, B2, B9};
use crate::common::LANE_SIZE;
use crate::gate_helpers::{biguint_to_f, f_to_biguint};
use crate::permutation::rho_helpers::{get_overflow_detector, BASE_NUM_OF_CHUNKS};
use eth_types::Field;
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, Table},
    plonk::{Advice, Column, ConstraintSystem, Error, Selector, TableColumn},
    poly::Rotation,
};
use itertools::Itertools;
use std::collections::HashMap;
use std::convert::TryInto;
use std::marker::PhantomData;
use strum_macros::{Display, EnumIter};

use super::rho_helpers::{Conversion, STEP2_RANGE, STEP3_RANGE};

const MAX_CHUNKS: usize = 64;
pub const NUM_OF_BINARY_CHUNKS_PER_SLICE: usize = 16;
pub const NUM_OF_BINARY_SLICES: usize = 4;
pub const NUM_OF_B9_CHUNKS_PER_SLICE: usize = 5;
/// is ceil(`MAX_CHUNKS`/ `NUM_OF_B9_CHUNKS_PER_SLICE`) = 13
pub const NUM_OF_B9_SLICES: usize = 13;

#[derive(Debug, Clone)]
struct ThreeColumnsLookup<F> {
    q_enable: Selector,
    pub(crate) col0: (Column<Advice>, TableColumn),
    pub(crate) col1: (Column<Advice>, TableColumn),
    pub(crate) col2: (Column<Advice>, TableColumn),
    _marker: PhantomData<F>,
}
impl<F: Field> ThreeColumnsLookup<F> {
    pub(crate) fn configure(
        meta: &mut ConstraintSystem<F>,
        adv_cols: [Column<Advice>; 3],
        table_cols: [TableColumn; 3],
        name: &'static str,
    ) -> Self {
        let col0 = (adv_cols[0], table_cols[0]);
        let col1 = (adv_cols[1], table_cols[1]);
        let col2 = (adv_cols[2], table_cols[2]);
        let q_enable = meta.complex_selector();
        meta.lookup(name, |meta| {
            let q_enable = meta.query_selector(q_enable);
            let col0_adv = meta.query_advice(col0.0, Rotation::cur());
            let col1_adv = meta.query_advice(col1.0, Rotation::cur());
            let col2_adv = meta.query_advice(col2.0, Rotation::cur());

            vec![
                (q_enable.clone() * col0_adv, col0.1),
                (q_enable.clone() * col1_adv, col1.1),
                (q_enable * col2_adv, col2.1),
            ]
        });
        Self {
            q_enable,
            col0,
            col1,
            col2,
            _marker: PhantomData,
        }
    }
}

#[derive(EnumIter, Display, Clone, Copy)]
enum TableTags {
    Range12 = 0,
    Range169,
    SpecialChunk,
    BooleanFlag,
}

#[derive(Debug, Clone)]
pub struct StackableTable<F> {
    lookup_config: ThreeColumnsLookup<F>,
    special_chunks_map: HashMap<[u8; 32], F>,
}

impl<F: Field> StackableTable<F> {
    /// We use col0 for tag that restricts the lookup into certain rows
    /// we use col1 and col2 for different purposes depend on the tag
    pub(crate) fn configure(
        meta: &mut ConstraintSystem<F>,
        adv_cols: [Column<Advice>; 3],
        table_cols: [TableColumn; 3],
    ) -> Self {
        let lookup_config =
            ThreeColumnsLookup::configure(meta, adv_cols, table_cols, "stackable lookup");
        let special_chunks_map = HashMap::new();
        Self {
            lookup_config,
            special_chunks_map,
        }
    }

    fn load_range(
        &self,
        table: &mut Table<F>,
        offset: usize,
        tag: TableTags,
        k: u64,
    ) -> Result<usize, Error> {
        let mut offset = offset;
        for i in 0..=k {
            table.assign_cell(
                || format!("tag range{}", tag),
                self.lookup_config.col0.1,
                offset,
                || Ok(F::from(tag as u64)),
            )?;
            table.assign_cell(
                || format!("range{}", tag),
                self.lookup_config.col1.1,
                offset,
                || Ok(F::from(i)),
            )?;
            table.assign_cell(
                || format!("dummy col range{}", tag),
                self.lookup_config.col2.1,
                offset,
                || Ok(F::zero()),
            )?;
            offset += 1;
        }
        Ok(offset)
    }
    /// The table describes all possible combinations of these two variables:
    /// - The last input accumulator: `high_value`*(13**64) + `low_value`, and
    /// - The last output coef: `convert_b13_coef(high_value + low_value)`
    fn load_special_chunks(&mut self, table: &mut Table<F>, offset: usize) -> Result<usize, Error> {
        let mut offset = offset;
        for i in 0..B13 {
            for j in 0..(B13 - i) {
                let (low, high) = (i, j);
                let last_chunk = F::from(low as u64)
                    + F::from(high as u64) * F::from(B13 as u64).pow(&[LANE_SIZE as u64, 0, 0, 0]);
                let output_coef = F::from(convert_b13_coef(low + high) as u64);
                self.special_chunks_map
                    .insert(last_chunk.to_repr(), output_coef);
                table.assign_cell(
                    || "tag special chunks",
                    self.lookup_config.col0.1,
                    offset,
                    || Ok(F::from(TableTags::SpecialChunk as u64)),
                )?;
                table.assign_cell(
                    || "last chunk",
                    self.lookup_config.col1.1,
                    offset,
                    || Ok(last_chunk),
                )?;
                table.assign_cell(
                    || "output coef",
                    self.lookup_config.col2.1,
                    offset,
                    || Ok(output_coef),
                )?;
                offset += 1;
            }
        }
        Ok(offset)
    }

    fn load_boolean_flag(&self, table: &mut Table<F>, offset: usize) -> Result<usize, Error> {
        let mut offset = offset;
        for (left, right) in [(true, false), (false, true)] {
            table.assign_cell(
                || "tag boolean flag",
                self.lookup_config.col0.1,
                offset,
                || Ok(F::from(TableTags::BooleanFlag as u64)),
            )?;
            table.assign_cell(
                || "left",
                self.lookup_config.col1.1,
                offset,
                || Ok(F::from(left)),
            )?;
            table.assign_cell(
                || "right",
                self.lookup_config.col2.1,
                offset,
                || Ok(F::from(right)),
            )?;
            offset += 1;
        }
        Ok(offset)
    }
    pub(crate) fn load(&mut self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(
            || "stackable",
            |mut table| {
                let mut offset = 0;
                for &(tag, k) in [
                    (TableTags::Range12, STEP2_RANGE),
                    (TableTags::Range169, STEP3_RANGE),
                ]
                .iter()
                {
                    offset = self.load_range(&mut table, offset, tag, k)?;
                }
                offset = self.load_special_chunks(&mut table, offset)?;
                self.load_boolean_flag(&mut table, offset)?;
                Ok(())
            },
        )
    }

    fn lookup_range(
        &self,
        layouter: &mut impl Layouter<F>,
        values: &[AssignedCell<F, F>],
        tag: TableTags,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || format!("lookup for {}", tag),
            |mut region| {
                let tag = F::from(tag as u64);
                for (offset, v) in values.iter().enumerate() {
                    self.lookup_config.q_enable.enable(&mut region, offset)?;
                    region.assign_advice_from_constant(
                        || "tag",
                        self.lookup_config.col0.0,
                        offset,
                        tag,
                    )?;
                    v.copy_advice(|| "value", &mut region, self.lookup_config.col1.0, offset)?;
                    region.assign_advice_from_constant(
                        || "dummy",
                        self.lookup_config.col2.0,
                        offset,
                        F::zero(),
                    )?;
                }
                Ok(())
            },
        )
    }
    pub(crate) fn lookup_range_12(
        &self,
        layouter: &mut impl Layouter<F>,
        values: &[AssignedCell<F, F>],
    ) -> Result<(), Error> {
        self.lookup_range(layouter, values, TableTags::Range12)
    }
    pub(crate) fn lookup_range_169(
        &self,
        layouter: &mut impl Layouter<F>,
        values: &[AssignedCell<F, F>],
    ) -> Result<(), Error> {
        self.lookup_range(layouter, values, TableTags::Range169)
    }

    pub(crate) fn lookup_special_chunks(
        &self,
        layouter: &mut impl Layouter<F>,
        last_chunk: &AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "lookup for special chunks",
            |mut region| {
                let offset = 0;
                let tag = F::from(TableTags::SpecialChunk as u64);
                self.lookup_config.q_enable.enable(&mut region, offset)?;
                region.assign_advice_from_constant(
                    || "tag",
                    self.lookup_config.col0.0,
                    offset,
                    tag,
                )?;
                last_chunk.copy_advice(
                    || "last chunk",
                    &mut region,
                    self.lookup_config.col1.0,
                    offset,
                )?;
                region.assign_advice(
                    || "output coef",
                    self.lookup_config.col2.0,
                    offset,
                    || {
                        last_chunk
                            .value()
                            .and_then(|&v| self.special_chunks_map.get(&v.to_repr()))
                            .map(|v| v.to_owned())
                            .ok_or(Error::Synthesis)
                    },
                )
            },
        )
    }
    /// Output two boolean cells. Prover can choose to enable one and disable
    /// another, but not both.
    pub(crate) fn assign_boolean_flag(
        &self,
        layouter: &mut impl Layouter<F>,
        is_left: Option<bool>,
    ) -> Result<(AssignedCell<F, F>, AssignedCell<F, F>), Error> {
        layouter.assign_region(
            || "lookup for boolean flag",
            |mut region| {
                let offset = 0;
                self.lookup_config.q_enable.enable(&mut region, offset)?;
                region.assign_advice_from_constant(
                    || "tag",
                    self.lookup_config.col0.0,
                    offset,
                    F::from(TableTags::BooleanFlag as u64),
                )?;
                let left = region.assign_advice(
                    || "left",
                    self.lookup_config.col1.0,
                    offset,
                    || is_left.map(|flag| F::from(flag)).ok_or(Error::Synthesis),
                )?;
                let right = region.assign_advice(
                    || "right",
                    self.lookup_config.col2.0,
                    offset,
                    || is_left.map(|flag| F::from(!flag)).ok_or(Error::Synthesis),
                )?;
                Ok((left, right))
            },
        )
    }
}

#[derive(Debug, Clone)]
pub struct RangeCheckConfig<F, const K: u64> {
    pub range: TableColumn,
    _marker: PhantomData<F>,
}

impl<F: Field, const K: u64> RangeCheckConfig<F, K> {
    pub(crate) fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(
            || "range",
            |mut table| {
                for i in 0..=K {
                    table.assign_cell(|| "range", self.range, i as usize, || Ok(F::from(i)))?;
                }
                Ok(())
            },
        )
    }
    // dead_code reason: WordBuilderConfig is using it. We defer the decision to
    // remove this after WordBuilderConfig is complete
    #[allow(dead_code)]
    pub(crate) fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            range: meta.lookup_table_column(),
            _marker: PhantomData,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Base13toBase9TableConfig<F> {
    lookup_config: ThreeColumnsLookup<F>,
    // mapping from base13 input to base9 output and overflow detector
    map: HashMap<[u8; 32], (F, F)>,
}

impl<F: Field> Base13toBase9TableConfig<F> {
    pub(crate) fn load(&mut self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(
            || "13 -> 9",
            |mut table| {
                // Iterate over all possible 13-ary values of size 4
                for (i, b13_chunks) in (0..BASE_NUM_OF_CHUNKS)
                    .map(|_| 0..B13)
                    .multi_cartesian_product()
                    .enumerate()
                {
                    let input_b13 = f_from_radix_be::<F>(&b13_chunks, B13);
                    let output_b9 = f_from_radix_be::<F>(
                        &b13_chunks
                            .iter()
                            .map(|&x| convert_b13_coef(x))
                            .collect_vec(),
                        B9,
                    );
                    let overflow_detector = F::from(get_overflow_detector(
                        b13_chunks.clone().try_into().unwrap(),
                    ) as u64);

                    self.map
                        .insert(input_b13.to_repr(), (output_b9, overflow_detector));
                    table.assign_cell(
                        || "base 13",
                        self.lookup_config.col0.1,
                        i,
                        || Ok(input_b13),
                    )?;

                    table.assign_cell(
                        || "base 9",
                        self.lookup_config.col1.1,
                        i,
                        || Ok(output_b9),
                    )?;
                    table.assign_cell(
                        || "overflow_detector",
                        self.lookup_config.col2.1,
                        i,
                        || Ok(overflow_detector),
                    )?;
                }
                Ok(())
            },
        )
    }

    /// We use col0 for base 13 input
    /// we use col1 for base 9 output
    /// we use col2 for overflow detector
    pub(crate) fn configure(
        meta: &mut ConstraintSystem<F>,
        adv_cols: [Column<Advice>; 3],
        table_cols: [TableColumn; 3],
    ) -> Self {
        let lookup_config =
            ThreeColumnsLookup::configure(meta, adv_cols, table_cols, "from base 13");
        let map = HashMap::new();
        Self { lookup_config, map }
    }
    pub(crate) fn assign_region(
        &self,
        layouter: &mut impl Layouter<F>,
        slices: &[(u32, u32)],
        conversions: &[Conversion],
    ) -> Result<
        (
            Vec<AssignedCell<F, F>>,
            Vec<AssignedCell<F, F>>,
            Vec<AssignedCell<F, F>>,
            Vec<AssignedCell<F, F>>,
        ),
        Error,
    > {
        layouter.assign_region(
            || "conversion lookup",
            |mut region| {
                let mut input_coefs: Vec<AssignedCell<F, F>> = vec![];
                let mut output_coefs: Vec<AssignedCell<F, F>> = vec![];
                let mut step2_od: Vec<AssignedCell<F, F>> = vec![];
                let mut step3_od: Vec<AssignedCell<F, F>> = vec![];
                for (offset, (&(_, step), conv)) in
                    slices.iter().zip(conversions.iter()).enumerate()
                {
                    self.lookup_config.q_enable.enable(&mut region, offset)?;
                    let input = biguint_to_f::<F>(&conv.input.coef);
                    let outputs = self.map.get(&input.to_repr());
                    let input_coef = region.assign_advice(
                        || "Input Coef",
                        self.lookup_config.col0.0,
                        offset,
                        || Ok(input),
                    )?;
                    input_coefs.push(input_coef);

                    let output_coef = region.assign_advice(
                        || "Output Coef",
                        self.lookup_config.col1.0,
                        offset,
                        || outputs.map(|o| o.0).ok_or(Error::Synthesis),
                    )?;
                    output_coefs.push(output_coef);

                    let od = region.assign_advice(
                        || "Overflow detector",
                        self.lookup_config.col2.0,
                        offset,
                        || outputs.map(|o| o.1).ok_or(Error::Synthesis),
                    )?;
                    match step {
                        1 => region.constrain_constant(od.cell(), F::zero())?,
                        2 => step2_od.push(od),
                        3 => step3_od.push(od),
                        4 => { // Do nothing
                        }
                        _ => unreachable!(),
                    }
                }
                Ok((input_coefs, output_coefs, step2_od, step3_od))
            },
        )
    }
}

fn compute_input_coefs<F: Field, const SLICES: usize>(
    input: Option<&F>,
    base: u8,
    num_chunks: usize,
) -> [Option<F>; SLICES] {
    input.map_or([None; SLICES], |&input| {
        // big-endian
        let input_chunks: Vec<u8> = {
            let raw = f_to_biguint(input);
            let mut v = raw.to_radix_le(base.into());
            debug_assert!(v.len() <= MAX_CHUNKS);
            // fill 0 to max chunks
            v.resize(MAX_CHUNKS, 0);
            // v is big-endian now
            v.reverse();
            v
        };
        // Use rchunks + rev so that the remainder chunks stay at the big-endian
        // side
        let input_coefs = input_chunks
            .rchunks(num_chunks)
            .rev()
            .map(|chunks| Some(f_from_radix_be(chunks, base)))
            .collect_vec();
        input_coefs.try_into().unwrap()
    })
}

#[derive(Debug, Clone)]
pub struct FromBase9TableConfig<F> {
    lookup_config: ThreeColumnsLookup<F>,
    // mapping from base9 input to base13 and base2 output
    map: HashMap<[u8; 32], (F, F)>,
}

impl<F: Field> FromBase9TableConfig<F> {
    pub fn load(&mut self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(
            || "9 -> (2 and 13)",
            |mut table| {
                // Iterate over all possible base 9 values of size 5
                for (i, b9_chunks) in (0..NUM_OF_B9_CHUNKS_PER_SLICE)
                    .map(|_| 0..B9)
                    .multi_cartesian_product()
                    .enumerate()
                {
                    let input_b9 = f_from_radix_be::<F>(&b9_chunks, B9);
                    let converted_chunks: Vec<u8> =
                        b9_chunks.iter().map(|&x| convert_b9_coef(x)).collect_vec();
                    let output_b13 = f_from_radix_be::<F>(&converted_chunks, B13);
                    let output_b2 = f_from_radix_be::<F>(&converted_chunks, B2);
                    self.map.insert(input_b9.to_repr(), (output_b13, output_b2));
                    table.assign_cell(
                        || "base 9",
                        self.lookup_config.col0.1,
                        i,
                        || Ok(input_b9),
                    )?;

                    table.assign_cell(
                        || "base 13",
                        self.lookup_config.col1.1,
                        i,
                        || Ok(output_b13),
                    )?;
                    table.assign_cell(
                        || "base 2",
                        self.lookup_config.col2.1,
                        i,
                        || Ok(output_b2),
                    )?;
                }
                Ok(())
            },
        )
    }

    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        adv_cols: [Column<Advice>; 3],
        table_cols: [TableColumn; 3],
    ) -> Self {
        let lookup_config = ThreeColumnsLookup::configure(meta, adv_cols, table_cols, "from base9");
        let map = HashMap::new();
        Self { lookup_config, map }
    }
    pub fn assign_region(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &AssignedCell<F, F>,
    ) -> Result<
        (
            Vec<AssignedCell<F, F>>,
            Vec<AssignedCell<F, F>>,
            Vec<AssignedCell<F, F>>,
        ),
        Error,
    > {
        let input_coefs = compute_input_coefs::<F, NUM_OF_B9_SLICES>(
            input.value(),
            B9,
            NUM_OF_B9_CHUNKS_PER_SLICE,
        );
        layouter.assign_region(
            || "base 9",
            |mut region| {
                let mut input_cells = vec![];
                let mut output_b13_cells = vec![];
                let mut output_b2_cells = vec![];
                for (offset, input_coef) in input_coefs.iter().enumerate() {
                    self.lookup_config.q_enable.enable(&mut region, offset)?;
                    let input = region.assign_advice(
                        || "base 9",
                        self.lookup_config.col0.0,
                        offset,
                        || input_coef.ok_or(Error::Synthesis),
                    )?;
                    input_cells.push(input.clone());
                    let output = input_coef.and_then(|v| self.map.get(&v.to_repr()));

                    let output_b13 = region.assign_advice(
                        || "base 13",
                        self.lookup_config.col1.0,
                        offset,
                        || output.map(|v| v.0).ok_or(Error::Synthesis),
                    )?;
                    output_b13_cells.push(output_b13);
                    let output_b2 = region.assign_advice(
                        || "base 2",
                        self.lookup_config.col2.0,
                        offset,
                        || output.map(|v| v.1).ok_or(Error::Synthesis),
                    )?;
                    output_b2_cells.push(output_b2);
                }
                Ok((input_cells, output_b13_cells, output_b2_cells))
            },
        )
    }
}

#[derive(Debug, Clone)]
pub struct FromBinaryTableConfig<F> {
    lookup_config: ThreeColumnsLookup<F>,
    // mapping from base9 input to base13 and base2 output
    map: HashMap<[u8; 32], (F, F)>,
}

impl<F: Field> FromBinaryTableConfig<F> {
    pub fn load(&mut self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(
            || "2 -> (9 and 13)",
            |mut table| {
                for (i, b2_chunks) in (0..NUM_OF_BINARY_CHUNKS_PER_SLICE)
                    .map(|_| 0..B2)
                    .multi_cartesian_product()
                    .enumerate()
                {
                    let input_b2 = f_from_radix_be::<F>(&b2_chunks, B2);
                    let output_b9 = f_from_radix_be::<F>(&b2_chunks, B9);
                    let output_b13 = f_from_radix_be::<F>(&b2_chunks, B13);

                    self.map.insert(input_b2.to_repr(), (output_b9, output_b13));
                    // Iterate over all possible binary values of size 16

                    table.assign_cell(
                        || "base 2",
                        self.lookup_config.col0.1,
                        i,
                        || Ok(input_b2),
                    )?;

                    table.assign_cell(
                        || "base 9",
                        self.lookup_config.col1.1,
                        i,
                        || Ok(output_b9),
                    )?;
                    table.assign_cell(
                        || "base 13",
                        self.lookup_config.col2.1,
                        i,
                        || Ok(output_b13),
                    )?;
                }
                Ok(())
            },
        )
    }

    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        adv_cols: [Column<Advice>; 3],
        table_cols: [TableColumn; 3],
    ) -> Self {
        let lookup_config = ThreeColumnsLookup::configure(meta, adv_cols, table_cols, "from base9");
        let map = HashMap::new();
        Self { lookup_config, map }
    }
    pub fn assign_region(
        &self,
        layouter: &mut impl Layouter<F>,
        input: &AssignedCell<F, F>,
    ) -> Result<
        (
            Vec<AssignedCell<F, F>>,
            Vec<AssignedCell<F, F>>,
            Vec<AssignedCell<F, F>>,
        ),
        Error,
    > {
        let input_coefs = compute_input_coefs::<F, NUM_OF_BINARY_SLICES>(
            input.value(),
            B2,
            NUM_OF_BINARY_CHUNKS_PER_SLICE,
        );
        layouter.assign_region(
            || "base 2",
            |mut region| {
                let mut input_cells = vec![];
                let mut output_b9_cells = vec![];
                let mut output_b13_cells = vec![];
                for (offset, input_coef) in input_coefs.iter().enumerate() {
                    self.lookup_config.q_enable.enable(&mut region, offset)?;
                    let input = region.assign_advice(
                        || "base 2",
                        self.lookup_config.col0.0,
                        offset,
                        || input_coef.ok_or(Error::Synthesis),
                    )?;
                    input_cells.push(input.clone());

                    let output = input_coef.and_then(|v| self.map.get(&v.to_repr()));

                    let output_b9 = region.assign_advice(
                        || "base 9",
                        self.lookup_config.col1.0,
                        offset,
                        || output.map(|v| v.0).ok_or(Error::Synthesis),
                    )?;
                    output_b9_cells.push(output_b9);
                    let output_b13 = region.assign_advice(
                        || "base 13",
                        self.lookup_config.col2.0,
                        offset,
                        || output.map(|v| v.1).ok_or(Error::Synthesis),
                    )?;
                    output_b13_cells.push(output_b13);
                }
                Ok((input_cells, output_b9_cells, output_b13_cells))
            },
        )
    }
}
