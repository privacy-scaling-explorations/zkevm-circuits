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
use strum_macros::{Display, EnumIter};

use super::rho_helpers::{Conversion, STEP2_RANGE, STEP3_RANGE};

const MAX_CHUNKS: usize = 64;
pub const NUM_OF_BINARY_CHUNKS_PER_SLICE: usize = 16;
pub const NUM_OF_BINARY_SLICES: usize = 4;
pub const NUM_OF_B9_CHUNKS_PER_SLICE: usize = 5;
/// is ceil(`MAX_CHUNKS`/ `NUM_OF_B9_CHUNKS_PER_SLICE`) = 13
pub const NUM_OF_B9_SLICES: usize = 13;

#[derive(EnumIter, Display, Clone, Copy)]
enum TableTags {
    Range12 = 0,
    Range169,
    SpecialChunk,
    BooleanFlag,
    FromBase13,
    FromBase9,
    FromBase2,
}

#[derive(Debug, Clone)]
pub struct LookupConfig<F> {
    q_enable: Selector,
    pub(crate) cols: [(Column<Advice>, TableColumn); 4],
    special_chunks_map: HashMap<[u8; 32], F>,
    /// mapping from base13 input to base9 output and overflow detector
    base13_map: HashMap<[u8; 32], (F, F)>,
    /// mapping from base9 input to base13 and base2 output
    base9_map: HashMap<[u8; 32], (F, F)>,
    /// mapping from base2 input to base9 and base13 output
    base2_map: HashMap<[u8; 32], (F, F)>,
}
impl<F: Field> LookupConfig<F> {
    pub(crate) fn configure(
        meta: &mut ConstraintSystem<F>,
        adv_cols: [Column<Advice>; 4],
        table_cols: [TableColumn; 4],
    ) -> Self {
        let cols: [(Column<Advice>, TableColumn); 4] = adv_cols
            .iter()
            .cloned()
            .zip(table_cols.iter().cloned())
            .collect_vec()
            .try_into()
            .unwrap();
        let q_enable = meta.complex_selector();
        meta.lookup("keccak", |meta| {
            let q_enable = meta.query_selector(q_enable);
            let col0_adv = meta.query_advice(cols[0].0, Rotation::cur());
            let col1_adv = meta.query_advice(cols[1].0, Rotation::cur());
            let col2_adv = meta.query_advice(cols[2].0, Rotation::cur());
            let col3_adv = meta.query_advice(cols[3].0, Rotation::cur());

            vec![
                (q_enable.clone() * col0_adv, cols[0].1),
                (q_enable.clone() * col1_adv, cols[1].1),
                (q_enable.clone() * col2_adv, cols[2].1),
                (q_enable * col3_adv, cols[3].1),
            ]
        });
        let special_chunks_map = HashMap::new();
        let base13_map = HashMap::new();
        let base9_map = HashMap::new();
        let base2_map = HashMap::new();
        Self {
            q_enable,
            cols,
            special_chunks_map,
            base13_map,
            base9_map,
            base2_map,
        }
    }

    fn assign_table_row(
        &self,
        table: &mut Table<F>,
        offset: usize,
        tag: TableTags,
        values: [F; 3],
    ) -> Result<(), Error> {
        table.assign_cell(|| "tag", self.cols[0].1, offset, || Ok(F::from(tag as u64)))?;
        for (col, value) in self.cols[1..4].iter().zip(values.iter()) {
            table.assign_cell(|| "cell", col.1, offset, || Ok(value))?;
        }
        Ok(())
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
            self.assign_table_row(table, offset, tag, [F::from(i), F::zero(), F::zero()])?;
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
                self.assign_table_row(
                    table,
                    offset,
                    TableTags::SpecialChunk,
                    [last_chunk, output_coef, F::zero()],
                )?;
                offset += 1;
            }
        }
        Ok(offset)
    }

    fn load_boolean_flag(&self, table: &mut Table<F>, offset: usize) -> Result<usize, Error> {
        let mut offset = offset;
        for (left, right) in [(true, false), (false, true)] {
            self.assign_table_row(
                table,
                offset,
                TableTags::BooleanFlag,
                [F::from(left), F::from(right), F::zero()],
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
                offset = self.load_boolean_flag(&mut table, offset)?;
                offset = self.load_base13(&mut table, offset)?;
                offset = self.load_base9(&mut table, offset)?;
                self.load_base2(&mut table, offset)?;
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
                for (offset, v) in values.iter().enumerate() {
                    self.q_enable.enable(&mut region, offset)?;
                    region.assign_advice_from_constant(
                        || "tag",
                        self.cols[0].0,
                        offset,
                        F::from(tag as u64),
                    )?;
                    v.copy_advice(|| "v", &mut region, self.cols[1].0, offset)?;
                    region.assign_advice_from_constant(
                        || "0",
                        self.cols[2].0,
                        offset,
                        F::zero(),
                    )?;
                    region.assign_advice_from_constant(
                        || "0",
                        self.cols[3].0,
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
                self.q_enable.enable(&mut region, offset)?;
                region.assign_advice_from_constant(|| "tag", self.cols[0].0, offset, tag)?;
                last_chunk.copy_advice(|| "last chunk", &mut region, self.cols[1].0, offset)?;
                let output_coef = region.assign_advice(
                    || "output coef",
                    self.cols[2].0,
                    offset,
                    || {
                        last_chunk
                            .value()
                            .and_then(|&v| self.special_chunks_map.get(&v.to_repr()))
                            .map(|v| v.to_owned())
                            .ok_or(Error::Synthesis)
                    },
                )?;
                region.assign_advice_from_constant(|| "0", self.cols[3].0, offset, F::zero())?;
                Ok(output_coef)
            },
        )
    }
    /// Output two boolean cells. Prover can choose to enable one and disable
    /// another, but not both.
    pub(crate) fn assign_boolean_flag(
        &self,
        layouter: &mut impl Layouter<F>,
        is_left: bool,
    ) -> Result<(AssignedCell<F, F>, AssignedCell<F, F>), Error> {
        layouter.assign_region(
            || "lookup for boolean flag",
            |mut region| {
                let offset = 0;
                self.q_enable.enable(&mut region, offset)?;
                region.assign_advice_from_constant(
                    || "tag",
                    self.cols[0].0,
                    offset,
                    F::from(TableTags::BooleanFlag as u64),
                )?;
                let left = region.assign_advice(
                    || "left",
                    self.cols[1].0,
                    offset,
                    || Ok(F::from(is_left)),
                )?;
                let right = region.assign_advice(
                    || "right",
                    self.cols[2].0,
                    offset,
                    || Ok(F::from(!is_left)),
                )?;
                region.assign_advice_from_constant(|| "0", self.cols[3].0, offset, F::zero())?;
                Ok((left, right))
            },
        )
    }

    pub(crate) fn load_base13(
        &mut self,
        table: &mut Table<F>,
        offset: usize,
    ) -> Result<usize, Error> {
        let mut offset = offset;
        // Iterate over all possible 13-ary values of size 4
        for b13_chunks in (0..BASE_NUM_OF_CHUNKS)
            .map(|_| 0..B13)
            .multi_cartesian_product()
        {
            let input_b13 = f_from_radix_be::<F>(&b13_chunks, B13);
            let output_b9 = f_from_radix_be::<F>(
                &b13_chunks
                    .iter()
                    .map(|&x| convert_b13_coef(x))
                    .collect_vec(),
                B9,
            );
            let overflow_detector =
                F::from(get_overflow_detector(b13_chunks.clone().try_into().unwrap()) as u64);

            self.base13_map
                .insert(input_b13.to_repr(), (output_b9, overflow_detector));

            self.assign_table_row(
                table,
                offset,
                TableTags::FromBase13,
                [input_b13, output_b9, overflow_detector],
            )?;
            offset += 1;
        }
        Ok(offset)
    }
    pub(crate) fn assign_base13(
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
                    self.q_enable.enable(&mut region, offset)?;
                    let input = biguint_to_f::<F>(&conv.input.coef);
                    let outputs = self.base13_map.get(&input.to_repr());
                    region.assign_advice_from_constant(
                        || "tag",
                        self.cols[0].0,
                        offset,
                        F::from(TableTags::FromBase13 as u64),
                    )?;
                    let input_coef = region.assign_advice(
                        || "Input Coef",
                        self.cols[1].0,
                        offset,
                        || Ok(input),
                    )?;
                    input_coefs.push(input_coef);

                    let output_coef = region.assign_advice(
                        || "Output Coef",
                        self.cols[2].0,
                        offset,
                        || outputs.map(|o| o.0).ok_or(Error::Synthesis),
                    )?;
                    output_coefs.push(output_coef);

                    let od = region.assign_advice(
                        || "Overflow detector",
                        self.cols[3].0,
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

    fn compute_input_coefs<const SLICES: usize>(
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

    pub fn load_base9(&mut self, table: &mut Table<F>, offset: usize) -> Result<usize, Error> {
        let mut offset = offset;
        // Iterate over all possible base 9 values of size 5
        for b9_chunks in (0..NUM_OF_B9_CHUNKS_PER_SLICE)
            .map(|_| 0..B9)
            .multi_cartesian_product()
        {
            let input_b9 = f_from_radix_be::<F>(&b9_chunks, B9);
            let converted_chunks: Vec<u8> =
                b9_chunks.iter().map(|&x| convert_b9_coef(x)).collect_vec();
            let output_b13 = f_from_radix_be::<F>(&converted_chunks, B13);
            let output_b2 = f_from_radix_be::<F>(&converted_chunks, B2);
            self.base9_map
                .insert(input_b9.to_repr(), (output_b13, output_b2));
            self.assign_table_row(
                table,
                offset,
                TableTags::FromBase9,
                [input_b9, output_b13, output_b2],
            )?;
            offset += 1;
        }
        Ok(offset)
    }

    pub fn assign_base9(
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
        let input_coefs = Self::compute_input_coefs::<NUM_OF_B9_SLICES>(
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
                    self.q_enable.enable(&mut region, offset)?;
                    region.assign_advice_from_constant(
                        || "tag",
                        self.cols[0].0,
                        offset,
                        F::from(TableTags::FromBase9 as u64),
                    )?;
                    let input = region.assign_advice(
                        || "base 9",
                        self.cols[1].0,
                        offset,
                        || input_coef.ok_or(Error::Synthesis),
                    )?;
                    input_cells.push(input.clone());
                    let output = input_coef.and_then(|v| self.base9_map.get(&v.to_repr()));

                    let output_b13 = region.assign_advice(
                        || "base 13",
                        self.cols[2].0,
                        offset,
                        || output.map(|v| v.0).ok_or(Error::Synthesis),
                    )?;
                    output_b13_cells.push(output_b13);
                    let output_b2 = region.assign_advice(
                        || "base 2",
                        self.cols[3].0,
                        offset,
                        || output.map(|v| v.1).ok_or(Error::Synthesis),
                    )?;
                    output_b2_cells.push(output_b2);
                }
                Ok((input_cells, output_b13_cells, output_b2_cells))
            },
        )
    }

    pub fn load_base2(&mut self, table: &mut Table<F>, offset: usize) -> Result<usize, Error> {
        let mut offset = offset;
        for b2_chunks in (0..NUM_OF_BINARY_CHUNKS_PER_SLICE)
            .map(|_| 0..B2)
            .multi_cartesian_product()
        {
            let input_b2 = f_from_radix_be::<F>(&b2_chunks, B2);
            let output_b9 = f_from_radix_be::<F>(&b2_chunks, B9);
            let output_b13 = f_from_radix_be::<F>(&b2_chunks, B13);

            self.base2_map
                .insert(input_b2.to_repr(), (output_b9, output_b13));
            self.assign_table_row(
                table,
                offset,
                TableTags::FromBase2,
                [input_b2, output_b9, output_b13],
            )?;
            offset += 1;
        }
        Ok(offset)
    }

    pub fn assign_base2(
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
        let input_coefs = Self::compute_input_coefs::<NUM_OF_BINARY_SLICES>(
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
                    self.q_enable.enable(&mut region, offset)?;
                    region.assign_advice_from_constant(
                        || "tag",
                        self.cols[0].0,
                        offset,
                        F::from(TableTags::FromBase2 as u64),
                    )?;
                    let input = region.assign_advice(
                        || "base 2",
                        self.cols[1].0,
                        offset,
                        || input_coef.ok_or(Error::Synthesis),
                    )?;
                    input_cells.push(input.clone());

                    let output = input_coef.and_then(|v| self.base2_map.get(&v.to_repr()));

                    let output_b9 = region.assign_advice(
                        || "base 9",
                        self.cols[2].0,
                        offset,
                        || output.map(|v| v.0).ok_or(Error::Synthesis),
                    )?;
                    output_b9_cells.push(output_b9);
                    let output_b13 = region.assign_advice(
                        || "base 13",
                        self.cols[3].0,
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
