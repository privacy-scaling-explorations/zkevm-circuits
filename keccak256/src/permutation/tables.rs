use crate::arith_helpers::{convert_b13_coef, convert_b9_coef, f_from_radix_be, B13, B2, B9};
use crate::common::LANE_SIZE;
use crate::gate_helpers::f_to_biguint;
use crate::permutation::rho_helpers::{get_overflow_detector, BASE_NUM_OF_CHUNKS};
use eth_types::Field;
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, Table},
    plonk::{Advice, Column, ConstraintSystem, Error, Selector, TableColumn},
    poly::Rotation,
};
use itertools::Itertools;
use std::convert::TryInto;
use std::marker::PhantomData;
use strum_macros::{Display, EnumIter};

use super::rho_helpers::{STEP2_RANGE, STEP3_RANGE};

const MAX_CHUNKS: usize = 64;
const NUM_OF_BINARY_CHUNKS: usize = 16;
const NUM_OF_B9_CHUNKS: usize = 5;

#[derive(EnumIter, Display, Clone, Copy)]
enum TableTags {
    Range12 = 0,
    Range169,
    SpecialChunk,
    BooleanFlag,
}

#[derive(Debug, Clone)]
pub struct StackableTable<F> {
    q_enable: Selector,
    tag: (Column<Advice>, TableColumn),
    col1: (Column<Advice>, TableColumn),
    col2: (Column<Advice>, TableColumn),
    _marker: PhantomData<F>,
}

impl<F: Field> StackableTable<F> {
    pub(crate) fn configure(
        meta: &mut ConstraintSystem<F>,
        adv_cols: [Column<Advice>; 3],
        table_cols: [TableColumn; 3],
    ) -> Self {
        let tag = (adv_cols[0], table_cols[0]);
        let col1 = (adv_cols[1], table_cols[1]);
        let col2 = (adv_cols[2], table_cols[2]);
        let q_enable = meta.complex_selector();
        meta.lookup("stackable lookup", |meta| {
            let q_enable = meta.query_selector(q_enable);
            let tag_adv = meta.query_advice(tag.0, Rotation::cur());
            let col1_adv = meta.query_advice(col1.0, Rotation::cur());
            let col2_adv = meta.query_advice(col2.0, Rotation::cur());

            vec![
                (q_enable.clone() * tag_adv, tag.1),
                (q_enable.clone() * col1_adv, col1.1),
                (q_enable * col2_adv, col2.1),
            ]
        });
        Self {
            q_enable,
            tag,
            col1,
            col2,
            _marker: PhantomData,
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
                self.tag.1,
                offset,
                || Ok(F::from(tag as u64)),
            )?;
            table.assign_cell(
                || format!("range{}", tag),
                self.col1.1,
                offset,
                || Ok(F::from(i)),
            )?;
            table.assign_cell(
                || format!("dummy col range{}", tag),
                self.col2.1,
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
    fn load_special_chunks(&self, table: &mut Table<F>, offset: usize) -> Result<usize, Error> {
        let mut offset = offset;
        for i in 0..B13 {
            for j in 0..(B13 - i) {
                let (low, high) = (i, j);
                let last_chunk = F::from(low as u64)
                    + F::from(high as u64) * F::from(B13 as u64).pow(&[LANE_SIZE as u64, 0, 0, 0]);
                let output_coef = F::from(convert_b13_coef(low + high) as u64);
                table.assign_cell(
                    || "tag special chunks",
                    self.tag.1,
                    offset,
                    || Ok(F::from(TableTags::SpecialChunk as u64)),
                )?;
                table.assign_cell(|| "last chunk", self.col1.1, offset, || Ok(last_chunk))?;
                table.assign_cell(|| "output coef", self.col2.1, offset, || Ok(output_coef))?;
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
                self.tag.1,
                offset,
                || Ok(F::from(TableTags::BooleanFlag as u64)),
            )?;
            table.assign_cell(|| "left", self.col1.1, offset, || Ok(F::from(left)))?;
            table.assign_cell(|| "right", self.col2.1, offset, || Ok(F::from(right)))?;
            offset += 1;
        }
        Ok(offset)
    }
    pub(crate) fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
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
                    self.q_enable.enable(&mut region, offset)?;
                    region.assign_advice_from_constant(|| "tag", self.tag.0, offset, tag)?;
                    v.copy_advice(|| "value", &mut region, self.col1.0, offset)?;
                    region.assign_advice_from_constant(
                        || "dummy",
                        self.col2.0,
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
        output_coef: &AssignedCell<F, F>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "lookup for special chunks",
            |mut region| {
                let offset = 0;
                let tag = F::from(TableTags::SpecialChunk as u64);
                self.q_enable.enable(&mut region, offset)?;
                region.assign_advice_from_constant(|| "tag", self.tag.0, offset, tag)?;
                last_chunk.copy_advice(|| "last chunk", &mut region, self.col1.0, offset)?;
                output_coef.copy_advice(|| "output coef", &mut region, self.col2.0, offset)?;
                Ok(())
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
                self.q_enable.enable(&mut region, offset)?;
                region.assign_advice_from_constant(
                    || "tag",
                    self.tag.0,
                    offset,
                    F::from(TableTags::BooleanFlag as u64),
                )?;
                let left = region.assign_advice(
                    || "left",
                    self.col1.0,
                    offset,
                    || is_left.map(|flag| F::from(flag)).ok_or(Error::Synthesis),
                )?;
                let right = region.assign_advice(
                    || "right",
                    self.col2.0,
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
    pub base13: TableColumn,
    pub base9: TableColumn,
    pub overflow_detector: TableColumn,
    _marker: PhantomData<F>,
}

impl<F: Field> Base13toBase9TableConfig<F> {
    pub(crate) fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(
            || "13 -> 9",
            |mut table| {
                // Iterate over all possible 13-ary values of size 4
                for (i, b13_chunks) in (0..BASE_NUM_OF_CHUNKS)
                    .map(|_| 0..B13)
                    .multi_cartesian_product()
                    .enumerate()
                {
                    table.assign_cell(
                        || "base 13",
                        self.base13,
                        i,
                        || Ok(f_from_radix_be::<F>(&b13_chunks, B13)),
                    )?;

                    table.assign_cell(
                        || "base 9",
                        self.base9,
                        i,
                        || {
                            let converted_chunks: Vec<u8> = b13_chunks
                                .iter()
                                .map(|&x| convert_b13_coef(x))
                                .collect_vec();
                            Ok(f_from_radix_be::<F>(&converted_chunks, B9))
                        },
                    )?;
                    table.assign_cell(
                        || "overflow_detector",
                        self.overflow_detector,
                        i,
                        || {
                            Ok(F::from(
                                get_overflow_detector(b13_chunks.clone().try_into().unwrap())
                                    as u64,
                            ))
                        },
                    )?;
                }
                Ok(())
            },
        )
    }

    pub(crate) fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            base13: meta.lookup_table_column(),
            base9: meta.lookup_table_column(),
            overflow_detector: meta.lookup_table_column(),
            _marker: PhantomData,
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct BaseInfo<F> {
    input_base: u8,
    output_base: u8,
    // How many chunks we perform in a lookup?
    num_chunks: usize,
    // How many chunks in total
    pub max_chunks: usize,
    pub input_tc: TableColumn,
    pub output_tc: TableColumn,
    _marker: PhantomData<F>,
}

impl<F: Field> BaseInfo<F> {
    pub fn input_pob(&self) -> F {
        F::from(self.input_base as u64).pow(&[self.num_chunks as u64, 0, 0, 0])
    }
    pub fn output_pob(&self) -> F {
        F::from(self.output_base as u64).pow(&[self.num_chunks as u64, 0, 0, 0])
    }

    pub fn compute_coefs(&self, input: F) -> Result<(Vec<F>, Vec<F>, F), Error> {
        // big-endian
        let input_chunks: Vec<u8> = {
            let raw = f_to_biguint(input);
            let mut v = raw.to_radix_le(self.input_base.into());
            debug_assert!(v.len() <= self.max_chunks);
            // fill 0 to max chunks
            v.resize(self.max_chunks, 0);
            // v is big-endian now
            v.reverse();
            v
        };
        // Use rchunks + rev so that the remainder chunks stay at the big-endian
        // side
        let input_coefs: Vec<F> = input_chunks
            .rchunks(self.num_chunks)
            .rev()
            .map(|chunks| f_from_radix_be(chunks, self.input_base))
            .collect();
        let convert_chunk = match self.input_base {
            B2 => |x| x,
            B13 => convert_b13_coef,
            B9 => convert_b9_coef,
            _ => unreachable!(),
        };
        let output: F = {
            let converted_chunks: Vec<u8> =
                input_chunks.iter().map(|&x| convert_chunk(x)).collect_vec();
            f_from_radix_be(&converted_chunks, self.output_base)
        };

        let output_coefs: Vec<F> = input_chunks
            .rchunks(self.num_chunks)
            .rev()
            .map(|chunks| {
                let converted_chunks: Vec<u8> =
                    chunks.iter().map(|&x| convert_chunk(x)).collect_vec();
                f_from_radix_be(&converted_chunks, self.output_base)
            })
            .collect();
        Ok((input_coefs, output_coefs, output))
    }
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
pub struct FromBinaryTableConfig<F> {
    base2: TableColumn,
    base9: TableColumn,
    base13: TableColumn,
    _marker: PhantomData<F>,
}

#[allow(dead_code)]
impl<F: Field> FromBinaryTableConfig<F> {
    pub(crate) fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(
            || "2 -> (9 and 13)",
            |mut table| {
                // Iterate over all possible binary values of size 16
                for (i, b2_chunks) in (0..NUM_OF_BINARY_CHUNKS)
                    .map(|_| 0..B2)
                    .multi_cartesian_product()
                    .enumerate()
                {
                    table.assign_cell(
                        || "base 2",
                        self.base2,
                        i,
                        || Ok(f_from_radix_be::<F>(&b2_chunks, B2)),
                    )?;

                    table.assign_cell(
                        || "base 9",
                        self.base9,
                        i,
                        || Ok(f_from_radix_be::<F>(&b2_chunks, B9)),
                    )?;
                    table.assign_cell(
                        || "base 13",
                        self.base13,
                        i,
                        || Ok(f_from_radix_be::<F>(&b2_chunks, B13)),
                    )?;
                }
                Ok(())
            },
        )
    }

    pub(crate) fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            base2: meta.lookup_table_column(),
            base9: meta.lookup_table_column(),
            base13: meta.lookup_table_column(),
            _marker: PhantomData,
        }
    }

    pub(crate) fn get_base_info(&self, output_b9: bool) -> BaseInfo<F> {
        BaseInfo {
            input_base: B2,
            output_base: if output_b9 { B9 } else { B13 },
            num_chunks: NUM_OF_BINARY_CHUNKS,
            max_chunks: MAX_CHUNKS,
            input_tc: self.base2,
            output_tc: if output_b9 { self.base9 } else { self.base13 },
            _marker: PhantomData,
        }
    }
}

#[derive(Debug, Clone)]
pub struct FromBase9TableConfig<F> {
    base9: TableColumn,
    base13: TableColumn,
    base2: TableColumn,
    _marker: PhantomData<F>,
}

impl<F: Field> FromBase9TableConfig<F> {
    pub fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(
            || "9 -> (2 and 13)",
            |mut table| {
                // Iterate over all possible base 9 values of size 5
                for (i, b9_chunks) in (0..NUM_OF_B9_CHUNKS)
                    .map(|_| 0..B9)
                    .multi_cartesian_product()
                    .enumerate()
                {
                    table.assign_cell(
                        || "base 9",
                        self.base9,
                        i,
                        || Ok(f_from_radix_be::<F>(&b9_chunks, B9)),
                    )?;
                    let converted_chunks: Vec<u8> =
                        b9_chunks.iter().map(|&x| convert_b9_coef(x)).collect_vec();
                    table.assign_cell(
                        || "base 13",
                        self.base13,
                        i,
                        || Ok(f_from_radix_be::<F>(&converted_chunks, B13)),
                    )?;
                    table.assign_cell(
                        || "base 2",
                        self.base2,
                        i,
                        || Ok(f_from_radix_be::<F>(&converted_chunks, B2)),
                    )?;
                }
                Ok(())
            },
        )
    }

    pub fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            base2: meta.lookup_table_column(),
            base9: meta.lookup_table_column(),
            base13: meta.lookup_table_column(),
            _marker: PhantomData,
        }
    }

    pub(crate) fn get_base_info(&self, output_b2: bool) -> BaseInfo<F> {
        BaseInfo {
            input_base: B9,
            output_base: if output_b2 { B2 } else { B13 },
            num_chunks: NUM_OF_B9_CHUNKS,
            max_chunks: MAX_CHUNKS,
            input_tc: self.base9,
            output_tc: if output_b2 { self.base2 } else { self.base13 },
            _marker: PhantomData,
        }
    }
}
