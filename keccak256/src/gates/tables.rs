use crate::arith_helpers::*;
use crate::common::LANE_SIZE;
use crate::gates::rho_helpers::{get_block_count, BASE_NUM_OF_CHUNKS};
use halo2::{
    arithmetic::FieldExt,
    circuit::Layouter,
    plonk::{Advice, Column, ConstraintSystem, Error, Fixed, Selector},
    poly::Rotation,
};
use std::convert::TryInto;
use std::marker::PhantomData;

use itertools::Itertools;

#[derive(Debug, Clone)]
pub struct Base13toBase9TableConfig<F> {
    base13: Column<Fixed>,
    base9: Column<Fixed>,
    block_count: Column<Fixed>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> Base13toBase9TableConfig<F> {
    pub(crate) fn load(
        &self,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "from base13",
            |mut region| {
                // Iterate over all possible 13-ary values of size 4
                for (i, b13_chunks) in (0..BASE_NUM_OF_CHUNKS)
                    .map(|_| 0..B13)
                    .multi_cartesian_product()
                    .enumerate()
                {
                    region.assign_fixed(
                        || "base 13",
                        self.base13,
                        i,
                        || {
                            Ok(F::from_u64(
                                b13_chunks
                                    .iter()
                                    .fold(0, |acc, x| acc * B13 + *x),
                            ))
                        },
                    )?;

                    region.assign_fixed(
                        || "base 9",
                        self.base9,
                        i,
                        || {
                            Ok(F::from_u64(
                                b13_chunks.iter().fold(0, |acc, x| {
                                    acc * B9 + convert_b13_coef(*x)
                                }),
                            ))
                        },
                    )?;
                    region.assign_fixed(
                        || "block_count",
                        self.block_count,
                        i,
                        || {
                            Ok(F::from_u64(
                                get_block_count(
                                    b13_chunks.clone().try_into().unwrap(),
                                )
                                .into(),
                            ))
                        },
                    )?;
                }
                Ok(())
            },
        )
    }

    pub(crate) fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: Selector,
        base13_coef: Column<Advice>,
        base9_coef: Column<Advice>,
        block_count: Column<Advice>,
        fixed: [Column<Fixed>; 3],
    ) -> Self {
        let config = Self {
            base13: fixed[0],
            base9: fixed[1],
            block_count: fixed[2],
            _marker: PhantomData,
        };

        meta.lookup(|meta| {
            let q_enable = meta.query_selector(q_enable);
            let base13_coef = meta.query_advice(base13_coef, Rotation::cur());
            let base9_coef = meta.query_advice(base9_coef, Rotation::cur());
            let bc = meta.query_advice(block_count, Rotation::cur());

            let base13 = meta.query_fixed(config.base13, Rotation::cur());
            let base9 = meta.query_fixed(config.base9, Rotation::cur());
            let block_count =
                meta.query_fixed(config.block_count, Rotation::cur());

            vec![
                (q_enable.clone() * base13_coef, base13),
                (q_enable.clone() * base9_coef, base9),
                (q_enable * bc, block_count),
            ]
        });
        config
    }
}

/// The table describes all possible combinations of these two variables:
/// - The last input accumulator: `high_value`*(13**64) + `low_value`, and
/// - The last output coef: `convert_b13_coef(high_value + low_value)`
#[derive(Debug, Clone)]
pub struct SpecialChunkTableConfig<F> {
    last_chunk: Column<Fixed>,
    output_coef: Column<Fixed>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> SpecialChunkTableConfig<F> {
    pub(crate) fn load(
        &self,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "Special Chunks",
            |mut region| {
                // Iterate over all possible values less than 13 for both low
                // and high
                let mut offset = 0;
                for i in 0..B13 {
                    for j in 0..(B13 - i) {
                        let (low, high) = (i, j);
                        let last_chunk = F::from_u64(low)
                            + F::from_u64(high)
                                * F::from_u64(B13).pow(&[
                                    LANE_SIZE as u64,
                                    0,
                                    0,
                                    0,
                                ]);
                        let output_coef =
                            F::from_u64(convert_b13_coef(low + high));
                        region.assign_fixed(
                            || "last chunk",
                            self.last_chunk,
                            offset,
                            || Ok(last_chunk),
                        )?;
                        region.assign_fixed(
                            || "output coef",
                            self.output_coef,
                            offset,
                            || Ok(output_coef),
                        )?;
                        offset += 1;
                    }
                }
                Ok(())
            },
        )
    }

    pub(crate) fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: Selector,
        last_chunk_advice: Column<Advice>,
        output_coef_advice: Column<Advice>,
        cols: [Column<Fixed>; 2],
    ) -> Self {
        let config = Self {
            last_chunk: cols[0],
            output_coef: cols[1],
            _marker: PhantomData,
        };
        // Lookup for special chunk conversion
        meta.lookup(|meta| {
            let q_enable = meta.query_selector(q_enable);
            let last_chunk_advice =
                meta.query_advice(last_chunk_advice, Rotation::cur());
            let output_coef_advice =
                meta.query_advice(output_coef_advice, Rotation::cur());

            let last_chunk =
                meta.query_fixed(config.last_chunk, Rotation::cur());
            let output_coef =
                meta.query_fixed(config.output_coef, Rotation::cur());

            vec![
                (q_enable.clone() * last_chunk_advice, last_chunk),
                (q_enable * output_coef_advice, output_coef),
            ]
        });
        config
    }
}
