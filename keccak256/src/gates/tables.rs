/*
tables:
- binary to 13 conversion
- 13 to 9 conversion
- special chunk conversion
- 9 to binary and 9 to 13 conversion
*/

use crate::arith_helpers::*;
use crate::common::*;
use halo2::{
    arithmetic::FieldExt,
    circuit::Layouter,
    plonk::{Advice, Column, ConstraintSystem, Error, Fixed, Selector},
    poly::Rotation,
};
use std::marker::PhantomData;

use itertools::Itertools;
use num_bigint::BigUint;

pub struct BinaryToBase13TableConfig<F> {
    binary: Column<Fixed>,
    base13: Column<Fixed>,
    q_lookup: Selector,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> BinaryToBase13TableConfig<F> {
    pub(crate) fn load(
        &self,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "from binary",
            |mut region| {
                // Iterate over all possible 16-bit values
                for (i, coefs) in
                    (0..16).map(|_| 0..1).multi_cartesian_product().enumerate()
                {
                    region.assign_fixed(
                        || "binary",
                        self.binary,
                        i,
                        || {
                            Ok(coefs.iter().fold(F::zero(), |acc, x| {
                                acc * F::from_u64(2) + F::from_u64(*x)
                            }))
                        },
                    )?;

                    region.assign_fixed(
                        || "base 13 col",
                        self.base13,
                        i,
                        || {
                            Ok(coefs.iter().fold(F::zero(), |acc, x| {
                                acc * F::from_u64(B13) + F::from_u64(*x)
                            }))
                        },
                    )?;
                }
                Ok(())
            },
        )
    }

    pub(crate) fn configure(
        meta: &mut ConstraintSystem<F>,
        q_lookup: Selector,
        binary_advice: Column<Advice>,
        base13_advice: Column<Advice>,
        binary: Column<Fixed>,
        base13: Column<Fixed>,
    ) -> Self {
        let config = Self {
            binary,
            base13,
            q_lookup,
            _marker: PhantomData,
        };

        // Lookup for binary to base-13 conversion
        meta.lookup(|meta| {
            let q_lookup = meta.query_selector(config.q_lookup);
            let binary_advice =
                meta.query_advice(binary_advice, Rotation::cur());
            let base13_advice =
                meta.query_advice(base13_advice, Rotation::cur());
            let binary = meta.query_fixed(config.binary, Rotation::cur());
            let base13 = meta.query_fixed(config.base13, Rotation::cur());

            vec![
                (q_lookup.clone() * binary_advice, binary),
                (q_lookup * base13_advice, base13),
            ]
        });
        config
    }
}

fn block_counting_function(n: usize) -> u64 {
    [0, 0, 1, 13, 170][n]
}

#[derive(Debug, Clone)]
pub struct Base13toBase9TableConfig<F> {
    base13: Column<Fixed>,
    base9: Column<Fixed>,
    block_count: Column<Fixed>,
    q_lookup: Selector,
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
                for (i, coefs) in
                    (0..4).map(|_| 0..B13).multi_cartesian_product().enumerate()
                {
                    region.assign_fixed(
                        || "base 13",
                        self.base13,
                        i,
                        || {
                            Ok(coefs.iter().fold(F::zero(), |acc, x| {
                                acc * F::from_u64(B13) + F::from_u64(*x)
                            }))
                        },
                    )?;

                    region.assign_fixed(
                        || "base 9",
                        self.base9,
                        i,
                        || {
                            Ok(coefs.iter().fold(F::zero(), |acc, x| {
                                acc * F::from_u64(B9)
                                    + F::from_u64(convert_b13_coef(*x))
                            }))
                        },
                    )?;
                    region.assign_fixed(
                        || "block_count",
                        self.block_count,
                        i,
                        || {
                            // could be 0, 1, 2, 3, 4
                            let non_zero_chunk_count =
                                coefs.iter().filter(|x| **x != 0).count();
                            // could be 0, 0, 1, 13, 170
                            let block_count =
                                block_counting_function(non_zero_chunk_count);
                            Ok(F::from_u64(block_count))
                        },
                    )?;
                }
                Ok(())
            },
        )
    }

    pub(crate) fn configure(
        meta: &mut ConstraintSystem<F>,
        q_lookup: Selector,
        base13_advice: Column<Advice>,
        base9_advice: Column<Advice>,
        block_count: Column<Advice>,
        fixed: [Column<Fixed>; 3],
    ) -> Self {
        let config = Self {
            base13: fixed[0],
            base9: fixed[1],
            block_count: fixed[2],
            q_lookup,
            _marker: PhantomData,
        };

        meta.lookup(|meta| {
            let q_lookup = meta.query_selector(q_lookup);
            let base13_advice =
                meta.query_advice(base13_advice, Rotation::cur());
            let base9_advice = meta.query_advice(base9_advice, Rotation::cur());
            let bc = meta.query_advice(block_count, Rotation::cur());

            let base13 = meta.query_fixed(config.base13, Rotation::cur());
            let base9 = meta.query_fixed(config.base9, Rotation::cur());
            let block_count =
                meta.query_fixed(config.block_count, Rotation::cur());

            vec![
                (q_lookup.clone() * base9_advice, base13),
                (q_lookup.clone() * base13_advice, base9),
                (q_lookup * bc, block_count),
            ]
        });
        config
    }

    pub fn get_block_count_and_output_coef(
        &self,
        input_coef: BigUint,
    ) -> (u32, u64) {
        let mut x = input_coef;
        let mut output_coef = 0;
        let mut non_zero_chunk_count = 0;
        for i in 0..4 {
            let base13_chunk = match (x.clone() % B13).to_u64_digits().first() {
                Some(d) => *d,
                None => 0u64,
            };
            let base9_chunk = convert_b13_coef(base13_chunk);
            if base9_chunk != 0 {
                non_zero_chunk_count += 1;
            }
            output_coef += base9_chunk * B9.pow(i as u32);
            x /= B13;
        }
        let block_count = block_counting_function(non_zero_chunk_count);

        (block_count as u32, output_coef)
    }
}

#[derive(Debug, Clone)]
pub struct SpecialChunkTableConfig<F> {
    q_enable: Selector,
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
            || "for special chunks",
            |mut region| {
                // Iterate over all possible values less than 13 for both low
                // and high
                for i in 0..B13 {
                    for j in 0..(B13 - i) {
                        let (low, high) = (i, j);

                        region.assign_fixed(
                            || "key",
                            self.last_chunk,
                            i as usize,
                            || {
                                Ok(F::from_u64(low)
                                    + F::from_u64(high)
                                        * F::from_u64(B13).pow(&[
                                            LANE_SIZE as u64,
                                            0,
                                            0,
                                            0,
                                        ]))
                            },
                        )?;
                        region.assign_fixed(
                            || "value",
                            self.output_coef,
                            i as usize,
                            || Ok(F::from_u64(convert_b13_coef(low + high))),
                        )?;
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
            q_enable,
            last_chunk: cols[0],
            output_coef: cols[1],
            _marker: PhantomData,
        };
        // Lookup for special chunk conversion
        meta.lookup(|meta| {
            let last_chunk_advice =
                meta.query_advice(last_chunk_advice, Rotation::cur());
            let output_coef_advice =
                meta.query_advice(output_coef_advice, Rotation::cur());

            let last_chunk =
                meta.query_fixed(config.last_chunk, Rotation::cur());
            let output_coef =
                meta.query_fixed(config.output_coef, Rotation::cur());

            vec![
                (last_chunk_advice, last_chunk),
                (output_coef_advice, output_coef),
            ]
        });
        config
    }
}
pub struct Base9toBase13BinaryTableConfig<F> {
    base9: Column<Fixed>,
    base13: Column<Fixed>,
    binary: Column<Fixed>,
    q_lookup: Selector,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> Base9toBase13BinaryTableConfig<F> {
    pub(crate) fn load(
        &self,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "from base 9",
            |mut region| {
                // Iterate over all possible 9-ary values of size 4
                for (i, coefs) in
                    (0..4).map(|_| 0..B9).multi_cartesian_product().enumerate()
                {
                    region.assign_fixed(
                        || "base 9",
                        self.base9,
                        i,
                        || {
                            Ok(coefs.iter().fold(F::zero(), |acc, x| {
                                acc * F::from_u64(B9) + F::from_u64(*x)
                            }))
                        },
                    )?;

                    region.assign_fixed(
                        || "base 13",
                        self.base13,
                        i,
                        || {
                            Ok(coefs.iter().fold(F::zero(), |acc, x| {
                                acc * F::from_u64(B13) + F::from_u64(*x)
                            }))
                        },
                    )?;

                    region.assign_fixed(
                        || "binary",
                        self.binary,
                        i,
                        || {
                            Ok(coefs.iter().fold(F::zero(), |acc, x| {
                                acc * F::from_u64(2) + F::from_u64(*x)
                            }))
                        },
                    )?;
                }
                Ok(())
            },
        )
    }

    pub(crate) fn configure(
        meta: &mut ConstraintSystem<F>,
        q_lookup: Selector,
        advices: [Column<Advice>; 3],
        fixed: [Column<Fixed>; 3],
    ) -> Self {
        let config = Self {
            base9: fixed[0],
            base13: fixed[1],
            binary: fixed[2],
            q_lookup,
            _marker: PhantomData,
        };

        // Lookup for base-9 to base-13/binary conversion
        meta.lookup(|meta| {
            let q_lookup = meta.query_selector(q_lookup);
            let base9_advice = meta.query_advice(advices[0], Rotation::cur());
            let base13_advice = meta.query_advice(advices[1], Rotation::next());
            let binary_advice = meta.query_advice(advices[2], Rotation::next());

            let base9 = meta.query_fixed(config.base9, Rotation::cur());
            let base13 = meta.query_fixed(config.base13, Rotation::cur());
            let binary = meta.query_fixed(config.binary, Rotation::cur());

            vec![
                (q_lookup.clone() * base9_advice, base9),
                (q_lookup.clone() * base13_advice, base13),
                (q_lookup * binary_advice, binary),
            ]
        });
        config
    }
}
