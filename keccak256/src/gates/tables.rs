/*
tables:
- binary to 13 conversion
- 13 to 9 conversion
- special chunk conversion
- 9 to binary and 9 to 13 conversion
*/

use crate::arith_helpers::*;
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
    from_binary_config: [Column<Fixed>; 2],
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
                    let key = coefs.iter().fold(F::zero(), |acc, x| {
                        acc * F::from_u64(2) + F::from_u64(*x)
                    });

                    region.assign_fixed(
                        || "binary col",
                        self.from_binary_config[0],
                        i,
                        || Ok(key),
                    )?;

                    let value = coefs.iter().fold(F::zero(), |acc, x| {
                        acc * F::from_u64(B13) + F::from_u64(*x)
                    });

                    region.assign_fixed(
                        || "base 13 col",
                        self.from_binary_config[1],
                        i,
                        || Ok(value),
                    )?;
                }
                Ok(())
            },
        )
    }

    pub(crate) fn configure(
        meta: &mut ConstraintSystem<F>,
        q_lookup: Selector,
        binary_slice: Column<Advice>,
        base13_slice: Column<Advice>,
    ) -> Self {
        let config = Self {
            from_binary_config: [meta.fixed_column(), meta.fixed_column()],
            q_lookup,
            _marker: PhantomData,
        };

        // Lookup for binary to base-13 conversion
        meta.lookup(|meta| {
            let q_lookup = meta.query_selector(config.q_lookup);
            let binary_slice = meta.query_advice(binary_slice, Rotation::cur());
            let base13_slice =
                meta.query_advice(base13_slice, Rotation::next());
            let key =
                meta.query_fixed(config.from_binary_config[0], Rotation::cur());
            let value =
                meta.query_fixed(config.from_binary_config[1], Rotation::cur());

            vec![
                (q_lookup.clone() * binary_slice, key),
                (q_lookup * base13_slice, value),
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
    cols: [Column<Fixed>; 3],
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
                        self.cols[0],
                        i,
                        || {
                            Ok(coefs.iter().fold(F::zero(), |acc, x| {
                                acc * F::from_u64(B13) + F::from_u64(*x)
                            }))
                        },
                    )?;

                    region.assign_fixed(
                        || "base 9",
                        self.cols[1],
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
                        self.cols[2],
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
        base13_slice: Column<Advice>,
        base9_slice: Column<Advice>,
        block_count: Column<Advice>,
    ) -> Self {
        let config = Self {
            cols: [
                meta.fixed_column(),
                meta.fixed_column(),
                meta.fixed_column(),
            ],
            q_lookup,
            _marker: PhantomData,
        };

        meta.lookup(|meta| {
            let q_lookup = meta.query_selector(q_lookup);
            let base13_slice = meta.query_advice(base13_slice, Rotation::cur());
            let base9_slice = meta.query_advice(base9_slice, Rotation::cur());
            let block_count = meta.query_advice(block_count, Rotation::cur());

            let key = meta.query_fixed(config.cols[0], Rotation::cur());
            let value = meta.query_fixed(config.cols[1], Rotation::cur());
            let value2 = meta.query_fixed(config.cols[2], Rotation::cur());

            vec![
                (q_lookup.clone() * base9_slice, key),
                (q_lookup.clone() * base13_slice, value),
                (q_lookup * block_count, value2),
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
    from_special_chunk_config: [Column<Fixed>; 2],
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
                        let low = i;
                        let high = j;

                        region.assign_fixed(
                            || "key",
                            self.from_special_chunk_config[0],
                            i as usize,
                            || {
                                Ok(F::from_u64(low)
                                    + F::from_u64(high)
                                        * F::from_u64(B13).pow(&[64, 0, 0, 0]))
                            },
                        )?;
                        region.assign_fixed(
                            || "value",
                            self.from_special_chunk_config[1],
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
        last_b13_coef: Column<Advice>,
        last_b9_coef: Column<Advice>,
    ) -> Self {
        let from_special_chunk_config =
            [meta.fixed_column(), meta.fixed_column()];

        // Lookup for special chunk conversion
        meta.lookup(|meta| {
            let last_limb_key =
                meta.query_advice(last_b13_coef, Rotation::cur());
            let last_limb_value =
                meta.query_advice(last_b9_coef, Rotation::cur());

            let key =
                meta.query_fixed(from_special_chunk_config[0], Rotation::cur());
            let value =
                meta.query_fixed(from_special_chunk_config[1], Rotation::cur());

            vec![(last_limb_key, key), (last_limb_value, value)]
        });
        Self {
            q_enable,
            from_special_chunk_config,
            _marker: PhantomData,
        }
    }
}
pub struct Base9toBase13BinaryTableConfig<F> {
    cols: [Column<Fixed>; 3],
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
                        self.cols[0],
                        i,
                        || {
                            Ok(coefs.iter().fold(F::zero(), |acc, x| {
                                acc * F::from_u64(B9) + F::from_u64(*x)
                            }))
                        },
                    )?;

                    region.assign_fixed(
                        || "base 13",
                        self.cols[1],
                        i,
                        || {
                            Ok(coefs.iter().fold(F::zero(), |acc, x| {
                                acc * F::from_u64(B13) + F::from_u64(*x)
                            }))
                        },
                    )?;

                    region.assign_fixed(
                        || "binary",
                        self.cols[2],
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
    ) -> Self {
        let config = Self {
            cols: [
                meta.fixed_column(),
                meta.fixed_column(),
                meta.fixed_column(),
            ],
            q_lookup,
            _marker: PhantomData,
        };

        // Lookup for base-9 to base-13/binary conversion
        meta.lookup(|meta| {
            let q_lookup = meta.query_selector(q_lookup);
            let base9_word = meta.query_advice(advices[0], Rotation::cur());
            let base13_word = meta.query_advice(advices[1], Rotation::next());
            let binary_word = meta.query_advice(advices[2], Rotation::next());

            let key = meta.query_fixed(config.cols[0], Rotation::cur());
            let value0 = meta.query_fixed(config.cols[1], Rotation::cur());
            let value1 = meta.query_fixed(config.cols[2], Rotation::cur());

            vec![
                (q_lookup.clone() * base9_word, key),
                (q_lookup.clone() * base13_word, value0),
                (q_lookup * binary_word, value1),
            ]
        });
        config
    }
}
