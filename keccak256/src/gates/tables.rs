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

pub struct BinaryToBase13TableConfig<F> {
    from_binary_config: [Column<Fixed>; 2],
    q_lookup: Selector,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> BinaryToBase13TableConfig<F> {
    pub(crate) fn load(
        config: Self,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        Self::binary_converter(config, layouter)
    }

    pub(crate) fn configure(
        meta: &mut ConstraintSystem<F>,
        q_lookup: Selector,
        binary_slice: Column<Advice>,
        base13_slice: Column<Advice>,
    ) -> Self {
        let from_binary_config = [meta.fixed_column(), meta.fixed_column()];
        let config = Self {
            from_binary_config,
            q_lookup,
            _marker: PhantomData,
        };

        // Lookup for binary to base-13 conversion
        meta.lookup(|meta| {
            let q_lookup = meta.query_selector(config.q_lookup);
            let binary_slice = meta.query_advice(binary_slice, Rotation::cur());
            let base13_slice =
                meta.query_advice(base13_slice, Rotation::next());

            let key = meta.query_fixed(from_binary_config[0], Rotation::cur());
            let value =
                meta.query_fixed(from_binary_config[1], Rotation::cur());

            vec![
                (q_lookup.clone() * binary_slice, key),
                (q_lookup * base13_slice, value),
            ]
        });
        config
    }

    // Fixed table converting binary to base-13
    fn binary_converter(
        config: Self,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        let [binary_col, base13_col] = config.from_binary_config;

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

                    region.assign_fixed(|| "key", binary_col, i, || Ok(key))?;

                    let value = coefs.iter().fold(F::from_u64(0), |acc, x| {
                        acc * F::from_u64(13) + F::from_u64(*x)
                    });

                    region.assign_fixed(
                        || "value",
                        base13_col,
                        i,
                        || Ok(value),
                    )?;
                }
                Ok(())
            },
        )
    }
}

fn block_counting_function(n: usize) -> u64 {
    let table = [0, 0, 1, 13, 170];
    return table[n];
}

#[derive(Debug)]
pub struct Base13toBase9TableConfig<F> {
    cols: [Column<Fixed>; 3],
    q_lookup: Selector,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> Base13toBase9TableConfig<F> {
    pub(crate) fn load(
        config: Self,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        Self::base13_converter(config, layouter)
    }

    pub(crate) fn configure(
        meta: &mut ConstraintSystem<F>,
        q_lookup: Selector,
        base13_slice: Column<Advice>,
        base9_slice: Column<Advice>,
        block_count: Column<Advice>,
    ) -> Self {
        let cols = [
            meta.fixed_column(),
            meta.fixed_column(),
            meta.fixed_column(),
        ];
        let config = Self {
            cols,
            q_lookup,
            _marker: PhantomData,
        };

        meta.lookup(|meta| {
            let q_lookup = meta.query_selector(q_lookup);
            let base13_slice = meta.query_advice(base13_slice, Rotation::cur());
            let base9_slice = meta.query_advice(base9_slice, Rotation::cur());
            let block_count = meta.query_advice(block_count, Rotation::cur());

            let key = meta.query_fixed(cols[0], Rotation::cur());
            let value = meta.query_fixed(cols[1], Rotation::cur());
            let value2 = meta.query_fixed(cols[2], Rotation::cur());

            vec![
                (q_lookup.clone() * base9_slice, key),
                (q_lookup.clone() * base13_slice, value),
                (q_lookup * block_count, value2),
            ]
        });
        config
    }

    // Fixed table converting base-13 to base-09
    fn base13_converter(
        config: Self,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        let [base13_col, base9_col, block_count_col] = config.cols;

        layouter.assign_region(
            || "from base13",
            |mut region| {
                // Iterate over all possible 13-ary values of size 4
                for (i, coefs) in
                    (0..4).map(|_| 0..13).multi_cartesian_product().enumerate()
                {
                    let key = coefs.iter().fold(F::zero(), |acc, x| {
                        acc * F::from_u64(13) + F::from_u64(*x)
                    });

                    region.assign_fixed(|| "key", base13_col, i, || Ok(key))?;

                    let value = coefs.iter().fold(F::zero(), |acc, x| {
                        acc * F::from_u64(9) + F::from_u64(*x)
                    });

                    region.assign_fixed(
                        || "value",
                        base9_col,
                        i,
                        || Ok(value),
                    )?;
                    // could be 0, 1, 2, 3, 4
                    let non_zero_chunk_count =
                        coefs.iter().filter(|x| **x != 0).count();
                    // could be 0, 0, 1, 13, 170
                    let block_count =
                        block_counting_function(non_zero_chunk_count);
                    region.assign_fixed(
                        || "block_count",
                        block_count_col,
                        i,
                        || Ok(F::from_u64(block_count)),
                    )?;
                }
                Ok(())
            },
        )
    }
}

#[derive(Debug)]
pub struct SpecialChunkTableConfig<F> {
    from_special_chunk_config: [Column<Fixed>; 2],
    _marker: PhantomData<F>,
}

impl<F: FieldExt> SpecialChunkTableConfig<F> {
    pub(crate) fn load(
        config: Self,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        Self::special_chunk_converter(config, layouter)
    }

    pub(crate) fn configure(
        meta: &mut ConstraintSystem<F>,
        high_chunk: Column<Advice>,
        low_chunk: Column<Advice>,
    ) -> Self {
        let from_special_chunk_config =
            [meta.fixed_column(), meta.fixed_column()];

        // Lookup for special chunk conversion
        meta.lookup(|meta| {
            let last_limb_key = meta.query_advice(high_chunk, Rotation::cur());
            let last_limb_value =
                meta.query_advice(low_chunk, Rotation::next());

            let key =
                meta.query_fixed(from_special_chunk_config[0], Rotation::cur());
            let value =
                meta.query_fixed(from_special_chunk_config[1], Rotation::cur());

            vec![(last_limb_key, key), (last_limb_value, value)]
        });
        Self {
            from_special_chunk_config,
            _marker: PhantomData,
        }
    }

    fn special_chunk_converter(
        config: Self,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        let [key_col, value_col] = config.from_special_chunk_config;

        layouter.assign_region(
            || "for special chunks",
            |mut region| {
                // Iterate over all possible values less than 13 for both low
                // and high
                for i in 0..13 {
                    for j in 0..(13 - i) {
                        let low = i;
                        let high = j;

                        let key = F::from_u64(low)
                            + F::from_u64(high)
                                * F::from_u64(13).pow(&[64, 0, 0, 0]);

                        region.assign_fixed(
                            || "key",
                            key_col,
                            i as usize,
                            || Ok(key),
                        )?;

                        let value = convert_b13_coef(low + high);

                        region.assign_fixed(
                            || "value",
                            value_col,
                            i as usize,
                            || Ok(F::from_u64(value)),
                        )?;
                    }
                }
                Ok(())
            },
        )
    }
}
pub struct Base9toBase13BinaryTableConfig<F> {
    cols: [Column<Fixed>; 3],
    q_lookup: Selector,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> Base9toBase13BinaryTableConfig<F> {
    pub(crate) fn load(
        config: Self,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        Self::base9_converter(config, layouter)
    }

    pub(crate) fn configure(
        meta: &mut ConstraintSystem<F>,
        q_lookup: Selector,
        advices: [Column<Advice>; 3],
    ) -> Self {
        let cols = [
            meta.fixed_column(),
            meta.fixed_column(),
            meta.fixed_column(),
        ];
        let config = Self {
            cols,
            q_lookup,
            _marker: PhantomData,
        };

        // Lookup for base-9 to base-13/binary conversion
        meta.lookup(|meta| {
            let q_lookup = meta.query_selector(q_lookup);
            let base9_word = meta.query_advice(advices[0], Rotation::cur());
            let base13_word = meta.query_advice(advices[1], Rotation::next());
            let binary_word = meta.query_advice(advices[2], Rotation::next());

            let key = meta.query_fixed(cols[0], Rotation::cur());
            let value0 = meta.query_fixed(cols[1], Rotation::cur());
            let value1 = meta.query_fixed(cols[2], Rotation::cur());

            vec![
                (q_lookup.clone() * base9_word, key),
                (q_lookup.clone() * base13_word, value0),
                (q_lookup * binary_word, value1),
            ]
        });
        config
    }

    // Fixed table converting base-9 to base-13/binary
    fn base9_converter(
        config: Self,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        let [base9_col, base_13_col, binary_col] = config.cols;

        layouter.assign_region(
            || "from base 9",
            |mut region| {
                // Iterate over all possible 9-ary values of size 4
                for (i, coefs) in
                    (0..4).map(|_| 0..9).multi_cartesian_product().enumerate()
                {
                    let key = coefs.iter().fold(F::zero(), |acc, x| {
                        acc * F::from_u64(9) + F::from_u64(*x)
                    });

                    region.assign_fixed(|| "key", base9_col, i, || Ok(key))?;

                    let value0 = coefs.iter().fold(F::zero(), |acc, x| {
                        acc * F::from_u64(13) + F::from_u64(*x)
                    });

                    region.assign_fixed(
                        || "value0",
                        base_13_col,
                        i,
                        || Ok(value0),
                    )?;

                    let value1 = coefs.iter().fold(F::zero(), |acc, x| {
                        acc * F::from_u64(2) + F::from_u64(*x)
                    });

                    region.assign_fixed(
                        || "value1",
                        binary_col,
                        i,
                        || Ok(value1),
                    )?;
                }
                Ok(())
            },
        )
    }
}
