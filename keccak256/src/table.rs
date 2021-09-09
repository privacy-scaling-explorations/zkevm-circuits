/*
tables:
- binary to 13 conversion
- 13 to 9 conversion
- special chunk conversion
- 9 to binary and 9 to 13 conversion
*/

pub struct BinaryToBase13TableConfig<F> {
    from_binary_config: [Column<Fixed>; 2]
}


impl<F: FieldExt> BinaryToBase13TableConfig<F> {
    pub(crate) fn load(
        config: Self,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        from_binary_converter(config, layouter);
    }

    pub(crate) fn configure(
        meta: &mut ConstraintSystem<F>,
        advices: [Column<Advice>; 25],
    ) -> Self {
        let from_binary_config = [meta.fixed_column(), meta.fixed_column()];

        for lane in 0..25 {
            // Lookup for binary to base-13 conversion
            meta.lookup(|meta| {
                let word = advices[lane];
                let binary_word = meta.query_advice(word, Rotation::cur());
                let base13_word = meta.query_advice(word, Rotation::next());

                let key = meta.query_fixed(from_binary_config[0], Rotation::cur());
                let value = meta.query_fixed(from_binary_config[1], Rotation::cur());

                vec![
                    (binary_word, key),
                    (base13_word, value),
                ]
            });
        }
        todo!("Add selectors");

    }

    // Fixed table converting binary to base-13
    fn from_binary_converter(
        config: Self,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        let [config] = config.from_binary_config;

        layouter.assign_region(|| "from binary", |mut region| {
            // Iterate over all possible 16-bit values
            for (i, coefs) in (0..16).map(|_| 0..1).multi_cartesian_product().enumerate() {
                let key = coefs.iter().fold(F:from_u64(0), |acc, x| {  acc * 2 + x });

                region.assign_fixed(
                    || "key",
                    config[0],
                    i,
                    || Ok(key)
                )?;
            
                let value = coefs.iter().fold(zero_fr.clone(), |acc, x| {  acc * 13 + x  });

                region.assign_fixed(
                    || "value",
                    config[1],
                    i,
                    || Ok(value)
                )?;
            }
            Ok(())
        })
    }
}

impl<F: FieldExt> Base13toBase9TableConfig<F> {
    pub(crate) fn load(
        config: Self,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        from_base13_converter(config, layouter);
    }

    pub(crate) fn configure(
        meta: &mut ConstraintSystem<F>,
        advices: [Column<Advice>; 25],
    ) -> Self {
        let from_base13_config = [meta.fixed_column(), meta.fixed_column()];

        for lane in 0..25 {
            // Lookup for base-13 to base-9 conversion
            meta.lookup(|meta| {
                let word = advices[lane];
                let base13_word = meta.query_advice(word, Rotation::cur());
                let base9_word = meta.query_advice(word, Rotation::next());

                let key = meta.query_fixed(from_base13_config[0], Rotation::cur());
                let value = meta.query_fixed(from_base13_config[1], Rotation::cur());

                vec![
                    (base13_word, key),
                    (base9_word, value),
                ]
            });
        }
        todo!("Add selectors");

    }

    // Fixed table converting base-13 to base-09
    fn from_base13_converter(
        config: Self,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        let [config] = config.from_base13_config;

        layouter.assign_region(|| "from base13", |mut region| {
            // Iterate over all possible 13-ary values of size 4
            for (i, coefs) in (0..4).map(|_| 0..13).multi_cartesian_product().enumerate() {
                let key = coefs.iter().fold(zero_fr.clone(), |acc, x| {  acc * 13 + x });

                region.assign_fixed(
                    || "key",
                    config[0],
                    i,
                    || Ok(key)
                )?;
            
                let value = coefs.iter().fold(zero_fr.clone(), |acc, x| {  acc * 9 + x  });

                region.assign_fixed(
                    || "value",
                    config[1],
                    i,
                    || Ok(value)
                )?;
            }
            Ok(())
        })
    }
}

impl<F: FieldExt> SpecialChunkTableConfig<F> {
    pub(crate) fn load(
        config: Self,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error>{
        from_special_chunk_converter(config,layouter)
    }

    pub(crate) fn configure(
        meta: &mut ConstraintSystem<F>,
        advices: [Column<Advice>; 25],
    ) -> Self {
        let from_special_chunk_config = [meta.fixed_column(), meta.fixed_column()];

        for lane in 0..25 {
            // Lookup for special chunk conversion
            meta.lookup(|meta| {
                let word = advices[lane];
                let last_limb_key = meta.query_advice(word, Rotation::cur());
                let last_limb_value = meta.query_advice(word, Rotation::next());

                let key = meta.query_fixed(from_special_chunk_config[0], Rotation::cur());
                let value = meta.query_fixed(from_special_chunk_config[1], Rotation::cur());

                vec![
                    (last_limb_key, key),
                    (last_limb_value, value),
                ]
            });
        }
        todo!("Add selectors");

    }

    fn special_chunk_converter(
        config: Self,
        layouter: &mut impl Layouter<F>
    ) -> Result<(), Error> {
        let [config] = config.from_special_chunk_config;

        layouter.assign_region(|| "for special chunks", |mut region| {
            // Iterate over all possible values less than 13 for both low and high
            for i in 0..13{
                for j in 0..(13-i){
                    let low = i;
                    let high = j;

                    let key = low + high * 13**64;

                    region.assign_fixed(
                        || "key",
                        config[0],
                        i,
                        || Ok(key)
                    )?;

                    let value = convert_13_base_limb(low + high)

                    region.assign_fixed(
                        || "value",
                        config[1],
                        i,
                        || Ok(value)
                    )?;
                }
            }
            Ok(())
        })
    }
    }
}

impl<F: FieldExt> Base9toBase13BinaryTableConfig<F> {
    pub(crate) fn load(
        config: Self,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        from_base9_converter(config, layouter);
    }

    pub(crate) fn configure(
        meta: &mut ConstraintSystem<F>,
        advices: [Column<Advice>; 25],
    ) -> Self {
        let from_base9_config = [meta.fixed_column(), meta.fixed_column()];

        for lane in 0..25 {
            // Lookup for base-9 to base-13/binary conversion
            meta.lookup(|meta| {
                let word = advices[lane];
                let base9_word = meta.query_advice(word, Rotation::cur());
                let base13_word = meta.query_advice(word, Rotation::next());
                let binary_word = meta.query_advice(word, Rotation::next());

                let key = meta.query_fixed(from_base9_config[0], Rotation::cur());
                let value0 = meta.query_fixed(from_base9_config[1], Rotation::cur());
                let value1 = meta.query_fixed(from_base9_config[2], Rotation::cur());

                vec![
                    (base9_word, key),
                    (base13_word, value0),
                    (binary_word, value1),
                ]
            });
        }
        todo!("Add selectors");

    }

    // Fixed table converting base-9 to base-13/binary
    fn from_base9_converter(
        config: Self,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        let [config] = config.from_base9_config;

        layouter.assign_region(|| "from base 9", |mut region| {
            // Iterate over all possible 9-ary values of size 4
            for (i, coefs) in (0..4).map(|_| 0..9).multi_cartesian_product().enumerate() {
                let key = coefs.iter().fold(zero_fr.clone(), |acc, x| {  acc * 9 + x });

                region.assign_fixed(
                    || "key",
                    config[0],
                    i,
                    || Ok(key)
                )?;
            
                let value0 = coefs.iter().fold(zero_fr.clone(), |acc, x| {  acc * 13 + x  });

                region.assign_fixed(
                    || "value0",
                    config[1],
                    i,
                    || Ok(value0)
                )?;

                let value1 = coefs.iter().fold(F:from_u64(0), |acc, x| {  acc * 2 + x  });

                region.assign_fixed(
                    || "value1",
                    config[2],
                    i,
                    || Ok(value1)
                )?;
            }
            Ok(())
        })
    }
}

todo!("Add test cases");
