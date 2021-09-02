


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