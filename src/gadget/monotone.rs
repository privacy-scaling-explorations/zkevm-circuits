use halo2::{
    circuit::{Chip, Layouter},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed, VirtualCells},
    poly::Rotation,
};
use pasta_curves::arithmetic::FieldExt;
use std::{marker::PhantomData, u64};

#[derive(Clone, Debug)]
pub(crate) struct MonotoneConfig {
    range_table: Column<Fixed>,
}

/// MonotoneChip helps to check if an advice column is monotone increasing
/// within a range. With strict enabled, it disallows equality of two cell.
pub(crate) struct MonotoneChip<F, const RANGE: usize, const INCR: bool, const STRICT: bool> {
    config: MonotoneConfig,
    _marker: PhantomData<F>,
}

pub(crate) type StrictMonoIncrChip<F, const RANGE: usize> = MonotoneChip<F, RANGE, true, true>;
pub(crate) type NonStrictMonoIncrChip<F, const RANGE: usize> = MonotoneChip<F, RANGE, true, false>;

impl<F: FieldExt, const RANGE: usize, const INCR: bool, const STRICT: bool>
    MonotoneChip<F, RANGE, INCR, STRICT>
{
    /// configure which column should be check. q_enable here as a fn is
    /// flexible for synthetic selector instead of a fixed one.
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: impl FnOnce(&mut VirtualCells<'_, F>) -> Expression<F>,
        value: Column<Advice>,
    ) -> MonotoneConfig {
        let range_table = meta.fixed_column();

        let config = MonotoneConfig { range_table };

        meta.lookup(|meta| {
            let q_enable = q_enable(meta);
            let range_table = meta.query_fixed(config.range_table, Rotation::cur());
            let value_diff = {
                let value_cur = meta.query_advice(value, Rotation::cur());
                let value_prev = meta.query_advice(value, Rotation::prev());
                if INCR {
                    value_cur - value_prev
                } else {
                    value_prev - value_cur
                }
            };

            // If strict monotone, we subtract diff by one
            // to make sure zero lookup fail
            let min_diff = Expression::Constant(F::from_u64(STRICT as u64));

            vec![(q_enable * (value_diff - min_diff), range_table)]
        });

        config
    }

    pub fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_region(
            || "range_table",
            |mut meta| {
                let max = RANGE - STRICT as usize;

                for idx in 0..=max {
                    meta.assign_fixed(
                        || "range_table_value",
                        self.config.range_table,
                        idx,
                        || Ok(F::from_u64(idx as u64)),
                    )?;
                }

                Ok(())
            },
        )
    }

    pub fn construct(config: MonotoneConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }
}

impl<F: FieldExt, const RANGE: usize, const INCR: bool, const STRICT: bool> Chip<F>
    for MonotoneChip<F, RANGE, INCR, STRICT>
{
    type Config = MonotoneConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

#[cfg(test)]
mod test {
    use super::{MonotoneConfig, NonStrictMonoIncrChip, StrictMonoIncrChip};
    use halo2::{
        arithmetic::FieldExt,
        circuit::{layouter::SingleChipLayouter, Layouter},
        dev::{
            MockProver,
            VerifyFailure::{self, Lookup},
        },
        plonk::{Advice, Assignment, Circuit, Column, ConstraintSystem, Error, Selector},
    };
    use pasta_curves::pallas::Base;
    use std::marker::PhantomData;

    #[test]
    fn mono_incr() {
        #[derive(Clone, Debug)]
        struct TestCircuitConfig {
            q_enable: Selector,
            value: Column<Advice>,
            strict_mono_incr: MonotoneConfig,
            non_strict_mono_incr: MonotoneConfig,
        }

        struct TestCircuit<F: FieldExt, const RANGE: usize> {
            values: Option<Vec<u64>>,
            _marker: PhantomData<F>,
        }

        impl<F: FieldExt, const RANGE: usize> Circuit<F> for TestCircuit<F, RANGE> {
            type Config = TestCircuitConfig;

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                let q_enable = meta.selector();
                let value = meta.advice_column();

                let strict_mono_incr = StrictMonoIncrChip::<F, RANGE>::configure(
                    meta,
                    |meta| meta.query_selector(q_enable),
                    value,
                );
                let non_strict_mono_incr = NonStrictMonoIncrChip::<F, RANGE>::configure(
                    meta,
                    |meta| meta.query_selector(q_enable),
                    value,
                );

                let config = Self::Config {
                    q_enable,
                    value,
                    strict_mono_incr,
                    non_strict_mono_incr,
                };

                config
            }

            fn synthesize(
                &self,
                cs: &mut impl Assignment<F>,
                config: Self::Config,
            ) -> Result<(), Error> {
                let mut layouter = SingleChipLayouter::new(cs)?;
                let strict_monotone_chip =
                    StrictMonoIncrChip::<F, RANGE>::construct(config.strict_mono_incr.clone());
                let non_strict_monotone_chip = NonStrictMonoIncrChip::<F, RANGE>::construct(
                    config.non_strict_mono_incr.clone(),
                );

                strict_monotone_chip.load(&mut layouter)?;
                non_strict_monotone_chip.load(&mut layouter)?;

                let values: Vec<_> = self
                    .values
                    .as_ref()
                    .map(|values| values.iter().map(|value| F::from_u64(*value)).collect())
                    .ok_or(Error::SynthesisError)?;

                layouter.assign_region(
                    || "witness",
                    |mut region| {
                        for (idx, value) in values.iter().enumerate() {
                            region.assign_advice(|| "value", config.value, idx, || Ok(*value))?;
                            if idx > 0 {
                                config.q_enable.enable(&mut region, idx)?;
                            }
                        }

                        Ok(())
                    },
                )
            }
        }

        fn try_test_circuit<const RANGE: usize>(
            values: Vec<u64>,
            result: Result<(), Vec<VerifyFailure>>,
        ) {
            let circuit = TestCircuit::<Base, RANGE> {
                values: Some(values),
                _marker: PhantomData,
            };
            let prover =
                MockProver::<Base>::run(usize::BITS - RANGE.leading_zeros(), &circuit, vec![])
                    .unwrap();
            assert_eq!(prover.verify(), result);
        }

        // both succeed
        try_test_circuit::<100>(vec![1, 2, 3, 4, 104], Ok(()));
        try_test_circuit::<100>(vec![1001, 1002, 1003, 1004, 1104], Ok(()));
        // strict monotone fails (equal)
        try_test_circuit::<100>(
            vec![1, 2, 2, 4, 4],
            Err(vec![
                Lookup {
                    lookup_index: 0,
                    row: 2,
                },
                Lookup {
                    lookup_index: 0,
                    row: 4,
                },
            ]),
        );
        // both fail (out of range)
        try_test_circuit::<100>(
            vec![1, 2, 3, 4, 105],
            Err(vec![
                Lookup {
                    lookup_index: 0,
                    row: 4,
                },
                Lookup {
                    lookup_index: 1,
                    row: 4,
                },
            ]),
        );
        // both fails (not monotone)
        try_test_circuit::<100>(
            vec![1, 2, 3, 103, 4],
            Err(vec![
                Lookup {
                    lookup_index: 0,
                    row: 4,
                },
                Lookup {
                    lookup_index: 1,
                    row: 4,
                },
            ]),
        );
    }
}
