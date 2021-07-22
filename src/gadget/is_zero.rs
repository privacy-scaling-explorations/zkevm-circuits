use halo2::{
    circuit::{Chip, Region},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Selector, VirtualCells},
    poly::Rotation,
};
use pasta_curves::arithmetic::FieldExt;
use std::array;

pub(crate) trait IsZeroInstruction<F: FieldExt> {
    /// Given a `value` to be checked if it is zero:
    ///   - witnesses `inv0(value)`, where `inv0(x)` is 0 when `x` = 0,
    ///     and `1/x` otherwise
    fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        value: Option<F>,
    ) -> Result<(), Error>;
}

#[derive(Clone, Debug)]
pub(crate) struct IsZeroConfig<F> {
    pub q_enable: Selector,
    pub value_inv: Column<Advice>,
    /// This can be used directly for custom gate at the offset if `is_zero` is
    /// called, it will be 1 if `value` is zero, and 0 otherwise.
    pub is_zero_expression: Expression<F>,
}

pub(crate) struct IsZeroChip<F> {
    config: IsZeroConfig<F>,
}

impl<F: FieldExt> IsZeroChip<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: Selector,
        value: impl FnOnce(&mut VirtualCells<'_, F>) -> Expression<F>,
    ) -> IsZeroConfig<F> {
        // dummy initialization
        let mut is_zero_expression = Expression::Constant(F::zero());
        let value_inv = meta.advice_column();

        // Truth table of iz_zero gate:
        // +----+-------+-----------+-----------------------+---------------------------------+-------------------------------------+
        // | ok | value | value_inv | 1 - value ⋅ value_inv | value ⋅ (1 - value ⋅ value_inv) | value_inv ⋅ (1 - value ⋅ value_inv) |
        // +----+-------+-----------+-----------------------+---------------------------------+-------------------------------------+
        // | V  | 0     | 0         | 1                     | 0                               | 0                                   |
        // |    | 0     | x         | 1                     | 0                               | x                                   |
        // |    | x     | 0         | 1                     | x                               | 0                                   |
        // | V  | x     | 1/x       | 0                     | 0                               | 0                                   |
        // |    | x     | y         | 1 - xy                | x(1 - xy)                       | y(1 - xy)                           |
        // +----+-------+-----------+-----------------------+---------------------------------+-------------------------------------+
        meta.create_gate("is_zero gate", |meta| {
            let q_enable = meta.query_selector(q_enable);

            let value_inv = meta.query_advice(value_inv, Rotation::cur());
            let value = value(meta);

            let one = Expression::Constant(F::one());
            is_zero_expression = one - value.clone() * value_inv.clone();

            // This checks `value_inv ≡ value.invert()` when `value` is not zero:
            // value ⋅ (1 - value ⋅ value_inv)
            let poly1 = value * is_zero_expression.clone();
            // This checks `value_inv ≡ 0` when `value` is zero:
            // value_inv ⋅ (1 - value ⋅ value_inv)
            let poly2 = value_inv * is_zero_expression.clone();

            array::IntoIter::new([poly1, poly2]).map(move |poly| q_enable.clone() * poly)
        });

        IsZeroConfig::<F> {
            q_enable,
            value_inv,
            is_zero_expression,
        }
    }

    pub fn construct(config: IsZeroConfig<F>) -> Self {
        IsZeroChip { config }
    }
}

impl<F: FieldExt> IsZeroInstruction<F> for IsZeroChip<F> {
    fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        value: Option<F>,
    ) -> Result<(), Error> {
        let config = self.config();

        let value_invert = value.map(|value| value.invert().unwrap_or(F::zero()));
        region.assign_advice(
            || "witness inverse of value",
            config.value_inv,
            offset,
            || value_invert.ok_or(Error::SynthesisError),
        )?;

        Ok(())
    }
}

impl<F: FieldExt> Chip<F> for IsZeroChip<F> {
    type Config = IsZeroConfig<F>;
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
    use super::{IsZeroChip, IsZeroConfig, IsZeroInstruction};
    use halo2::{
        arithmetic::FieldExt,
        circuit::{Layouter, SimpleFloorPlanner},
        dev::{MockProver, VerifyFailure::ConstraintNotSatisfied},
        plonk::{Advice, Circuit, Column, ConstraintSystem, Error},
        poly::Rotation,
    };
    use pasta_curves::pallas::Base;
    use std::marker::PhantomData;

    macro_rules! try_test_circuit {
        ($values:expr, $checks:expr, $result:expr) => {{
            // let k = usize::BITS - $values.len().leading_zeros();

            // TODO: remove zk blinding factors in halo2 to restore the
            // correct k (without the extra + 2).
            let k = usize::BITS - $values.len().leading_zeros() + 2;
            let circuit = TestCircuit::<Base> {
                values: Some($values),
                checks: Some($checks),
                _marker: PhantomData,
            };
            let prover = MockProver::<Base>::run(k, &circuit, vec![]).unwrap();
            assert_eq!(prover.verify(), $result);
        }};
    }

    macro_rules! error_constraint_at_row {
        ($row:expr) => {
            ConstraintNotSatisfied {
                constraint: ((1, "check is_zero").into(), 0, "").into(),
                row: $row,
            }
        };
    }

    #[test]
    fn row_diff_is_zero() {
        #[derive(Clone, Debug)]
        struct TestCircuitConfig<F> {
            value: Column<Advice>,
            check: Column<Advice>,
            is_zero: IsZeroConfig<F>,
        }

        #[derive(Default)]
        struct TestCircuit<F: FieldExt> {
            values: Option<Vec<u64>>,
            // checks[i] = is_zero(values[i + 1] - values[i])
            checks: Option<Vec<bool>>,
            _marker: PhantomData<F>,
        }

        impl<F: FieldExt> Circuit<F> for TestCircuit<F> {
            type Config = TestCircuitConfig<F>;
            type FloorPlanner = SimpleFloorPlanner;

            fn without_witnesses(&self) -> Self {
                Self::default()
            }

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                let q_enable = meta.selector();
                let value = meta.advice_column();
                let check = meta.advice_column();

                let is_zero = IsZeroChip::configure(meta, q_enable, |meta| {
                    let value_prev = meta.query_advice(value, Rotation::prev());
                    let value_cur = meta.query_advice(value, Rotation::cur());
                    value_cur - value_prev
                });

                let config = Self::Config {
                    value,
                    check,
                    is_zero,
                };

                meta.create_gate("check is_zero", |meta| {
                    let q_enable = meta.query_selector(q_enable);

                    // This verifies is_zero is calculated correctly
                    let check = meta.query_advice(config.check, Rotation::cur());

                    vec![q_enable * (config.is_zero.is_zero_expression.clone() - check)]
                });

                config
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<F>,
            ) -> Result<(), Error> {
                let chip = IsZeroChip::construct(config.is_zero.clone());

                let values: Vec<_> = self
                    .values
                    .as_ref()
                    .map(|values| values.iter().map(|value| F::from_u64(*value)).collect())
                    .ok_or(Error::SynthesisError)?;
                let checks = self.checks.as_ref().ok_or(Error::SynthesisError)?;
                let (first_value, values) = values.split_at(1);
                let first_value = first_value[0];

                layouter.assign_region(
                    || "witness",
                    |mut region| {
                        region.assign_advice(
                            || "first row value",
                            config.value,
                            0,
                            || Ok(first_value),
                        )?;

                        let mut value_prev = first_value;
                        for (idx, (value, check)) in values.iter().zip(checks).enumerate() {
                            region.assign_advice(
                                || "check",
                                config.check,
                                idx + 1,
                                || Ok(F::from_u64(*check as u64)),
                            )?;
                            region.assign_advice(
                                || "value",
                                config.value,
                                idx + 1,
                                || Ok(*value),
                            )?;

                            chip.config.q_enable.enable(&mut region, idx + 1)?;
                            chip.assign(&mut region, idx + 1, Some(*value - value_prev))?;

                            value_prev = *value;
                        }

                        Ok(())
                    },
                )
            }
        }

        // ok
        try_test_circuit!(
            vec![1, 2, 3, 4, 5],
            vec![false, false, false, false],
            Ok(())
        );
        try_test_circuit!(
            vec![1, 2, 2, 3, 3], //
            vec![false, true, false, true],
            Ok(())
        );
        // error
        try_test_circuit!(
            vec![1, 2, 3, 4, 5],
            vec![true, true, true, true],
            Err(vec![
                error_constraint_at_row!(1),
                error_constraint_at_row!(2),
                error_constraint_at_row!(3),
                error_constraint_at_row!(4)
            ])
        );
        try_test_circuit!(
            vec![1, 2, 2, 3, 3],
            vec![true, false, true, false],
            Err(vec![
                error_constraint_at_row!(1),
                error_constraint_at_row!(2),
                error_constraint_at_row!(3),
                error_constraint_at_row!(4)
            ])
        );
    }

    #[test]
    fn column_diff_is_zero() {
        #[derive(Clone, Debug)]
        struct TestCircuitConfig<F> {
            value_a: Column<Advice>,
            value_b: Column<Advice>,
            check: Column<Advice>,
            is_zero: IsZeroConfig<F>,
        }

        #[derive(Default)]
        struct TestCircuit<F: FieldExt> {
            values: Option<Vec<(u64, u64)>>,
            // checks[i] = is_zero(values[i].0 - values[i].1)
            checks: Option<Vec<bool>>,
            _marker: PhantomData<F>,
        }

        impl<F: FieldExt> Circuit<F> for TestCircuit<F> {
            type Config = TestCircuitConfig<F>;
            type FloorPlanner = SimpleFloorPlanner;

            fn without_witnesses(&self) -> Self {
                Self::default()
            }

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                let q_enable = meta.selector();
                let (value_a, value_b) = (meta.advice_column(), meta.advice_column());
                let check = meta.advice_column();

                let is_zero = IsZeroChip::configure(meta, q_enable, |meta| {
                    let value_a = meta.query_advice(value_a, Rotation::cur());
                    let value_b = meta.query_advice(value_b, Rotation::cur());
                    value_a - value_b
                });

                let config = Self::Config {
                    value_a,
                    value_b,
                    check,
                    is_zero,
                };

                meta.create_gate("check is_zero", |meta| {
                    let q_enable = meta.query_selector(q_enable);

                    // This verifies is_zero is calculated correctly
                    let check = meta.query_advice(config.check, Rotation::cur());

                    vec![q_enable * (config.is_zero.is_zero_expression.clone() - check)]
                });

                config
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<F>,
            ) -> Result<(), Error> {
                let chip = IsZeroChip::construct(config.is_zero.clone());

                let values: Vec<_> = self
                    .values
                    .as_ref()
                    .map(|values| {
                        values
                            .iter()
                            .map(|(value_a, value_b)| {
                                (F::from_u64(*value_a), F::from_u64(*value_b))
                            })
                            .collect()
                    })
                    .ok_or(Error::SynthesisError)?;
                let checks = self.checks.as_ref().ok_or(Error::SynthesisError)?;

                layouter.assign_region(
                    || "witness",
                    |mut region| {
                        for (idx, ((value_a, value_b), check)) in
                            values.iter().zip(checks).enumerate()
                        {
                            region.assign_advice(
                                || "check",
                                config.check,
                                idx + 1,
                                || Ok(F::from_u64(*check as u64)),
                            )?;
                            region.assign_advice(
                                || "value_a",
                                config.value_a,
                                idx + 1,
                                || Ok(*value_a),
                            )?;
                            region.assign_advice(
                                || "value_b",
                                config.value_b,
                                idx + 1,
                                || Ok(*value_b),
                            )?;

                            chip.config.q_enable.enable(&mut region, idx + 1)?;
                            chip.assign(&mut region, idx + 1, Some(*value_a - *value_b))?;
                        }

                        Ok(())
                    },
                )
            }
        }

        // ok
        try_test_circuit!(
            vec![(1, 2), (3, 4), (5, 6)],
            vec![false, false, false],
            Ok(())
        );
        try_test_circuit!(
            vec![(1, 1), (3, 4), (6, 6)],
            vec![true, false, true],
            Ok(())
        );
        // error
        try_test_circuit!(
            vec![(1, 2), (3, 4), (5, 6)],
            vec![true, true, true],
            Err(vec![
                error_constraint_at_row!(1),
                error_constraint_at_row!(2),
                error_constraint_at_row!(3),
            ])
        );
        try_test_circuit!(
            vec![(1, 1), (3, 4), (6, 6)],
            vec![false, true, false],
            Err(vec![
                error_constraint_at_row!(1),
                error_constraint_at_row!(2),
                error_constraint_at_row!(3),
            ])
        );
    }
}
