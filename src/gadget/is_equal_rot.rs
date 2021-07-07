use crate::gadget::Variable;
use halo2::{
    circuit::{Chip, Region},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Selector, VirtualCells},
    poly::Rotation,
};
use pasta_curves::arithmetic::FieldExt;
use std::marker::PhantomData;

pub(crate) trait IsEqualRotInstruction<F: FieldExt, const R: i32> {
    /// Given an input pair `(value.rot(R), value)`, helps assign `value` and
    /// `(value - value.rot(R)).invert()`, returns variable `value`
    fn is_equal_rot(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        pair: (Variable<F, F>, Option<F>),
    ) -> Result<Variable<F, F>, Error>;
}

#[derive(Clone, Debug)]
pub(crate) struct IsEqualRotConfig {
    pub q_enable: Selector,
    pub value: Column<Advice>,
    pub value_diff_inv: Column<Advice>,
}

pub(crate) struct IsEqualRotChip<F, const R: i32> {
    config: IsEqualRotConfig,
    _marker: PhantomData<F>,
}

pub(crate) type IsEqualPrevChip<F> = IsEqualRotChip<F, -1>;

impl<F: FieldExt, const R: i32> IsEqualRotChip<F, R> {
    /// returns a bool expression of `value === value.rot(R)`
    pub fn is_equal_rot_expression(
        meta: &mut VirtualCells<'_, F>,
        config: &IsEqualRotConfig,
    ) -> Expression<F> {
        let value_cur = meta.query_advice(config.value, Rotation::cur());
        let value_rot = meta.query_advice(config.value, Rotation(R));
        let value_diff_inv_cur = meta.query_advice(config.value_diff_inv, Rotation::cur());
        let value_diff = value_cur - value_rot;

        let one = Expression::Constant(F::one());

        one - value_diff * value_diff_inv_cur
    }

    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: Option<Selector>,
        advices: [Column<Advice>; 2],
    ) -> IsEqualRotConfig {
        let q_enable = q_enable.unwrap_or_else(|| meta.selector());

        let config = IsEqualRotConfig {
            q_enable,
            value: advices[0],
            value_diff_inv: advices[1],
        };

        meta.create_gate(
            "value_diff ⋅ (1 - value_cur ⋅ value_diff_inv) = 0",
            |meta| {
                let q_enable = meta.query_selector(q_enable);

                let one = Expression::Constant(F::one());

                // This checks whether value_diff_inv is valid, which should be inverse of value_diff or zero
                let is_equal_rot = Self::is_equal_rot_expression(meta, &config);
                let inv_check = is_equal_rot.clone() * (one - is_equal_rot);

                vec![q_enable * inv_check]
            },
        );

        config
    }

    pub fn construct(config: IsEqualRotConfig) -> Self {
        IsEqualRotChip {
            config,
            _marker: PhantomData,
        }
    }
}

impl<F: FieldExt, const R: i32> IsEqualRotInstruction<F, R> for IsEqualRotChip<F, R> {
    fn is_equal_rot(
        &self,
        mut region: &mut Region<'_, F>,
        offset: usize,
        (value_rot, value_cur): (Variable<F, F>, Option<F>),
    ) -> Result<Variable<F, F>, Error> {
        let config = self.config();

        config.q_enable.enable(&mut region, offset)?;

        let cell = region.assign_advice(
            || "witness value",
            config.value,
            offset,
            || value_cur.ok_or(Error::SynthesisError),
        )?;

        let value_diff_invert = value_rot
            .value
            .zip(value_cur)
            .map(|(value_rot, value_cur)| (value_cur - value_rot).invert().unwrap_or(F::zero()));

        region.assign_advice(
            || "witness value diff inverse",
            config.value_diff_inv,
            offset,
            || value_diff_invert.ok_or(Error::SynthesisError),
        )?;

        Ok(Variable {
            cell,
            field_elem: value_cur,
            value: value_cur,
        })
    }
}

impl<F: FieldExt, const R: i32> Chip<F> for IsEqualRotChip<F, R> {
    type Config = IsEqualRotConfig;
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
    use super::{IsEqualPrevChip, IsEqualRotConfig, IsEqualRotInstruction};
    use crate::gadget::Variable;
    use halo2::{
        arithmetic::FieldExt,
        circuit::{layouter::SingleChipLayouter, Layouter},
        dev::{MockProver, VerifyFailure},
        plonk::{Advice, Assignment, Circuit, Column, ConstraintSystem, Error},
        poly::Rotation,
    };
    use pasta_curves::pallas::Base;
    use std::marker::PhantomData;

    #[test]
    fn is_equal_prev() {
        #[derive(Clone, Debug)]
        struct TestCircuitConfig {
            check: Column<Advice>,
            is_equal_prev: IsEqualRotConfig,
        }

        struct TestCircuit<F: FieldExt> {
            values: Option<Vec<u64>>,
            // checks[i] = is_zero(values[i] - values[i - 1])
            checks: Option<Vec<bool>>,
            _marker: PhantomData<F>,
        }

        impl<F: FieldExt> Circuit<F> for TestCircuit<F> {
            type Config = TestCircuitConfig;

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                let q_enable = meta.selector();
                let values = [meta.advice_column(), meta.advice_column()];
                let check = meta.advice_column();

                let is_equal_prev = IsEqualPrevChip::configure(meta, Some(q_enable), values);

                let config = Self::Config {
                    check,
                    is_equal_prev,
                };

                meta.create_gate("check is_equal_rot", |meta| {
                    let q_enable = meta.query_selector(q_enable);

                    // This verifies is_equal_prev is calculated correctly
                    let is_equal_prev =
                        IsEqualPrevChip::is_equal_rot_expression(meta, &config.is_equal_prev);
                    let check = meta.query_advice(config.check, Rotation::cur());

                    vec![q_enable * (is_equal_prev - check)]
                });

                config
            }

            fn synthesize(
                &self,
                cs: &mut impl Assignment<F>,
                config: Self::Config,
            ) -> Result<(), Error> {
                let mut layouter = SingleChipLayouter::new(cs)?;
                let chip = IsEqualPrevChip::construct(config.is_equal_prev.clone());

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
                        let cell = region.assign_advice(
                            || "first row value",
                            config.is_equal_prev.value,
                            0,
                            || Ok(first_value),
                        )?;

                        let mut value_prev = Variable {
                            cell,
                            field_elem: Some(first_value),
                            value: Some(first_value),
                        };
                        for (idx, (value, check)) in values.iter().zip(checks).enumerate() {
                            region.assign_advice(
                                || "check",
                                config.check,
                                idx + 1,
                                || Ok(F::from_u64(*check as u64)),
                            )?;

                            // is_equal_rot enables q_enable for us
                            value_prev = chip.is_equal_rot(
                                &mut region,
                                idx + 1,
                                (value_prev, Some(*value)),
                            )?;
                        }

                        Ok(())
                    },
                )
            }
        }

        let try_test_circuit = |values, checks, result| {
            let circuit = TestCircuit::<Base> {
                values: Some(values),
                checks: Some(checks),
                _marker: PhantomData,
            };
            let prover = MockProver::<Base>::run(3, &circuit, vec![]).unwrap();
            assert_eq!(prover.verify(), result);
        };

        try_test_circuit(
            vec![1, 2, 3, 4, 5],
            vec![false, false, false, false],
            Ok(()),
        );
        try_test_circuit(
            vec![1, 2, 2, 3, 3], //
            vec![false, true, false, true],
            Ok(()),
        );
        try_test_circuit(
            vec![1, 2, 3, 4, 5],
            vec![true, false, false, false],
            Err(vec![VerifyFailure::Constraint {
                gate_index: 1,
                gate_name: "check is_equal_rot",
                constraint_index: 0,
                constraint_name: "",
                row: 1,
            }]),
        );
        try_test_circuit(
            vec![1, 2, 2, 3, 3],
            vec![false, false, false, true],
            Err(vec![VerifyFailure::Constraint {
                gate_index: 1,
                gate_name: "check is_equal_rot",
                constraint_index: 0,
                constraint_name: "",
                row: 2,
            }]),
        );
    }
}
