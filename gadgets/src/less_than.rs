//! Lt chip can be used to compare LT for two expressions LHS and RHS.

use eth_types::Field;
use halo2_proofs::{
    circuit::{Chip, Layouter, Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed, VirtualCells},
    poly::Rotation,
};

use super::{
    bool_check,
    util::{expr_from_bytes, pow_of_two},
};

use chiquito::{
    ast::{query::Queriable, Expr, ToExpr, ToField},
    backend::halo2::{chiquito2Halo2, ChiquitoHalo2},
    compiler::{
        cell_manager::SingleRowCellManager, step_selector::SimpleStepSelectorBuilder, Compiler,
    },
    dsl::{cb::*, circuit},
};

/// Instruction that the Lt chip needs to implement.
pub trait LtInstruction<F: Field> {
    /// Assign the lhs and rhs witnesses to the Lt chip's region.
    fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        lhs: F,
        rhs: F,
    ) -> Result<(), Error>;

    /// Load the u8 lookup table.
    fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error>;
}

// chiquito
fn less_than_circuit<F: Field, const N_BYTES: usize>(
    u8: Column<Fixed>
) -> Circuit<F: Field, (), (u64, u64, bool)> {
    let lt_chip = circuit::<F, (u64, u64, bool), (u64, u64, bool), _>("lt", |ctx| {
        
        let u8 = ctx.import_halo2_fixed("u8", u8);
        ctx.fixed_gen(move |ctx| {
            const RANGE: usize = 256;
            (0..RANGE).map(|idx| {ctx.assign(idx, u8, F::from(idx as u64))});
        });

        let range = pow_of_two(N_BYTES * 8);
        let lt_step = ctx.step_type("lt");
        ctx.step_type_def(lt_step, |ctx| {
            let lhs = ctx.internal("lhs");
            let rhs = ctx.internal("rhs");
            let lt = ctx.internal("lt");
            let diff: Vec<Queriable<F>> = (0..N_BYTES).map(|idx| ctx.internal(format!("diff{idx}").as_str())).collect();
            let q_enable = ctx.internal("q_enable");

            // Multiply all Queriable elements in diff
            let diff_product = diff.iter().fold(Expr::Const(F::from(1)), |acc, x| acc * *x);

            // Set lhs - rhs + lt * range = product of Queriable
            ctx.constr(when(q_enable, eq(lhs - rhs + lt * range, diff_product)));

            // bool value for lt
            ctx.constr(when(q_enable, or(vec![eq(lt, 0u64.expr()), eq(lt, 1u64.expr())])));

            ctx.wg(move |ctx, (lhs_value, rhs_value, q_enable_value)| {
                ctx.assign(lhs, lhs_value.field());
                ctx.assign(rhs, rhs_value.field());
                ctx.assign(q_enable, q_enable_value.field());
                let lt_value = lhs_value < rhs_value;
                ctx.assign(lt, lt_value.field());
                let diff_field = (lhs_value - rhs_value).field() + (if (lt_value) {range} else {0u64.field()});
                let diff_bytes: [F; 32] = diff_field.to_repr().map(|byte| byte.field());
                for(idx, diff) in diff.iter().enumerate() {
                    ctx.assign(*diff, diff_bytes[idx]);
                }    
            });
            
            // lookup for each of the diff columns to constrain them to 0-255
            ctx.add_lookup(diff.iter().fold(&mut lookup::<F>(), |acc, x| acc.add(*x, u8)));
        });

        ctx.trace(move |ctx, (lhs_value, rhs_value, q_enable_value)| {
            ctx.add(&lt_step, (lhs_value, rhs_value, q_enable_value));
        });
    });
}

/// Config for the Lt chip.
#[derive(Clone, Copy, Debug)]
pub struct LtConfig<F, const N_BYTES: usize> {
    /// Denotes the lt outcome. If lhs < rhs then lt == 1, otherwise lt == 0.
    pub lt: Column<Advice>,
    /// Denotes the bytes representation of the difference between lhs and rhs.
    pub diff: [Column<Advice>; N_BYTES], // This array of columns in the advice region stores the bytes representation of the difference between lhs and rhs (lhs - rhs). Each byte of the difference is stored in a separate column.
    /// Denotes the range within which each byte should lie.
    pub u8: Column<Fixed>, // This fixed column in the circuit is used to constrain the values in the diff array to be within the valid u8 range (0 to 255).
    /// Denotes the range within which both lhs and rhs lie.
    pub range: F, // range: This field element is used to denote the valid range for lhs and rhs values. It ensures that the inputs are within the allowed range and that no overflow occurs during the calculation.
}

impl<F: Field, const N_BYTES: usize> LtConfig<F, N_BYTES> {
    /// Returns an expression that denotes whether lhs < rhs, or not.
    pub fn is_lt(&self, meta: &mut VirtualCells<F>, rotation: Option<Rotation>) -> Expression<F> {
        meta.query_advice(self.lt, rotation.unwrap_or_else(Rotation::cur))
    }
}

/// Chip that compares lhs < rhs.
#[derive(Clone, Debug)]
pub struct LtChip<F, const N_BYTES: usize> {
    config: LtConfig<F, N_BYTES>,
}

impl<F: Field, const N_BYTES: usize> LtChip<F, N_BYTES> {
    /// Configures the Lt chip.
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: impl FnOnce(&mut VirtualCells<'_, F>) -> Expression<F>,
        lhs: impl FnOnce(&mut VirtualCells<F>) -> Expression<F>,
        rhs: impl FnOnce(&mut VirtualCells<F>) -> Expression<F>,
    ) -> LtConfig<F, N_BYTES> {
        let lt = meta.advice_column();
        let diff = [(); N_BYTES].map(|_| meta.advice_column());
        let range = pow_of_two(N_BYTES * 8);
        let u8 = meta.fixed_column();

        meta.create_gate("lt gate", |meta| {
            let q_enable = q_enable(meta);
            let lt = meta.query_advice(lt, Rotation::cur());

            let diff_bytes = diff
                .iter()
                .map(|c| meta.query_advice(*c, Rotation::cur()))
                .collect::<Vec<Expression<F>>>();

            // from below: diff = (lhs - rhs) + (if lt { config.range } else { F::ZERO });
            let check_a =
                lhs(meta) - rhs(meta) - expr_from_bytes(&diff_bytes) + (lt.clone() * range); 
                // This gate enforces the constraint that the difference between lhs and rhs plus the result of the "less than" operation (lt) times the range equals the sum of the bytes represented by diff

            let check_b = bool_check(lt);
            // Additionally, it checks that lt is either 0 or 1, ensuring it's a boolean value.

            [check_a, check_b]
                .into_iter()
                .map(move |poly| q_enable.clone() * poly)
        });

        meta.annotate_lookup_any_column(u8, || "LOOKUP_u8");
        // It sets up a range check for each byte in the diff array using the lookup_any method, ensuring that each byte in the diff array is within the range of a valid u8 value.
        diff[0..N_BYTES].iter().for_each(|column| {
            meta.lookup_any("range check for u8", |meta| {
                let u8_cell = meta.query_advice(*column, Rotation::cur());
                let u8_range = meta.query_fixed(u8, Rotation::cur());
                vec![(u8_cell, u8_range)]
            });
        });

        LtConfig {
            lt,
            diff,
            range,
            u8,
        }
    }

    /// Constructs a Lt chip given a config.
    pub fn construct(config: LtConfig<F, N_BYTES>) -> LtChip<F, N_BYTES> {
        LtChip { config }
    }
}

impl<F: Field, const N_BYTES: usize> LtInstruction<F> for LtChip<F, N_BYTES> {
    fn assign( // assign lt result and diff byte columns, given lhs, rhs, and offset
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        lhs: F,
        rhs: F,
    ) -> Result<(), Error> {
        let config = self.config();
        // It computes the boolean result lt of the "less than" operation between lhs and rhs. If lhs is less than rhs, lt will be true; otherwise, it will be false.
        // It assigns the lt value to the config.lt advice column at the given offset.
        let lt = lhs < rhs;
        region.assign_advice(
            || "lt chip: lt",
            config.lt,
            offset,
            || Value::known(F::from(lt as u64)),
        )?;

        let diff = (lhs - rhs) + (if lt { config.range } else { F::ZERO }); // ??? why is diff defined with range? 
        let diff_bytes = diff.to_repr();
        let diff_bytes = diff_bytes.as_ref();
        // It converts diff to its byte representation and assigns each byte to the corresponding advice column in the config.diff array at the given offset.
        for (idx, diff_column) in config.diff.iter().enumerate() { // iterate over config.diff columns and assign diff_bytes
            region.assign_advice(
                || format!("lt chip: diff byte {}", idx),
                *diff_column,
                offset, // same offset as lt result
                || Value::known(F::from(diff_bytes[idx] as u64)),
            )?;
        }

        Ok(())
    }

    fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        const RANGE: usize = 256;

        layouter.assign_region( // assign 256 values to one fixed column u8 to constrain the diff byte values
            || "load u8 range check table",
            |mut region| {
                for i in 0..RANGE {
                    region.assign_fixed(
                        || "assign cell in fixed column",
                        self.config.u8,
                        i,
                        || Value::known(F::from(i as u64)),
                    )?;
                }
                Ok(())
            },
        )
    }
}

impl<F: Field, const N_BYTES: usize> Chip<F> for LtChip<F, N_BYTES> {
    type Config = LtConfig<F, N_BYTES>;
    type Loaded = ();

    fn config(&self) -> &Self::Config { // required method for Chip
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded { // required method for Chip
        &()
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use eth_types::Field;
    use halo2_proofs::{
        circuit::{Layouter, SimpleFloorPlanner, Value},
        dev::MockProver,
        halo2curves::bn256::Fr as Fp,
        plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Selector},
        poly::Rotation,
    };
    use std::marker::PhantomData;

    macro_rules! try_test_circuit {
        ($values:expr, $checks:expr, $result:expr) => {{
            // let k = usize::BITS - $values.len().leading_zeros();

            // TODO: remove zk blinding factors in halo2 to restore the
            // correct k (without the extra + 2).
            let k = 9;
            let circuit = TestCircuit::<Fp> {
                values: Some($values),
                checks: Some($checks),
                _marker: PhantomData,
            };
            // The macro constructs a TestCircuit with the provided values and checks, and then runs the MockProver on it. The MockProver is a test prover that simulates the proving process without actually generating a proof. After the prover has been run, the macro checks if the verification result is equal to the expected result $result.
            let prover = MockProver::<Fp>::run(k, &circuit, vec![]).unwrap();
            assert_eq!(prover.verify(), $result);
        }};
    }

    macro_rules! try_test_circuit_error {
        ($values:expr, $checks:expr) => {{
            // let k = usize::BITS - $values.len().leading_zeros();

            // TODO: remove zk blinding factors in halo2 to restore the
            // correct k (without the extra + 2).
            let k = 9;
            let circuit = TestCircuit::<Fp> {
                values: Some($values),
                checks: Some($checks),
                _marker: PhantomData,
            };
            let prover = MockProver::<Fp>::run(k, &circuit, vec![]).unwrap();
            // Similar to the try_test_circuit macro, this macro constructs a TestCircuit with the provided values and checks and runs the MockProver. However, instead of comparing the verification result to an expected result, this macro checks if the verification result is an error.
            assert!(prover.verify().is_err());
        }};
    }

    #[test]
    fn row_diff_is_lt() {
        #[derive(Clone, Debug)]
        struct TestCircuitConfig<F> {
            q_enable: Selector,
            value: Column<Advice>,
            check: Column<Advice>,
            lt: LtConfig<F, 8>, // 8 bytes for the diff byte vector
        }

        #[derive(Default)]
        struct TestCircuit<F: Field> {
            values: Option<Vec<u64>>,
            // checks[i] = lt(values[i + 1], values[i])
            checks: Option<Vec<bool>>,
            _marker: PhantomData<F>,
        }

        impl<F: Field> Circuit<F> for TestCircuit<F> {
            type Config = TestCircuitConfig<F>;
            type FloorPlanner = SimpleFloorPlanner;

            fn without_witnesses(&self) -> Self {
                Self::default()
            }

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config { // make columns
                let q_enable = meta.complex_selector();
                let value = meta.advice_column();
                let check = meta.advice_column();

                let lt = LtChip::configure(
                    meta,
                    |meta| meta.query_selector(q_enable), // just created above
                    |meta| meta.query_advice(value, Rotation::prev()), // query the same column but different rows corresponding to the vector input
                    |meta| meta.query_advice(value, Rotation::cur()),
                );

                let config = Self::Config {
                    q_enable,
                    value,
                    check,
                    lt,
                };

                meta.create_gate("check is_lt between adjacent rows", |meta| {
                    let q_enable = meta.query_selector(q_enable);

                    // This verifies lt(value::cur, value::next) is calculated correctly
                    let check = meta.query_advice(config.check, Rotation::cur());

                    vec![q_enable * (config.lt.is_lt(meta, None) - check)] // call is_lt (the main function that returns the lt value from the LtChip) with no rotation
                    // ensure check (true false value in vector provided) equals to result generated from lt
                });

                config
            }

            fn synthesize( // assign witnesses
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<F>,
            ) -> Result<(), Error> {
                let chip = LtChip::construct(config.lt); // testcircuitconfig has a lt field which is a ltconfig

                let values: Vec<_> = self
                    .values
                    .as_ref()
                    .map(|values| values.iter().map(|value| F::from(*value)).collect())
                    .ok_or(Error::Synthesis)?;
                let checks = self.checks.as_ref().ok_or(Error::Synthesis)?;
                let (first_value, values) = values.split_at(1);
                let first_value = first_value[0]; // take out first value and the rest values, checks have one element fewer than values

                chip.load(&mut layouter)?;

                layouter.assign_region(
                    || "witness",
                    |mut region| { // q_enable not enabled for the first row
                        region.assign_advice( // no check assigned for first row
                            || "first row value",
                            config.value,
                            0,
                            || Value::known(first_value),
                        )?;

                        let mut value_prev = first_value;
                        for (idx, (value, check)) in values.iter().zip(checks).enumerate() {
                            config.q_enable.enable(&mut region, idx + 1)?; // q_enable enabled for all the rest rows
                            region.assign_advice(
                                || "check",
                                config.check,
                                idx + 1,
                                || Value::known(F::from(*check as u64)),
                            )?;
                            region.assign_advice(
                                || "value",
                                config.value,
                                idx + 1,
                                || Value::known(*value),
                            )?;
                            chip.assign(&mut region, idx + 1, value_prev, *value)?; // ltchip has same offset as the testcircuit, so in the test circuit it's constrained that q_enable * (check - lt) == 0

                            value_prev = *value;
                        }

                        Ok(())
                    },
                )
            }
        }

        // ok
        try_test_circuit!(vec![1, 2, 3, 4, 5], vec![true, true, true, true], Ok(())); // query starting from the second row
        try_test_circuit!(vec![1, 2, 1, 3, 2], vec![true, false, true, false], Ok(()));
        // error
        try_test_circuit_error!(vec![5, 4, 3, 2, 1], vec![true, true, true, true]);
        try_test_circuit_error!(vec![1, 2, 1, 3, 2], vec![false, true, false, true]);
    }

    #[test]
    fn column_diff_is_lt() {
        #[derive(Clone, Debug)]
        struct TestCircuitConfig<F> { // different config from above
            q_enable: Selector,
            value_a: Column<Advice>,
            value_b: Column<Advice>,
            check: Column<Advice>,
            lt: LtConfig<F, 8>,
        }

        #[derive(Default)]
        struct TestCircuit<F: Field> {
            values: Option<Vec<(u64, u64)>>,
            // checks[i] = lt(values[i].0 - values[i].1)
            checks: Option<Vec<bool>>,
            _marker: PhantomData<F>,
        }

        impl<F: Field> Circuit<F> for TestCircuit<F> {
            type Config = TestCircuitConfig<F>;
            type FloorPlanner = SimpleFloorPlanner;

            fn without_witnesses(&self) -> Self {
                Self::default()
            }

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                let q_enable = meta.complex_selector();
                let (value_a, value_b) = (meta.advice_column(), meta.advice_column());
                let check = meta.advice_column();

                let lt = LtChip::configure(
                    meta,
                    |meta| meta.query_selector(q_enable),
                    |meta| meta.query_advice(value_a, Rotation::cur()),
                    |meta| meta.query_advice(value_b, Rotation::cur()),
                );

                let config = Self::Config {
                    q_enable,
                    value_a,
                    value_b,
                    check,
                    lt,
                };

                meta.create_gate("check is_lt between columns in the same row", |meta| {
                    let q_enable = meta.query_selector(q_enable);

                    // This verifies lt(lhs, rhs) is calculated correctly
                    let check = meta.query_advice(config.check, Rotation::cur());

                    vec![q_enable * (config.lt.is_lt(meta, None) - check)]
                });

                config
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<F>,
            ) -> Result<(), Error> {
                let chip = LtChip::construct(config.lt);

                let values: Vec<_> = self
                    .values
                    .as_ref()
                    .map(|values| {
                        values
                            .iter()
                            .map(|(value_a, value_b)| (F::from(*value_a), F::from(*value_b)))
                            .collect()
                    })
                    .ok_or(Error::Synthesis)?;
                let checks = self.checks.as_ref().ok_or(Error::Synthesis)?;

                chip.load(&mut layouter)?;

                layouter.assign_region(
                    || "witness",
                    |mut region| {
                        for (idx, ((value_a, value_b), check)) in
                            values.iter().zip(checks).enumerate()
                        {
                            config.q_enable.enable(&mut region, idx + 1)?;
                            region.assign_advice(
                                || "check",
                                config.check,
                                idx + 1,
                                || Value::known(F::from(*check as u64)),
                            )?;
                            region.assign_advice(
                                || "value_a",
                                config.value_a,
                                idx + 1,
                                || Value::known(*value_a),
                            )?;
                            region.assign_advice(
                                || "value_b",
                                config.value_b,
                                idx + 1,
                                || Value::known(*value_b),
                            )?;
                            chip.assign(&mut region, idx + 1, *value_a, *value_b)?;
                        }

                        Ok(())
                    },
                )
            }
        }

        // ok
        try_test_circuit!(
            vec![(1, 2), (4, 4), (5, 5)],
            vec![true, false, false],
            Ok(())
        );
        try_test_circuit!(
            vec![
                (14124, 14124),
                (383168732, 383168731),
                (383168731, 383168732)
            ],
            vec![false, false, true],
            Ok(())
        );
        // error
        try_test_circuit_error!(vec![(1, 2), (3, 4), (5, 6)], vec![false, false, false]);
        try_test_circuit_error!(vec![(1, 1), (3, 4), (6, 6)], vec![true, false, true]);
    }
}
