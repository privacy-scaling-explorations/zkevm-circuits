//! Exponentiation verification circuit.

use eth_types::{Field, ToScalar, U256};
use gadgets::{
    is_zero::{IsZeroChip, IsZeroConfig, IsZeroInstruction},
    mul_add::{MulAddChip, MulAddConfig},
    util::{and, not, or, Expr},
};
use halo2_proofs::{
    circuit::{Layouter, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Selector},
    poly::Rotation,
};

use crate::{
    evm_circuit::{util::constraint_builder::BaseConstraintBuilder, witness::Block},
    table::ExpTable,
};

/// Layout for the Exponentiation circuit.
#[derive(Clone, Debug)]
pub struct ExpCircuit<F> {
    /// Whether the row is a step.
    pub q_step: Selector,
    /// The incremental index in the circuit.
    pub idx: Column<Advice>,
    /// To compare whether or not the idx increments.
    pub idx_eq: IsZeroConfig<F>,
    /// Whether this row is the last row in the circuit.
    pub is_last: Column<Advice>,
    /// Multiplication gadget to check that the reducing exponent's division by
    /// 2 was done correctly.
    pub exp_div: MulAddConfig<F>,
    /// The Exponentiation circuit's table.
    pub exp_table: ExpTable,
    /// Multiplication gadget for verification of each step.
    pub mul_gadget: MulAddConfig<F>,
    /// Whether or not the current row is meant for padding.
    pub is_pad: Column<Advice>,
}

impl<F: Field> ExpCircuit<F> {
    /// Configure the exponentiation circuit.
    pub fn configure(meta: &mut ConstraintSystem<F>, exp_table: ExpTable) -> Self {
        let q_step = meta.complex_selector();
        let idx = meta.advice_column();
        let is_last = meta.advice_column();
        let exp_div = MulAddChip::configure(meta, q_step);
        let mul_gadget = MulAddChip::configure(meta, q_step);
        let is_pad = meta.advice_column();

        let diff_inv = meta.advice_column();
        let idx_eq = IsZeroChip::configure(
            meta,
            |meta| meta.query_selector(q_step),
            |meta| meta.query_advice(idx, Rotation(7)) - meta.query_advice(idx, Rotation::cur()),
            diff_inv,
        );

        meta.create_gate("verify all but last steps", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            // base limbs MUST be the same across all steps. Since each step consumes 7 rows
            // (check MulAddChip), we check the current step's rotation `i`
            // against `i + 7`.
            for i in 0..4 {
                cb.require_equal(
                    "base_limb[i] is the same across all steps",
                    meta.query_advice(exp_table.base_limb, Rotation(i)),
                    meta.query_advice(exp_table.base_limb, Rotation(i + 7)),
                );
            }

            // We want to verify that the multiplication result from each step (of
            // exponentiation by squaring) is passed on as the first
            // multiplicand to the next step. Since the steps are assigned in
            // the reverse order, we have: a::cur == d::next.
            //
            // multiplier <- 2^64
            let multiplier: F = U256::from_dec_str("18446744073709551616")
                .unwrap()
                .to_scalar()
                .unwrap();
            let (a_limb0, a_limb1, a_limb2, a_limb3) = (
                meta.query_advice(mul_gadget.col0, Rotation::cur()),
                meta.query_advice(mul_gadget.col1, Rotation::cur()),
                meta.query_advice(mul_gadget.col2, Rotation::cur()),
                meta.query_advice(mul_gadget.col3, Rotation::cur()),
            );
            let a_lo = a_limb0 + (a_limb1 * multiplier);
            let a_hi = a_limb2 + (a_limb3 * multiplier);
            cb.require_equal(
                "multiplication gadget => a::cur == d::next (lo)",
                a_lo,
                meta.query_advice(mul_gadget.col2, Rotation(9)),
            );
            cb.require_equal(
                "multiplication gadget => a::cur == d::next (hi)",
                a_hi,
                meta.query_advice(mul_gadget.col3, Rotation(9)),
            );

            cb.gate(and::expr([
                meta.query_selector(q_step),
                not::expr(meta.query_advice(is_last, Rotation::cur())),
            ]))
        });

        meta.create_gate("verify all steps (excluding padding)", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            // We don't use the exp circuit for exponentiation by 0 or 1, so the first
            // multiplication MUST equal `base*base == base^2`. Since we populate the
            // multiplication gadget in a reverse order, the first multiplication is
            // assigned to the last row.
            cb.condition(meta.query_advice(is_last, Rotation::cur()), |cb| {
                for (i, mul_gadget_col) in [
                    mul_gadget.col0,
                    mul_gadget.col1,
                    mul_gadget.col2,
                    mul_gadget.col3,
                ]
                .into_iter()
                .enumerate()
                {
                    cb.require_equal(
                        "if is_last is True: exp_table.base_limb[i] == mul_gadget.a[i]",
                        meta.query_advice(exp_table.base_limb, Rotation(i as i32)),
                        meta.query_advice(mul_gadget_col, Rotation(0)),
                    );
                    cb.require_equal(
                        "if is_last is True: exp_table.base_limb[i] == mul_gadget.b[i]",
                        meta.query_advice(exp_table.base_limb, Rotation(i as i32)),
                        meta.query_advice(mul_gadget_col, Rotation(1)),
                    );
                }
            });

            // For every step, the intermediate exponentiation MUST equal the result of
            // the corresponding multiplication.
            cb.require_equal(
                "intermediate exponentiation lo == mul_gadget.d_lo",
                meta.query_advice(exp_table.intermediate_exp_lo_hi, Rotation::cur()),
                meta.query_advice(mul_gadget.col2, Rotation(2)),
            );
            cb.require_equal(
                "intermediate exponentiation hi == mul_gadget.d_hi",
                meta.query_advice(exp_table.intermediate_exp_lo_hi, Rotation::next()),
                meta.query_advice(mul_gadget.col3, Rotation(2)),
            );

            // For every step, the MulAddChip's `c` MUST be 0, considering the equation `a *
            // b + c == d` applied ONLY for multiplication.
            cb.require_zero(
                "mul_gadget.c == 0",
                or::expr([
                    meta.query_advice(mul_gadget.col0, Rotation(2)),
                    meta.query_advice(mul_gadget.col1, Rotation(2)),
                ]),
            );

            // The intermediate exponent starts at the exponent, i.e.
            // intermediate_exponent[0] == exponent.
            // For every intermediate step, the intermediate exponent is reduced:
            // 1. intermediate_exponent::next == intermediate_exponent::cur - 1, if odd.
            // 2. intermediate_exponent::next == intermediate_exponent::cur/2, if even.
            let remainder = meta.query_advice(exp_div.col0, Rotation(2));
            cb.require_zero("remainder_hi == 0", meta.query_advice(exp_div.col1, Rotation(2)));
            cb.require_boolean("remainder_lo is 0 or 1", remainder.clone());

            // verify that denominator == 2
            cb.require_zero(
                "denominator_limb[1], [2] and [3] == 0",
                or::expr([
                    meta.query_advice(exp_div.col1, Rotation(1)),
                    meta.query_advice(exp_div.col2, Rotation(1)),
                    meta.query_advice(exp_div.col3, Rotation(1)),
                ]),
            );
            cb.require_equal(
                "denominator_limbs[0] == 2",
                meta.query_advice(exp_div.col0, Rotation(1)),
                2.expr(),
            );

            // verify that `exponent` value was divided by 2.
            for ((column1, rot1), (column2, rot2)) in [
                ((exp_div.col2, Rotation(2)), (exp_table.intermediate_exponent_lo_hi, Rotation(0))),
                ((exp_div.col3, Rotation(2)), (exp_table.intermediate_exponent_lo_hi, Rotation(1))),
            ] {
                cb.require_equal(
                    "intermediate exponent == numerator from exponent division gadget",
                    meta.query_advice(column1, rot1),
                    meta.query_advice(column2, rot2),
                );
            }

            // remainder == 1 => exponent is odd
            cb.condition(
                and::expr([
                    not::expr(meta.query_advice(is_last, Rotation::cur())),
                    remainder.clone(),
                ]), |cb| {
                cb.require_equal(
                    "intermediate_exponent::next == intermediate_exponent::cur - 1 (lo::next == lo::cur - 1)",
                    meta.query_advice(exp_table.intermediate_exponent_lo_hi, Rotation(7)),
                    meta.query_advice(exp_table.intermediate_exponent_lo_hi, Rotation(0)) - 1.expr(),
                );
                cb.require_equal(
                    "intermediate_exponent::next == intermediate_exponent::cur - 1 (hi::next == hi::cur)",
                    meta.query_advice(exp_table.intermediate_exponent_lo_hi, Rotation(8)),
                    meta.query_advice(exp_table.intermediate_exponent_lo_hi, Rotation(1)),
                );
                for (i, mul_gadget_col) in [
                    mul_gadget.col0,
                    mul_gadget.col1,
                    mul_gadget.col2,
                    mul_gadget.col3,
                ]
                .into_iter()
                .enumerate()
                {
                    cb.require_equal(
                        "exp_table.base_limb[i] == mul_gadget.b[i] (intermediate exponent is odd)",
                        meta.query_advice(exp_table.base_limb, Rotation(i as i32)),
                        meta.query_advice(mul_gadget_col, Rotation(1)),
                    );
                }
            });
            // remainder == 0 => exponent is even
            cb.condition(
                and::expr([
                    not::expr(meta.query_advice(is_last, Rotation::cur())),
                    not::expr(remainder),
                ]), |cb| {
                cb.require_equal(
                    "intermediate_exponent::next == intermediate_exponent::cur / 2",
                    meta.query_advice(exp_table.intermediate_exponent_lo_hi, Rotation(0)),
                    meta.query_advice(exp_table.intermediate_exponent_lo_hi, Rotation(7)) * 2.expr(),
                );
                cb.require_equal(
                    "intermediate_exponent::next == intermediate_exponent::cur / 2",
                    meta.query_advice(exp_table.intermediate_exponent_lo_hi, Rotation(1)),
                    meta.query_advice(exp_table.intermediate_exponent_lo_hi, Rotation(8)) * 2.expr(),
                );
                for mul_gadget_col in [
                    mul_gadget.col0,
                    mul_gadget.col1,
                    mul_gadget.col2,
                    mul_gadget.col3,
                ]
                .into_iter()
                {
                    cb.require_equal(
                        "mul_gadget.a[i] == mul_gadget.b[i] (intermediate exponent is even)",
                        meta.query_advice(mul_gadget_col, Rotation(0)),
                        meta.query_advice(mul_gadget_col, Rotation(1)),
                    );
                }
            });

            // If idx does not change
            cb.condition(idx_eq.is_zero_expression.clone(), |cb| {
                cb.require_zero("not the last step", meta.query_advice(is_last, Rotation::cur()));
            });

            // If idx changes
            cb.condition(not::expr(idx_eq.is_zero_expression.clone()), |cb| {
                cb.require_equal(
                    "idx increments by 1",
                    meta.query_advice(idx, Rotation::cur()) + 1.expr(),
                    meta.query_advice(idx, Rotation(7)),
                );
                cb.require_equal(
                    "is the last step",
                    meta.query_advice(is_last, Rotation::cur()),
                    1.expr(),
                );
                cb.require_equal(
                    "if is_last is True: intermediate_exponent == 2 (lo == 2)",
                    meta.query_advice(exp_table.intermediate_exponent_lo_hi, Rotation::cur()),
                    2.expr(),
                );
                cb.require_zero(
                    "if is_last is True: intermediate_exponent == 2 (hi == 0)",
                    meta.query_advice(exp_table.intermediate_exponent_lo_hi, Rotation::next()),
                );
            });

            cb.gate(and::expr([
                meta.query_selector(q_step),
                not::expr(meta.query_advice(is_pad, Rotation::cur())),
            ]))
        });

        Self {
            q_step,
            idx,
            idx_eq,
            is_last,
            exp_div,
            exp_table,
            mul_gadget,
            is_pad,
        }
    }

    /// Assign witness to the exponentiation circuit.
    pub fn assign_block(
        &self,
        layouter: &mut impl Layouter<F>,
        block: &Block<F>,
    ) -> Result<(), Error> {
        const OFFSET_INCREMENT: usize = 7usize;
        const ROWS_PER_STEP: usize = 4usize;

        let exp_div_chip = MulAddChip::construct(self.exp_div.clone());
        let mul_chip = MulAddChip::construct(self.mul_gadget.clone());
        let idx_eq_chip = IsZeroChip::construct(self.idx_eq.clone());

        layouter.assign_region(
            || "exponentiation circuit",
            |mut region| {
                // assign everything except the exp table.
                let mut offset = 0;
                let two = U256::from(2);
                for (idx, exp_event) in block.exp_events.iter().enumerate() {
                    let mut exponent = exp_event.exponent;
                    for (i, step) in exp_event.steps.iter().rev().enumerate() {
                        let is_last = if i == exp_event.steps.len() - 1 {
                            F::one()
                        } else {
                            F::zero()
                        };
                        let (exponent_div2, remainder) = exponent.div_mod(2.into());

                        self.q_step.enable(&mut region, offset)?;
                        region.assign_advice(
                            || format!("idx: {}", offset),
                            self.idx,
                            offset,
                            || Value::known(F::from(idx as u64 + 1)),
                        )?;
                        region.assign_advice(
                            || format!("is_last: {}", offset),
                            self.is_last,
                            offset,
                            || Value::known(is_last),
                        )?;
                        region.assign_advice(
                            || format!("is_pad: {}", offset),
                            self.is_pad,
                            offset,
                            || Value::known(F::zero()),
                        )?;
                        exp_div_chip.assign(
                            &mut region,
                            offset,
                            [exponent_div2, two, remainder, exponent],
                        )?;
                        mul_chip.assign(
                            &mut region,
                            offset,
                            [step.a, step.b, U256::zero(), step.d],
                        )?;
                        idx_eq_chip.assign(&mut region, offset, Value::known(is_last))?;

                        // update reducing exponent
                        if remainder.is_zero() {
                            // exponent is even
                            exponent = exponent_div2;
                        } else {
                            // exponent is odd
                            exponent = exponent - 1;
                        }

                        // mul_chip has 7 rows, exp_table has 4 rows. So we increment the offset by
                        // the maximum number of rows taken up by any gadget within the
                        // exponentiation circuit.
                        offset += OFFSET_INCREMENT;
                    }
                }

                // assign exp table.
                offset = 0usize;
                for exp_event in block.exp_events.iter() {
                    for step_assignments in
                        ExpTable::assignments::<F>(exp_event).chunks_exact(ROWS_PER_STEP)
                    {
                        for (i, assignment) in step_assignments.iter().enumerate() {
                            for (column, value) in self.exp_table.columns().iter().zip(assignment) {
                                region.assign_advice(
                                    || format!("exp circuit: {:?}: {}", *column, offset + i),
                                    *column,
                                    offset + i,
                                    || Value::known(*value),
                                )?;
                            }
                            for column in self.exp_table.columns() {
                                for j in ROWS_PER_STEP..OFFSET_INCREMENT {
                                    region.assign_advice(
                                        || format!("unused rows: {}", offset + j),
                                        column,
                                        offset + j,
                                        || Value::known(F::zero()),
                                    )?;
                                }
                            }
                        }
                        offset += OFFSET_INCREMENT;
                    }
                }

                // assign a zero step, analogous to padding.
                let mut all_columns = self.exp_table.columns();
                all_columns.extend_from_slice(&[
                    self.is_last,
                    self.exp_div.col0,
                    self.exp_div.col1,
                    self.exp_div.col2,
                    self.exp_div.col3,
                ]);
                for column in all_columns {
                    for i in 0..OFFSET_INCREMENT {
                        region.assign_advice(
                            || format!("padding steps: {}", offset + i),
                            column,
                            offset + i,
                            || Value::known(F::zero()),
                        )?;
                    }
                }
                region.assign_advice(
                    || format!("padding step (idx): {}", offset),
                    self.idx,
                    offset,
                    || Value::known(F::from((block.exp_events.len() + 1) as u64)),
                )?;
                region.assign_advice(
                    || format!("padding step (is_pad): {}", offset),
                    self.is_pad,
                    offset,
                    || Value::known(F::one()),
                )?;
                for column in [
                    self.mul_gadget.col0,
                    self.mul_gadget.col1,
                    self.mul_gadget.col2,
                    self.mul_gadget.col3,
                ] {
                    for i in 0..OFFSET_INCREMENT {
                        region.assign_advice(
                            || format!("padding steps: {}", offset + i),
                            column,
                            offset + i,
                            || Value::known(F::zero()),
                        )?;
                    }
                }

                Ok(())
            },
        )
    }
}

#[cfg(any(feature = "test", test))]
/// Dev helpers
pub mod dev {
    use super::*;
    use eth_types::Field;
    use halo2_proofs::{
        circuit::{Layouter, SimpleFloorPlanner},
        dev::{MockProver, VerifyFailure},
        plonk::{Circuit, ConstraintSystem},
    };

    use crate::evm_circuit::witness::Block;

    #[derive(Clone)]
    struct ExpCircuitTesterConfig<F> {
        exp_circuit: ExpCircuit<F>,
    }

    #[derive(Default)]
    struct ExpCircuitTester<F> {
        block: Block<F>,
    }

    impl<F: Field> ExpCircuitTester<F> {
        pub fn new(block: Block<F>) -> Self {
            Self { block }
        }
    }

    impl<F: Field> Circuit<F> for ExpCircuitTester<F> {
        type Config = ExpCircuitTesterConfig<F>;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let exp_table = ExpTable::construct(meta);
            let exp_circuit = ExpCircuit::configure(meta, exp_table);

            ExpCircuitTesterConfig { exp_circuit }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), halo2_proofs::plonk::Error> {
            config.exp_circuit.assign_block(&mut layouter, &self.block)
        }
    }

    /// Test exponentiation circuit with the provided block witness
    pub fn test_exp_circuit<F: Field>(k: u32, block: Block<F>) -> Result<(), Vec<VerifyFailure>> {
        let circuit = ExpCircuitTester::<F>::new(block);
        let prover = MockProver::<F>::run(k, &circuit, vec![]).unwrap();
        prover.verify()
    }
}

#[cfg(test)]
mod tests {
    use bus_mapping::{circuit_input_builder::CircuitInputBuilder, evm::OpcodeId, mock::BlockData};
    use eth_types::{bytecode, geth_types::GethData, Bytecode, Word};
    use mock::TestContext;

    use crate::{evm_circuit::witness::block_convert, exp_circuit::dev::test_exp_circuit};

    fn gen_code_single(base: Word, exponent: Word) -> Bytecode {
        bytecode! {
            PUSH32(exponent)
            PUSH32(base)
            EXP
            STOP
        }
    }

    fn gen_code_multiple(args: Vec<(Word, Word)>) -> Bytecode {
        let mut code = Bytecode::default();
        for (base, exponent) in args.into_iter() {
            code.push(32, exponent);
            code.push(32, base);
            code.write_op(OpcodeId::EXP);
        }
        code.write_op(OpcodeId::STOP);
        code
    }

    fn gen_data(code: Bytecode) -> CircuitInputBuilder {
        let test_ctx = TestContext::<2, 1>::simple_ctx_with_bytecode(code).unwrap();
        let block: GethData = test_ctx.into();
        let mut builder = BlockData::new_from_geth_data(block.clone()).new_circuit_input_builder();
        builder
            .handle_block(&block.eth_block, &block.geth_traces)
            .unwrap();
        builder
    }

    fn test_ok(base: Word, exponent: Word) {
        let code = gen_code_single(base, exponent);
        let builder = gen_data(code);
        let block = block_convert(&builder.block, &builder.code_db);
        assert_eq!(test_exp_circuit(10, block), Ok(()));
    }

    fn test_ok_multiple(args: Vec<(Word, Word)>) {
        let code = gen_code_multiple(args);
        let builder = gen_data(code);
        let block = block_convert(&builder.block, &builder.code_db);
        assert_eq!(test_exp_circuit(20, block), Ok(()));
    }

    #[test]
    fn exp_circuit_single() {
        test_ok(3.into(), 7.into());
        test_ok(5.into(), 11.into());
        test_ok(7.into(), 13.into());
        test_ok(11.into(), 17.into());
        test_ok(13.into(), 23.into());
        test_ok(29.into(), 43.into());
        test_ok(41.into(), 259.into());
    }

    #[test]
    fn exp_circuit_multiple() {
        test_ok_multiple(vec![
            (3.into(), 7.into()),
            (5.into(), 11.into()),
            (7.into(), 13.into()),
        ]);
    }
}
