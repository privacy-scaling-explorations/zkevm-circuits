//! Exponentiation verification circuit.

use eth_types::{Field, ToScalar, U256};
use gadgets::{
    mul_add::{MulAddChip, MulAddConfig},
    util::{and, not, or, Expr},
};
use halo2_proofs::{
    circuit::{Layouter, Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Selector},
    poly::Rotation,
};

use crate::{
    evm_circuit::{util::constraint_builder::BaseConstraintBuilder, witness::Block},
    table::ExpTable,
};

/// The number of rows assigned for each step in an exponentiation trace.
pub const OFFSET_INCREMENT: usize = 7usize;
/// The number of rows required for the exponentiation table within the circuit
/// for each step.
pub const ROWS_PER_STEP: usize = 4usize;

/// Layout for the Exponentiation circuit.
#[derive(Clone, Debug)]
pub struct ExpCircuit<F> {
    /// Whether the row is a step.
    pub q_step: Selector,
    /// Whether the row is reserved for padding after an exponentiation trace.
    pub is_pad: Column<Advice>,
    /// The Exponentiation circuit's table.
    pub exp_table: ExpTable,
    /// Multiplication gadget for verification of each step.
    pub mul_gadget: MulAddConfig<F>,
    /// Multiplication gadget to perform 2*n + k.
    pub parity_check: MulAddConfig<F>,
}

impl<F: Field> ExpCircuit<F> {
    /// Configure the exponentiation circuit.
    pub fn configure(meta: &mut ConstraintSystem<F>, exp_table: ExpTable) -> Self {
        let q_step = meta.complex_selector();
        let is_pad = meta.advice_column();
        let mul_gadget = MulAddChip::configure(meta, q_step);
        let parity_check = MulAddChip::configure(meta, q_step);

        // multiplier <- 2^64
        let multiplier: F = U256::from_dec_str("18446744073709551616")
            .unwrap()
            .to_scalar()
            .unwrap();

        meta.create_gate("verify all but the last step", |meta| {
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

            // Identifier does not change over the steps of an exponentiation trace.
            cb.require_equal(
                "identifier does not change",
                meta.query_advice(exp_table.identifier, Rotation::cur()),
                meta.query_advice(exp_table.identifier, Rotation(7)),
            );

            cb.gate(and::expr([
                meta.query_selector(q_step),
                not::expr(meta.query_advice(exp_table.is_last, Rotation::cur())),
            ]))
        });

        meta.create_gate("verify all steps", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            // is_last are boolean values.
            cb.require_boolean(
                "is_last is boolean",
                meta.query_advice(exp_table.is_last, Rotation::cur()),
            );
            // is_pad is boolean.
            cb.require_boolean(
                "is_pad is boolean",
                meta.query_advice(is_pad, Rotation::cur()),
            );
            // is_last is True then the following row is reserved for padding.
            cb.condition(meta.query_advice(exp_table.is_last, Rotation::cur()), |cb| {
                cb.require_equal(
                    "if is_last is True then is_pad::next == 1",
                    meta.query_advice(is_pad, Rotation(7)),
                    1.expr(),
                );
            });
            // is_last is False then the following row is not padding.
            cb.condition(
                not::expr(meta.query_advice(exp_table.is_last, Rotation::cur())),
                |cb| {
                cb.require_zero(
                    "if is_last is False then is_pad::next == 0",
                    meta.query_advice(is_pad, Rotation(7)),
                );
            });

            // For every step, the intermediate exponentiation MUST equal the result of
            // the corresponding multiplication.
            cb.require_equal(
                "intermediate exponentiation lo == mul_gadget.d_lo",
                meta.query_advice(exp_table.exponentiation_lo_hi, Rotation::cur()),
                meta.query_advice(mul_gadget.col2, Rotation(2)),
            );
            cb.require_equal(
                "intermediate exponentiation hi == mul_gadget.d_hi",
                meta.query_advice(exp_table.exponentiation_lo_hi, Rotation::next()),
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

            // The odd/even assignment is boolean.
            cb.require_zero("is_odd is boolean (hi == 0)", meta.query_advice(parity_check.col1, Rotation(2)));
            let is_odd = meta.query_advice(parity_check.col0, Rotation(2));
            cb.require_boolean("is_odd parity is boolean", is_odd.clone());

            // remainder == 1 => exponent is odd
            cb.condition(
                and::expr([
                    not::expr(meta.query_advice(exp_table.is_last, Rotation::cur())),
                    is_odd.clone(),
                ]), |cb| {
                cb.require_equal(
                    "intermediate_exponent::next == intermediate_exponent::cur - 1 (lo::next == lo::cur - 1)",
                    meta.query_advice(exp_table.exponent_lo_hi, Rotation(7)),
                    meta.query_advice(exp_table.exponent_lo_hi, Rotation(0)) - 1.expr(),
                );
                cb.require_equal(
                    "intermediate_exponent::next == intermediate_exponent::cur - 1 (hi::next == hi::cur)",
                    meta.query_advice(exp_table.exponent_lo_hi, Rotation(8)),
                    meta.query_advice(exp_table.exponent_lo_hi, Rotation(1)),
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
                    not::expr(meta.query_advice(exp_table.is_last, Rotation::cur())),
                    not::expr(is_odd),
                ]), |cb| {
                cb.require_equal(
                    "intermediate_exponent::next == intermediate_exponent::cur / 2 (equate cur lo)",
                    meta.query_advice(exp_table.exponent_lo_hi, Rotation(0)),
                    meta.query_advice(parity_check.col2, Rotation(2)),
                );
                cb.require_equal(
                    "intermediate_exponent::next == intermediate_exponent::cur / 2 (equate cur hi)",
                    meta.query_advice(exp_table.exponent_lo_hi, Rotation(1)),
                    meta.query_advice(parity_check.col3, Rotation(2)),
                );
                let (limb0, limb1, limb2, limb3) = (
                    meta.query_advice(parity_check.col0, Rotation(1)),
                    meta.query_advice(parity_check.col1, Rotation(1)),
                    meta.query_advice(parity_check.col2, Rotation(1)),
                    meta.query_advice(parity_check.col3, Rotation(1)),
                );
                let exponent_next_lo = limb0 + (limb1 * multiplier);
                let exponent_next_hi = limb2 + (limb3 * multiplier);
                cb.require_equal(
                    "intermediate_exponent::next == intermediate_exponent::cur / 2 (equate next lo)",
                    meta.query_advice(exp_table.exponent_lo_hi, Rotation(7)),
                    exponent_next_lo,
                );
                cb.require_equal(
                    "intermediate_exponent::next == intermediate_exponent::cur / 2 (equate next hi)",
                    meta.query_advice(exp_table.exponent_lo_hi, Rotation(8)),
                    exponent_next_hi,
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

            // For the last step in the exponentiation operation's trace.
            cb.condition(meta.query_advice(exp_table.is_last, Rotation::cur()), |cb| {
                cb.require_equal(
                    "if is_last is True: intermediate_exponent == 2 (lo == 2)",
                    meta.query_advice(exp_table.exponent_lo_hi, Rotation::cur()),
                    2.expr(),
                );
                cb.require_zero(
                    "if is_last is True: intermediate_exponent == 2 (hi == 0)",
                    meta.query_advice(exp_table.exponent_lo_hi, Rotation::next()),
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

            cb.gate(meta.query_selector(q_step))
        });

        Self {
            q_step,
            is_pad,
            exp_table,
            mul_gadget,
            parity_check,
        }
    }

    /// Assign witness to the exponentiation circuit.
    pub fn assign_block(
        &self,
        layouter: &mut impl Layouter<F>,
        block: &Block<F>,
    ) -> Result<(), Error> {
        let mul_chip = MulAddChip::construct(self.mul_gadget.clone());
        let parity_check_chip = MulAddChip::construct(self.parity_check.clone());

        layouter.assign_region(
            || "exponentiation circuit",
            |mut region| {
                // assign everything except the exp table.
                let mut offset = 0;
                for exp_event in block.exp_events.iter() {
                    let mut exponent = exp_event.exponent;
                    for step in exp_event.steps.iter().rev() {
                        let two = U256::from(2);
                        let (exponent_div2, remainder) = exponent.div_mod(two);

                        self.q_step.enable(&mut region, offset)?;
                        region.assign_advice(
                            || format!("is_pad: {}", offset),
                            self.is_pad,
                            offset,
                            || Value::known(F::zero()),
                        )?;
                        mul_chip.assign(
                            &mut region,
                            offset,
                            [step.a, step.b, U256::zero(), step.d],
                        )?;
                        parity_check_chip.assign(
                            &mut region,
                            offset,
                            [two, exponent_div2, remainder, exponent],
                        )?;

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
                    // Additionally, 1 row is reserved for a padding row at the end of every
                    // exponentiation trace.
                    offset += 1;
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
                    self.assign_padding_row(&mut region, offset)?;
                    offset += 1;
                }

                // assign a zero step, analogous to padding.
                let mut all_columns = self.exp_table.columns();
                all_columns.extend_from_slice(&[
                    self.mul_gadget.col0,
                    self.mul_gadget.col1,
                    self.mul_gadget.col2,
                    self.mul_gadget.col3,
                ]);
                for column in all_columns {
                    for i in 0..(OFFSET_INCREMENT - 1) {
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

    fn assign_padding_row(&self, region: &mut Region<'_, F>, offset: usize) -> Result<(), Error> {
        region.assign_advice(
            || format!("padding row (is_pad): {}", offset),
            self.is_pad,
            offset,
            || Value::known(F::one()),
        )?;

        let mut all_columns = self.exp_table.columns();
        all_columns.extend_from_slice(&[
            self.mul_gadget.col0,
            self.mul_gadget.col1,
            self.mul_gadget.col2,
            self.mul_gadget.col3,
        ]);
        for column in all_columns {
            region.assign_advice(
                || format!("padding steps: {}", offset),
                column,
                offset,
                || Value::known(F::zero()),
            )?;
        }

        Ok(())
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

    fn test_ok(base: Word, exponent: Word, k: Option<u32>) {
        let code = gen_code_single(base, exponent);
        let builder = gen_data(code);
        let block = block_convert(&builder.block, &builder.code_db);
        assert_eq!(test_exp_circuit(k.unwrap_or(10), block), Ok(()));
    }

    fn test_ok_multiple(args: Vec<(Word, Word)>) {
        let code = gen_code_multiple(args);
        let builder = gen_data(code);
        let block = block_convert(&builder.block, &builder.code_db);
        assert_eq!(test_exp_circuit(20, block), Ok(()));
    }

    #[test]
    fn exp_circuit_single() {
        test_ok(3.into(), 7.into(), None);
        test_ok(5.into(), 11.into(), None);
        test_ok(7.into(), 13.into(), None);
        test_ok(11.into(), 17.into(), None);
        test_ok(13.into(), 23.into(), None);
        test_ok(29.into(), 43.into(), None);
        test_ok(41.into(), 259.into(), None);
    }

    #[test]
    fn exp_circuit_big() {
        test_ok(
            2.into(),
            Word::from_str_radix("0x1FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE", 16).unwrap(),
            Some(20),
        );
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
