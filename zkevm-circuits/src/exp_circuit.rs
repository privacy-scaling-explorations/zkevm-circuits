//! Exponentiation verification circuit.

use eth_types::{Field, ToScalar, U256};
use gadgets::{
    impl_expr,
    mul_add::{MulAddChip, MulAddConfig},
    util::{and, not, or, Expr},
};
use halo2_proofs::{
    circuit::{Layouter, Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed, Selector},
    poly::Rotation,
};
use itertools::Itertools;
use strum_macros::EnumIter;

use crate::{
    evm_circuit::{util::constraint_builder::BaseConstraintBuilder, witness::Block},
    table::{ExpTable, LookupTable},
};

#[derive(Clone, Copy, Debug, EnumIter)]
/// Fixed table to lookup odd or even byte values.
pub enum FixedTableTag {
    /// Represents an odd byte.
    OddByte,
    /// Represents an even byte.
    EvenByte,
}
impl_expr!(FixedTableTag);

impl FixedTableTag {
    /// Build the assignments for the fixed table.
    pub fn build<F: Field>(&self) -> Box<dyn Iterator<Item = [F; 2]>> {
        let tag = F::from(*self as u64);
        match self {
            Self::OddByte => Box::new((1..256).step_by(2).map(move |value| [tag, F::from(value)])),
            Self::EvenByte => Box::new((0..256).step_by(2).map(move |value| [tag, F::from(value)])),
        }
    }
}

/// Layout for the Exponentiation circuit.
#[derive(Clone, Debug)]
pub struct ExpCircuit<F> {
    /// Whether the row is a step.
    pub q_step: Selector,
    /// Whether the row is reserved for padding after an exponentiation trace.
    pub is_pad: Column<Advice>,
    /// Boolean value to indicate whether or not the intermediate exponent value
    /// at this row is odd or even.
    pub is_odd: Column<Advice>,
    /// The Exponentiation circuit's table.
    pub exp_table: ExpTable,
    /// Multiplication gadget for verification of each step.
    pub mul_gadget: MulAddConfig<F>,
    /// Fixed table for odd/even byte values.
    pub fixed_table: [Column<Fixed>; 2],
}

impl<F: Field> ExpCircuit<F> {
    /// Configure the exponentiation circuit.
    pub fn configure(meta: &mut ConstraintSystem<F>, exp_table: ExpTable) -> Self {
        let q_step = meta.complex_selector();
        let is_pad = meta.advice_column();
        let is_odd = meta.advice_column();
        let mul_gadget = MulAddChip::configure(meta, q_step);
        let fixed_table = [(); 2].map(|_| meta.fixed_column());

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
                not::expr(meta.query_advice(exp_table.is_last, Rotation::cur())),
            ]))
        });

        meta.create_gate("verify all steps", |meta| {
            let mut cb = BaseConstraintBuilder::default();

            // both is_first and is_last are boolean values.
            cb.require_boolean(
                "is_first is boolean",
                meta.query_advice(exp_table.is_first, Rotation::cur()),
            );
            cb.require_boolean(
                "is_last is boolean",
                meta.query_advice(exp_table.is_last, Rotation::cur()),
            );
            // first step is followed by either intermediate or padding row.
            cb.require_zero(
                "if is_first::cur is True: is_first::next is False",
                and::expr([
                    meta.query_advice(exp_table.is_first, Rotation::cur()),
                    meta.query_advice(exp_table.is_first, Rotation(7)),
                ]),
            );
            // is_first == 0 following an intermediate step.
            cb.require_zero(
                "if is_first::cur is False then is_first::next is False",
                and::expr([
                    not::expr(meta.query_advice(exp_table.is_first, Rotation::cur())),
                    meta.query_advice(exp_table.is_first, Rotation(7)),
                ]),
            );
            // is_last is True then the following row is reserved for padding.
            cb.require_zero(
                "if is_last::cur is True then is_pad::next is True",
                and::expr([
                    not::expr(meta.query_advice(exp_table.is_last, Rotation::cur())),
                    meta.query_advice(is_pad, Rotation(7)),
                ]),
            );

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

            // The odd/even assignment is boolean.
            cb.require_boolean("is_odd parity is boolean", meta.query_advice(is_odd, Rotation::cur()));

            // remainder == 1 => exponent is odd
            cb.condition(
                and::expr([
                    not::expr(meta.query_advice(exp_table.is_last, Rotation::cur())),
                    meta.query_advice(is_odd, Rotation::cur()),
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
                    not::expr(meta.query_advice(exp_table.is_last, Rotation::cur())),
                    not::expr(meta.query_advice(is_odd, Rotation::cur())),
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

            // For the last step in the exponentiation operation's trace.
            cb.condition(meta.query_advice(exp_table.is_last, Rotation::cur()), |cb| {
                cb.require_equal(
                    "if is_last is True: intermediate_exponent == 2 (lo == 2)",
                    meta.query_advice(exp_table.intermediate_exponent_lo_hi, Rotation::cur()),
                    2.expr(),
                );
                cb.require_zero(
                    "if is_last is True: intermediate_exponent == 2 (hi == 0)",
                    meta.query_advice(exp_table.intermediate_exponent_lo_hi, Rotation::next()),
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

        meta.lookup_any("fixed table (odd) lookup", |meta| {
            let cond = and::expr([
                meta.query_selector(q_step),
                meta.query_advice(is_odd, Rotation::cur()),
            ]);
            vec![
                FixedTableTag::OddByte.expr(),
                meta.query_advice(exp_table.lsb_int_exponent, Rotation::cur()),
            ]
            .into_iter()
            .zip(fixed_table.table_exprs(meta).into_iter())
            .map(|(arg, table)| (cond.clone() * arg, table))
            .collect()
        });

        meta.lookup_any("fixed table (even) lookup", |meta| {
            let cond = and::expr([
                meta.query_selector(q_step),
                not::expr(meta.query_advice(is_odd, Rotation::cur())),
            ]);
            vec![
                FixedTableTag::EvenByte.expr(),
                meta.query_advice(exp_table.lsb_int_exponent, Rotation::cur()),
            ]
            .into_iter()
            .zip(fixed_table.table_exprs(meta).into_iter())
            .map(|(arg, table)| (cond.clone() * arg, table))
            .collect()
        });

        Self {
            q_step,
            is_pad,
            is_odd,
            exp_table,
            mul_gadget,
            fixed_table,
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

        let mul_chip = MulAddChip::construct(self.mul_gadget.clone());

        layouter.assign_region(
            || "exponentiation circuit",
            |mut region| {
                // assign everything except the exp table.
                let mut offset = 0;
                for exp_event in block.exp_events.iter() {
                    let mut exponent = exp_event.exponent;
                    for step in exp_event.steps.iter().rev() {
                        let (exponent_div2, remainder) = exponent.div_mod(2.into());

                        self.q_step.enable(&mut region, offset)?;
                        region.assign_advice(
                            || format!("is_pad: {}", offset),
                            self.is_pad,
                            offset,
                            || Value::known(F::zero()),
                        )?;
                        region.assign_advice(
                            || format!("is_odd: {}", offset),
                            self.is_odd,
                            offset,
                            || Value::known(F::from(remainder.as_u64())),
                        )?;
                        mul_chip.assign(
                            &mut region,
                            offset,
                            [step.a, step.b, U256::zero(), step.d],
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

    /// Load fixed table
    pub fn load_fixed_table(
        &self,
        layouter: &mut impl Layouter<F>,
        fixed_table_tags: Vec<FixedTableTag>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "fixed table",
            |mut region| {
                for (offset, row) in std::iter::once([F::zero(); 2])
                    .chain(fixed_table_tags.iter().flat_map(|tag| tag.build()))
                    .enumerate()
                {
                    for (column, value) in self.fixed_table.iter().zip_eq(row) {
                        region.assign_fixed(|| "", *column, offset, || Value::known(value))?;
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
            config.exp_circuit.load_fixed_table(
                &mut layouter,
                vec![FixedTableTag::OddByte, FixedTableTag::EvenByte],
            )?;
            config
                .exp_circuit
                .assign_block(&mut layouter, &self.block)?;
            Ok(())
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
