use bus_mapping::evm::OpcodeId;
use eth_types::{evm_types::GasCost, Field, ToScalar, U256};
use gadgets::util::{and, not, split_u256, Expr};
use halo2_proofs::{
    circuit::Value,
    plonk::{Error, Expression},
};

use crate::{
    evm_circuit::{
        step::ExecutionState,
        util::{
            common_gadget::SameContextGadget,
            constraint_builder::{
                ConstrainBuilderCommon, EVMConstraintBuilder, StepStateTransition, Transition,
            },
            math_gadget::{ByteSizeGadget, IsEqualGadget, IsZeroGadget},
            CachedRegion, Cell,
        },
        witness::{Block, Call, Chunk, ExecStep, Transaction},
    },
    util::word::{Word32Cell, Word4, WordExpr},
};

use super::ExecutionGadget;

#[derive(Clone, Debug)]
pub(crate) struct ExponentiationGadget<F> {
    /// Gadget to check that we stay within the same context.
    same_context: SameContextGadget<F>,
    /// RLC-encoded integer base that will be exponentiated.
    base: Word32Cell<F>,
    /// RLC-encoded representation for base * base, i.e. base^2
    base_sq: Word32Cell<F>,
    /// RLC-encoded exponent for the exponentiation operation.
    exponent: Word32Cell<F>,
    /// RLC-encoded result of the exponentiation.
    exponentiation: Word32Cell<F>,
    /// Gadget to check if low 128-bit part of exponent is zero or not.
    exponent_lo_is_zero: IsZeroGadget<F>,
    /// Gadget to check if high 128-bit part of exponent is zero or not.
    exponent_hi_is_zero: IsZeroGadget<F>,
    /// Gadget to check if low 128-bit part of exponent is one or not.
    exponent_lo_is_one: IsEqualGadget<F>,
    /// Whether there is a single step in the exponentiation trace.
    single_step: Cell<F>,
    /// Gadget to check the byte-size of exponent.
    exponent_byte_size: ByteSizeGadget<F>,
}

impl<F: Field> ExecutionGadget<F> for ExponentiationGadget<F> {
    const NAME: &'static str = "EXP";

    const EXECUTION_STATE: ExecutionState = ExecutionState::EXP;

    fn configure(cb: &mut EVMConstraintBuilder<F>) -> Self {
        let opcode = cb.query_cell();

        // Query RLC-encoded values for base, exponent and exponentiation, where:
        // base^exponent == exponentiation (mod 2^256).
        let base = cb.query_word32();
        let exponent = cb.query_word32();
        let exponentiation = cb.query_word32();

        // Pop RLC-encoded base and exponent from the stack.
        cb.stack_pop(base.to_word());
        cb.stack_pop(exponent.to_word());

        // Push RLC-encoded exponentiation to the stack.
        cb.stack_push(exponentiation.to_word());

        // Extract low and high bytes of the base.
        let (base_lo, base_hi) = base.to_word().to_lo_hi();
        // Extract low and high bytes of the exponent.
        let (exponent_lo, exponent_hi) = exponent.to_word().to_lo_hi();
        // Extract low and high bytes of the exponentiation result.
        let (exponentiation_lo, exponentiation_hi) = exponentiation.to_word().to_lo_hi();

        // We simplify constraints depending on whether or not the exponent is 0 or 1.
        // In order to do this, we build some utility expressions.
        let exponent_lo_is_zero = cb.is_zero(exponent_lo.clone());
        let exponent_hi_is_zero = cb.is_zero(exponent_hi.clone());
        let exponent_is_zero_expr =
            and::expr([exponent_lo_is_zero.expr(), exponent_hi_is_zero.expr()]);
        let exponent_lo_is_one = cb.is_eq(exponent_lo.clone(), 1.expr());
        let exponent_is_one_expr =
            and::expr([exponent_lo_is_one.expr(), exponent_hi_is_zero.expr()]);

        let base_sq = cb.query_word32();

        // If exponent == 0, base^exponent == 1, which implies:
        // 1. Low bytes of exponentiation == 1
        // 2. High bytes of exponentiation == 0
        cb.condition(exponent_is_zero_expr.clone(), |cb| {
            cb.require_equal(
                "exponentiation == 1 if exponent == 0 (lo == 1)",
                exponentiation_lo.clone(),
                1.expr(),
            );
            cb.require_equal(
                "exponentiation == 1 if exponent == 0 (hi == 0)",
                exponentiation_hi.clone(),
                0.expr(),
            );
        });
        // If exponent == 1, base^exponent == base, which implies:
        // 1. Low bytes of exponentiation == low bytes of base.
        // 2. High bytes of exponentiation == high bytes of base.
        cb.condition(exponent_is_one_expr.clone(), |cb| {
            cb.require_equal(
                "exponentiation == base if exponent == 1 (lo)",
                exponentiation_lo.clone(),
                base_lo.clone(),
            );
            cb.require_equal(
                "exponentiation == base if exponent == 1 (hi)",
                exponentiation_hi.clone(),
                base_hi.clone(),
            );
        });
        // If exponent > 1, i.e. exponent != 0 && exponent != 1:
        // We do two lookups to the exponentiation table. If exponent == 2, there is
        // only a single step in the exponentiation by squaring trace. In this
        // case, is_first == is_last == true for that step.
        let single_step = cb.query_cell();
        cb.condition(
            and::expr([
                not::expr(exponent_is_zero_expr),
                not::expr(exponent_is_one_expr),
            ]),
            |cb| {
                let base_limbs: Word4<Expression<F>> = base.to_word_n();
                let (base_sq_lo, base_sq_hi) = base_sq.to_word().to_lo_hi();
                let identifier = cb.curr.state.rw_counter.expr() + cb.rw_counter_offset();
                // lookup for first step, i.e.
                // (is_last, base, exponent, exponentiation)
                cb.exp_table_lookup(
                    identifier.clone(),
                    single_step.expr(),
                    base_limbs.limbs.clone(),
                    [exponent_lo.clone(), exponent_hi.clone()],
                    [exponentiation_lo.clone(), exponentiation_hi.clone()],
                );
                // lookup for last step, i.e. (is_last, base, 2, base^2)
                cb.exp_table_lookup(
                    identifier,
                    1.expr(),
                    base_limbs.limbs,
                    [2.expr(), 0.expr()], // exponent == 2
                    [base_sq_lo.expr(), base_sq_hi.expr()],
                );
            },
        );

        // In order to calculate the dynamic gas cost of the exponentiation operation,
        // we need the byte-size of the exponent, i.e. the minimum number of
        // bytes that can represent the exponent value.
        let exponent_byte_size = ByteSizeGadget::construct(cb, exponent.to_word_n().limbs);

        // Finally we build an expression for the dynamic gas cost as:
        // dynamic_gas = 50 * exponent_byte_size
        let dynamic_gas_cost = GasCost::EXP_BYTE_TIMES.expr() * exponent_byte_size.byte_size();
        let step_state_transition = StepStateTransition {
            rw_counter: Transition::Delta(3.expr()), // 2 stack pops, 1 stack push
            program_counter: Transition::Delta(1.expr()),
            stack_pointer: Transition::Delta(1.expr()),
            gas_left: Transition::Delta(
                // gas_cost = static_gas (10) + dynamic_gas
                -OpcodeId::EXP.constant_gas_cost().expr() - dynamic_gas_cost,
            ),
            ..Default::default()
        };
        let same_context = SameContextGadget::construct(cb, opcode, step_state_transition);

        Self {
            same_context,
            base,
            base_sq,
            exponent,
            exponentiation,
            exponent_lo_is_zero,
            exponent_hi_is_zero,
            exponent_lo_is_one,
            single_step,
            exponent_byte_size,
        }
    }

    fn assign_exec_step(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        block: &Block<F>,
        _chunk: &Chunk<F>,
        _tx: &Transaction,
        _call: &Call,
        step: &ExecStep,
    ) -> Result<(), Error> {
        self.same_context.assign_exec_step(region, offset, step)?;

        let [base, exponent, exponentiation] =
            [0, 1, 2].map(|index| block.get_rws(step, index).stack_value());

        self.base.assign_u256(region, offset, base)?;
        self.exponent.assign_u256(region, offset, exponent)?;
        self.exponentiation
            .assign_u256(region, offset, exponentiation)?;

        let (exponent_lo, exponent_hi) = split_u256(&exponent);
        let exponent_lo_scalar = exponent_lo
            .to_scalar()
            .expect("exponent lo should fit into scalar");
        let exponent_hi_scalar = exponent_hi
            .to_scalar()
            .expect("exponent hi should fit into scalar");
        self.exponent_lo_is_zero
            .assign(region, offset, exponent_lo_scalar)?;
        self.exponent_hi_is_zero
            .assign(region, offset, exponent_hi_scalar)?;
        self.exponent_lo_is_one
            .assign(region, offset, exponent_lo_scalar, F::ONE)?;

        let (base_sq, _) = base.overflowing_mul(base);
        self.base_sq.assign_u256(region, offset, base_sq)?;
        let single_step = exponent.eq(&U256::from(2u64));
        self.single_step
            .assign(region, offset, Value::known(F::from(single_step as u64)))?;

        self.exponent_byte_size.assign(region, offset, exponent)?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::test_util::CircuitTestBuilder;
    use eth_types::{bytecode, Word};
    use mock::TestContext;

    fn test_ok(base: Word, exponent: Word) {
        let code = bytecode! {
            PUSH32(exponent)
            PUSH32(base)
            EXP
            STOP
        };
        CircuitTestBuilder::new_from_test_ctx(
            TestContext::<2, 1>::simple_ctx_with_bytecode(code).unwrap(),
        )
        .run();
    }

    #[test]
    fn exp_gadget_zero() {
        test_ok(Word::zero(), Word::zero());
        test_ok(Word::one(), Word::zero());
        test_ok(0xcafeu64.into(), Word::zero());
        test_ok(Word::MAX, Word::zero());
    }

    #[test]
    fn exp_gadget_one() {
        test_ok(Word::zero(), Word::one());
        test_ok(Word::one(), Word::one());
        test_ok(0xcafeu64.into(), Word::one());
        test_ok(Word::MAX, Word::one());
    }

    #[test]
    fn exp_gadget_simple() {
        test_ok(2.into(), 5.into());
        test_ok(
            2.into(),
            Word::from_str_radix("0x200000000000000000000000000000000", 16).unwrap(),
        );
        test_ok(3.into(), 101.into());
        test_ok(5.into(), 259.into());
        test_ok(7.into(), 1023.into());
        test_ok(Word::MAX, 2.into());
        test_ok(Word::MAX, 3.into());
    }
}
