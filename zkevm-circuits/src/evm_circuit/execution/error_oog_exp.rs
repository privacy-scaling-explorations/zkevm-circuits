use crate::evm_circuit::execution::ExecutionGadget;
use crate::evm_circuit::param::N_BYTES_GAS;
use crate::evm_circuit::step::ExecutionState;
use crate::evm_circuit::util::common_gadget::RestoreContextGadget;
use crate::evm_circuit::util::constraint_builder::Transition::{Delta, Same};
use crate::evm_circuit::util::constraint_builder::{ConstraintBuilder, StepStateTransition};
use crate::evm_circuit::util::math_gadget::{ByteSizeGadget, LtGadget};
use crate::evm_circuit::util::{CachedRegion, Cell, Word};
use crate::evm_circuit::witness::{Block, Call, ExecStep, Transaction};
use crate::table::CallContextFieldTag;
use crate::util::Expr;
use eth_types::evm_types::{GasCost, OpcodeId};
use eth_types::{Field, ToLittleEndian};
use halo2_proofs::circuit::Value;
use halo2_proofs::plonk::Error;

/// Gadget to implement the corresponding out of gas errors for
/// [`OpcodeId::EXP`].
#[derive(Clone, Debug)]
pub(crate) struct ErrorOOGExpGadget<F> {
    opcode: Cell<F>,
    rw_counter_end_of_reversion: Cell<F>,
    base: Word<F>,
    exponent: Word<F>,
    exponent_byte_size: ByteSizeGadget<F>,
    insufficient_gas_cost: LtGadget<F, N_BYTES_GAS>,
    restore_context: RestoreContextGadget<F>,
}

impl<F: Field> ExecutionGadget<F> for ErrorOOGExpGadget<F> {
    const NAME: &'static str = "ErrorOutOfGasEXP";

    const EXECUTION_STATE: ExecutionState = ExecutionState::ErrorOutOfGasEXP;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        let opcode = cb.query_cell();
        cb.opcode_lookup(opcode.expr(), 1.expr());

        cb.require_equal(
            "ErrorOutOfGasEXP opcode must be EXP",
            opcode.expr(),
            OpcodeId::EXP.expr(),
        );

        let base = cb.query_word_rlc();
        let exponent = cb.query_word_rlc();
        cb.stack_pop(base.expr());
        cb.stack_pop(exponent.expr());

        let exponent_byte_size = ByteSizeGadget::construct(cb, &exponent);

        let insufficient_gas_cost = LtGadget::construct(
            cb,
            cb.curr.state.gas_left.expr(),
            // static_gas = 10
            // dynamic_gas = exponent_byte_size * 50
            // gas_cost = dynamic_gas + static_gas
            exponent_byte_size.byte_size() * GasCost::EXP_BYTE_TIMES.0.expr()
                + OpcodeId::EXP.constant_gas_cost().expr(),
        );

        cb.require_equal(
            "Gas left is less than gas cost",
            insufficient_gas_cost.expr(),
            1.expr(),
        );

        // Current call must fail.
        cb.call_context_lookup(false.expr(), None, CallContextFieldTag::IsSuccess, 0.expr());

        let rw_counter_end_of_reversion = cb.query_cell();
        cb.call_context_lookup(
            false.expr(),
            None,
            CallContextFieldTag::RwCounterEndOfReversion,
            rw_counter_end_of_reversion.expr(),
        );

        // Go to EndTx only when is_root.
        let is_to_end_tx = cb.next.execution_state_selector([ExecutionState::EndTx]);
        cb.require_equal(
            "Go to EndTx only when is_root",
            cb.curr.state.is_root.expr(),
            is_to_end_tx,
        );

        // When it's a root call.
        cb.condition(cb.curr.state.is_root.expr(), |cb| {
            // Do step state transition.
            cb.require_step_state_transition(StepStateTransition {
                call_id: Same,
                rw_counter: Delta(4.expr() + cb.curr.state.reversible_write_counter.expr()),
                ..StepStateTransition::any()
            });
        });

        // When it's an internal call, need to restore caller's state as finishing this
        // call. Restore caller state to next StepState.
        let restore_context = cb.condition(1.expr() - cb.curr.state.is_root.expr(), |cb| {
            RestoreContextGadget::construct(
                cb,
                0.expr(),
                0.expr(),
                0.expr(),
                0.expr(),
                0.expr(),
                0.expr(),
            )
        });

        // Constrain RwCounterEndOfReversion.
        let rw_counter_end_of_step =
            cb.curr.state.rw_counter.expr() + cb.rw_counter_offset() - 1.expr();
        cb.require_equal(
            "rw_counter_end_of_reversion = rw_counter_end_of_step + reversible_counter",
            rw_counter_end_of_reversion.expr(),
            rw_counter_end_of_step + cb.curr.state.reversible_write_counter.expr(),
        );

        Self {
            opcode,
            rw_counter_end_of_reversion,
            base,
            exponent,
            exponent_byte_size,
            insufficient_gas_cost,
            restore_context,
        }
    }

    fn assign_exec_step(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        block: &Block<F>,
        _tx: &Transaction,
        call: &Call,
        step: &ExecStep,
    ) -> Result<(), Error> {
        let opcode = step.opcode.unwrap();
        let [base, exponent] = [0, 1].map(|idx| block.rws[step.rw_indices[idx]].stack_value());

        log::debug!(
            "ErrorOutOfGasEXP: gas_left = {}, gas_cost = {}",
            step.gas_left,
            step.gas_cost,
        );

        self.opcode
            .assign(region, offset, Value::known(F::from(opcode.as_u64())))?;
        self.rw_counter_end_of_reversion.assign(
            region,
            offset,
            Value::known(F::from(call.rw_counter_end_of_reversion as u64)),
        )?;
        self.base.assign(region, offset, Some(base.to_le_bytes()))?;
        self.exponent
            .assign(region, offset, Some(exponent.to_le_bytes()))?;
        self.exponent_byte_size.assign(region, offset, exponent)?;
        self.insufficient_gas_cost.assign_value(
            region,
            offset,
            Value::known(F::from(step.gas_left)),
            Value::known(F::from(step.gas_cost)),
        )?;
        self.restore_context
            .assign(region, offset, block, call, step, 4)
    }
}

#[cfg(test)]
mod tests {
    use crate::evm_circuit::test::rand_word;
    use crate::test_util::CircuitTestBuilder;
    use eth_types::evm_types::{GasCost, OpcodeId};
    use eth_types::{bytecode, U256};
    use mock::test_ctx::helpers::account_0_code_account_1_no_code;
    use mock::TestContext;

    #[test]
    fn test_oog_exp() {
        test_ok(U256::zero());
        test_ok(U256::one());
        test_ok(1023.into());
        test_ok(U256::MAX);
        test_ok(rand_word());
    }

    fn test_ok(exponent: U256) {
        let code = bytecode! {
            PUSH32(exponent)
            PUSH32(rand_word())
            EXP
        };

        let gas_cost = OpcodeId::PUSH32.constant_gas_cost().0 * 2
            + OpcodeId::EXP.constant_gas_cost().0
            + ((exponent.bits() as u64 + 7) / 8) * GasCost::EXP_BYTE_TIMES.0;

        let ctx = TestContext::<2, 1>::new(
            None,
            account_0_code_account_1_no_code(code),
            |mut txs, accs| {
                // Decrease expected gas cost (by 1) to trigger out of gas error.
                txs[0]
                    .from(accs[1].address)
                    .to(accs[0].address)
                    .gas((GasCost::TX.0 + gas_cost - 1).into());
            },
            |block, _tx| block.number(0xcafe_u64),
        )
        .unwrap();

        CircuitTestBuilder::new_from_test_ctx(ctx).run();
    }
}
