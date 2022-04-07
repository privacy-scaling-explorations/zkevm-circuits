use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        step::ExecutionState,
        table::CallContextFieldTag,
        util::{
            common_gadget::SameContextGadget,
            constraint_builder::{
                ConstraintBuilder, ReversionInfo, StepStateTransition, Transition::Delta,
            },
            math_gadget::{IsEqualGadget, IsZeroGadget},
            not, select, Cell, Word,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    util::Expr,
};
use eth_types::{evm_types::GasCost, Field, ToLittleEndian, ToScalar};
use halo2_proofs::{
    circuit::Region,
    plonk::{Error, Expression},
};

#[derive(Clone, Debug)]
pub(crate) struct SstoreGadget<F> {
    same_context: SameContextGadget<F>,
    tx_id: Cell<F>,
    reversion_info: ReversionInfo<F>,
    callee_address: Cell<F>,
    key: Cell<F>,
    value: Cell<F>,
    value_prev: Cell<F>,
    original_value: Cell<F>,
    is_warm: Cell<F>,
    tx_refund_prev: Cell<F>,
    gas_cost: SstoreGasGadget<F>,
    tx_refund: SstoreTxRefundGadget<F>,
}

impl<F: Field> ExecutionGadget<F> for SstoreGadget<F> {
    const NAME: &'static str = "SSTORE";

    const EXECUTION_STATE: ExecutionState = ExecutionState::SSTORE;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        let opcode = cb.query_cell();

        let tx_id = cb.call_context(None, CallContextFieldTag::TxId);
        let mut reversion_info = cb.reversion_info(None);
        let callee_address = cb.call_context(None, CallContextFieldTag::CalleeAddress);

        let key = cb.query_cell();
        // Pop the key from the stack
        cb.stack_pop(key.expr());

        let value = cb.query_cell();
        // Pop the value from the stack
        cb.stack_pop(value.expr());

        let value_prev = cb.query_cell();
        let original_value = cb.query_cell();
        cb.account_storage_write(
            callee_address.expr(),
            key.expr(),
            value.expr(),
            value_prev.expr(),
            tx_id.expr(),
            original_value.expr(),
            Some(&mut reversion_info),
        );

        let is_warm = cb.query_bool();
        cb.account_storage_access_list_write(
            tx_id.expr(),
            callee_address.expr(),
            key.expr(),
            true.expr(),
            is_warm.expr(),
            Some(&mut reversion_info),
        );

        let gas_cost = SstoreGasGadget::construct(
            cb,
            value.clone(),
            value_prev.clone(),
            original_value.clone(),
            is_warm.clone(),
        );

        let tx_refund_prev = cb.query_cell();
        let tx_refund = SstoreTxRefundGadget::construct(
            cb,
            tx_refund_prev.clone(),
            value.clone(),
            value_prev.clone(),
            original_value.clone(),
        );
        cb.tx_refund_write(
            tx_id.expr(),
            tx_refund.expr(),
            tx_refund_prev.expr(),
            Some(&mut reversion_info),
        );

        let step_state_transition = StepStateTransition {
            rw_counter: Delta(9.expr()),
            program_counter: Delta(1.expr()),
            stack_pointer: Delta(2.expr()),
            reversible_write_counter: Delta(3.expr()),
            gas_left: Delta(-gas_cost.expr()),
            ..Default::default()
        };
        let same_context = SameContextGadget::construct(cb, opcode, step_state_transition);

        Self {
            same_context,
            tx_id,
            reversion_info,
            callee_address,
            key,
            value,
            value_prev,
            original_value,
            is_warm,
            tx_refund_prev,
            gas_cost,
            tx_refund,
        }
    }

    fn assign_exec_step(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        block: &Block<F>,
        tx: &Transaction,
        call: &Call,
        step: &ExecStep,
    ) -> Result<(), Error> {
        self.same_context.assign_exec_step(region, offset, step)?;

        self.tx_id
            .assign(region, offset, Some(F::from(tx.id as u64)))?;
        self.reversion_info.assign(
            region,
            offset,
            call.rw_counter_end_of_reversion,
            call.is_persistent,
        )?;
        self.callee_address
            .assign(region, offset, call.callee_address.to_scalar())?;

        let [key, value] =
            [step.rw_indices[4], step.rw_indices[5]].map(|idx| block.rws[idx].stack_value());
        self.key.assign(
            region,
            offset,
            Some(Word::random_linear_combine(
                key.to_le_bytes(),
                block.randomness,
            )),
        )?;
        self.value.assign(
            region,
            offset,
            Some(Word::random_linear_combine(
                value.to_le_bytes(),
                block.randomness,
            )),
        )?;

        let (_, value_prev, _, original_value) = block.rws[step.rw_indices[6]].storage_value_aux();
        self.value_prev.assign(
            region,
            offset,
            Some(Word::random_linear_combine(
                value_prev.to_le_bytes(),
                block.randomness,
            )),
        )?;
        self.original_value.assign(
            region,
            offset,
            Some(Word::random_linear_combine(
                original_value.to_le_bytes(),
                block.randomness,
            )),
        )?;

        let (_, is_warm) = block.rws[step.rw_indices[7]].tx_access_list_value_pair();
        self.is_warm
            .assign(region, offset, Some(F::from(is_warm as u64)))?;

        let (tx_refund, tx_refund_prev) = block.rws[step.rw_indices[8]].tx_refund_value_pair();
        self.tx_refund_prev
            .assign(region, offset, Some(F::from(tx_refund_prev)))?;

        self.gas_cost.assign(
            region,
            offset,
            step.gas_cost,
            value,
            value_prev,
            original_value,
            is_warm,
            block.randomness,
        )?;

        self.tx_refund.assign(
            region,
            offset,
            tx_refund,
            tx_refund_prev,
            value,
            value_prev,
            original_value,
            block.randomness,
        )?;
        Ok(())
    }
}

#[derive(Clone, Debug)]
pub(crate) struct SstoreGasGadget<F> {
    value: Cell<F>,
    value_prev: Cell<F>,
    original_value: Cell<F>,
    is_warm: Cell<F>,
    gas_cost: Expression<F>,
    value_eq_prev: IsEqualGadget<F>,
    original_eq_prev: IsEqualGadget<F>,
    original_is_zero: IsZeroGadget<F>,
}

impl<F: Field> SstoreGasGadget<F> {
    pub(crate) fn construct(
        cb: &mut ConstraintBuilder<F>,
        value: Cell<F>,
        value_prev: Cell<F>,
        original_value: Cell<F>,
        is_warm: Cell<F>,
    ) -> Self {
        let value_eq_prev = IsEqualGadget::construct(cb, value.expr(), value_prev.expr());
        let original_eq_prev =
            IsEqualGadget::construct(cb, original_value.expr(), value_prev.expr());
        let original_is_zero = IsZeroGadget::construct(cb, original_value.expr());
        let warm_case_gas = select::expr(
            value_eq_prev.expr(),
            GasCost::WARM_ACCESS.expr(),
            select::expr(
                original_eq_prev.expr(),
                select::expr(
                    original_is_zero.expr(),
                    GasCost::SSTORE_SET.expr(),
                    GasCost::SSTORE_RESET.expr(),
                ),
                GasCost::WARM_ACCESS.expr(),
            ),
        );
        let gas_cost = select::expr(
            is_warm.expr(),
            warm_case_gas.expr(),
            warm_case_gas + GasCost::COLD_SLOAD.expr(),
        );

        Self {
            value,
            value_prev,
            original_value,
            is_warm,
            gas_cost,
            value_eq_prev,
            original_eq_prev,
            original_is_zero,
        }
    }

    pub(crate) fn expr(&self) -> Expression<F> {
        // Return the gas cost
        self.gas_cost.clone()
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        gas_cost: u64,
        value: eth_types::Word,
        value_prev: eth_types::Word,
        original_value: eth_types::Word,
        is_warm: bool,
        randomness: F,
    ) -> Result<(), Error> {
        self.value.assign(
            region,
            offset,
            Some(Word::random_linear_combine(value.to_le_bytes(), randomness)),
        )?;
        self.value_prev.assign(
            region,
            offset,
            Some(Word::random_linear_combine(
                value_prev.to_le_bytes(),
                randomness,
            )),
        )?;
        self.original_value.assign(
            region,
            offset,
            Some(Word::random_linear_combine(
                original_value.to_le_bytes(),
                randomness,
            )),
        )?;
        self.is_warm
            .assign(region, offset, Some(F::from(is_warm as u64)))?;
        self.value_eq_prev.assign(
            region,
            offset,
            Word::random_linear_combine(value.to_le_bytes(), randomness),
            Word::random_linear_combine(value_prev.to_le_bytes(), randomness),
        )?;
        self.original_eq_prev.assign(
            region,
            offset,
            Word::random_linear_combine(original_value.to_le_bytes(), randomness),
            Word::random_linear_combine(value_prev.to_le_bytes(), randomness),
        )?;
        self.original_is_zero.assign(
            region,
            offset,
            Word::random_linear_combine(original_value.to_le_bytes(), randomness),
        )?;
        debug_assert_eq!(
            calc_expected_gas_cost(value, value_prev, original_value, is_warm),
            gas_cost
        );
        Ok(())
    }
}

#[derive(Clone, Debug)]
pub(crate) struct SstoreTxRefundGadget<F> {
    tx_refund_old: Cell<F>,
    tx_refund_new: Expression<F>,
    value: Cell<F>,
    value_prev: Cell<F>,
    original_value: Cell<F>,
    value_prev_is_zero_gadget: IsZeroGadget<F>,
    value_is_zero_gadget: IsZeroGadget<F>,
    original_is_zero_gadget: IsZeroGadget<F>,
    original_eq_value_gadget: IsEqualGadget<F>,
    prev_eq_value_gadget: IsEqualGadget<F>,
    original_eq_prev_gadget: IsEqualGadget<F>,
}

impl<F: Field> SstoreTxRefundGadget<F> {
    pub(crate) fn construct(
        cb: &mut ConstraintBuilder<F>,
        tx_refund_old: Cell<F>,
        value: Cell<F>,
        value_prev: Cell<F>,
        original_value: Cell<F>,
    ) -> Self {
        let value_prev_is_zero_gadget = IsZeroGadget::construct(cb, value_prev.expr());
        let value_is_zero_gadget = IsZeroGadget::construct(cb, value.expr());
        let original_is_zero_gadget = IsZeroGadget::construct(cb, original_value.expr());

        let original_eq_value_gadget =
            IsEqualGadget::construct(cb, original_value.expr(), value.expr());
        let prev_eq_value_gadget = IsEqualGadget::construct(cb, value_prev.expr(), value.expr());
        let original_eq_prev_gadget =
            IsEqualGadget::construct(cb, original_value.expr(), value_prev.expr());

        let value_prev_is_zero = value_prev_is_zero_gadget.expr();
        let value_is_zero = value_is_zero_gadget.expr();
        let original_is_zero = original_is_zero_gadget.expr();

        let original_eq_value = original_eq_value_gadget.expr();
        let prev_eq_value = prev_eq_value_gadget.expr();
        let original_eq_prev = original_eq_prev_gadget.expr();

        // (value_prev != value) && (original_value != value) && (value ==
        // Word::from(0))
        let case_a =
            not::expr(prev_eq_value.clone()) * not::expr(original_is_zero.clone()) * value_is_zero;
        // (value_prev != value) && (original_value == value) && (original_value !=
        // Word::from(0))
        let case_b = not::expr(prev_eq_value.clone())
            * original_eq_value.clone()
            * not::expr(original_is_zero.clone());
        // (value_prev != value) && (original_value == value) && (original_value ==
        // Word::from(0))
        let case_c = not::expr(prev_eq_value.clone()) * original_eq_value * (original_is_zero);
        // (value_prev != value) && (original_value != value_prev) && (value_prev ==
        // Word::from(0))
        let case_d = not::expr(prev_eq_value) * not::expr(original_eq_prev) * (value_prev_is_zero);

        let tx_refund_new = tx_refund_old.expr()
            + case_a * GasCost::SSTORE_CLEARS_SCHEDULE.expr()
            + case_b * (GasCost::SSTORE_RESET.expr() - GasCost::WARM_ACCESS.expr())
            + case_c * (GasCost::SSTORE_SET.expr() - GasCost::WARM_ACCESS.expr())
            - case_d * (GasCost::SSTORE_CLEARS_SCHEDULE.expr());

        Self {
            value,
            value_prev,
            original_value,
            tx_refund_old,
            tx_refund_new,
            value_prev_is_zero_gadget,
            value_is_zero_gadget,
            original_is_zero_gadget,
            original_eq_value_gadget,
            prev_eq_value_gadget,
            original_eq_prev_gadget,
        }
    }

    pub(crate) fn expr(&self) -> Expression<F> {
        // Return the new tx_refund
        self.tx_refund_new.clone()
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        tx_refund: u64,
        tx_refund_old: u64,
        value: eth_types::Word,
        value_prev: eth_types::Word,
        original_value: eth_types::Word,
        randomness: F,
    ) -> Result<(), Error> {
        self.tx_refund_old
            .assign(region, offset, Some(F::from(tx_refund_old)))?;
        self.value.assign(
            region,
            offset,
            Some(Word::random_linear_combine(value.to_le_bytes(), randomness)),
        )?;
        self.value_prev.assign(
            region,
            offset,
            Some(Word::random_linear_combine(
                value_prev.to_le_bytes(),
                randomness,
            )),
        )?;
        self.original_value.assign(
            region,
            offset,
            Some(Word::random_linear_combine(
                original_value.to_le_bytes(),
                randomness,
            )),
        )?;
        self.value_prev_is_zero_gadget.assign(
            region,
            offset,
            Word::random_linear_combine(value_prev.to_le_bytes(), randomness),
        )?;
        self.value_is_zero_gadget.assign(
            region,
            offset,
            Word::random_linear_combine(value.to_le_bytes(), randomness),
        )?;
        self.original_is_zero_gadget.assign(
            region,
            offset,
            Word::random_linear_combine(original_value.to_le_bytes(), randomness),
        )?;
        self.original_eq_value_gadget.assign(
            region,
            offset,
            Word::random_linear_combine(original_value.to_le_bytes(), randomness),
            Word::random_linear_combine(value.to_le_bytes(), randomness),
        )?;
        self.prev_eq_value_gadget.assign(
            region,
            offset,
            Word::random_linear_combine(value_prev.to_le_bytes(), randomness),
            Word::random_linear_combine(value.to_le_bytes(), randomness),
        )?;
        self.original_eq_prev_gadget.assign(
            region,
            offset,
            Word::random_linear_combine(original_value.to_le_bytes(), randomness),
            Word::random_linear_combine(value_prev.to_le_bytes(), randomness),
        )?;
        debug_assert_eq!(
            calc_expected_tx_refund(tx_refund_old, value, value_prev, original_value),
            tx_refund
        );
        Ok(())
    }
}

fn calc_expected_gas_cost(
    value: eth_types::Word,
    value_prev: eth_types::Word,
    original_value: eth_types::Word,
    is_warm: bool,
) -> u64 {
    let warm_case_gas = if value_prev == value {
        GasCost::WARM_ACCESS
    } else if original_value == value_prev {
        if original_value == eth_types::Word::from(0) {
            GasCost::SSTORE_SET
        } else {
            GasCost::SSTORE_RESET
        }
    } else {
        GasCost::WARM_ACCESS
    };
    if is_warm {
        warm_case_gas.as_u64()
    } else {
        warm_case_gas.as_u64() + GasCost::COLD_SLOAD.as_u64()
    }
}

fn calc_expected_tx_refund(
    tx_refund_old: u64,
    value: eth_types::Word,
    value_prev: eth_types::Word,
    original_value: eth_types::Word,
) -> u64 {
    let mut tx_refund_new = tx_refund_old;

    if value_prev != value {
        if (original_value != value) && (value == eth_types::Word::from(0)) {
            // CaseA
            tx_refund_new += GasCost::SSTORE_CLEARS_SCHEDULE.as_u64();
        }
        if original_value == value {
            if original_value != eth_types::Word::from(0) {
                // CaseB
                tx_refund_new += GasCost::SSTORE_RESET.as_u64() - GasCost::WARM_ACCESS.as_u64();
            } else {
                // CaseC
                tx_refund_new += GasCost::SSTORE_SET.as_u64() - GasCost::WARM_ACCESS.as_u64();
            }
        }
        if original_value != value_prev && value_prev == eth_types::Word::from(0) {
            // CaseD
            tx_refund_new -= GasCost::SSTORE_CLEARS_SCHEDULE.as_u64()
        }
    }

    tx_refund_new
}

#[cfg(test)]
mod test {

    use crate::{
        test_util::{run_test_circuits, BytecodeTestConfig},
    };
    
    use eth_types::{bytecode, Word};
    use mock::{test_ctx::helpers::tx_from_1_to_0, TestContext, MOCK_ACCOUNTS};
    

    #[test]
    fn sstore_gadget_no_refund() {
        // value_prev == value
        test_ok(
            0x030201.into(),
            0x060504.into(),
            0x060504.into(),
            0x060504.into(),
        );
    }

    #[test]
    fn sstore_gadget_case_a() {
        // value_prev != value, original_value != value, value == 0
        test_ok(
            0x030201.into(),
            0x0.into(),
            0x060505.into(),
            0x060506.into(),
        );
    }

    #[test]
    fn sstore_gadget_case_b() {
        // value_prev != value, original_value == value, original_value != 0
        test_ok(
            0x030201.into(),
            0x060504.into(),
            0x060505.into(),
            0x060504.into(),
        );
    }
    #[test]
    fn sstore_gadget_case_c() {
        // value_prev != value, original_value == value, original_value == 0
        test_ok(0x030201.into(), 0.into(), 0x060505.into(), 0.into());
    }
    #[test]
    fn sstore_gadget_case_d() {
        // value_prev != value, original_value != value_prev, value_prev == 0
        test_ok(
            0x030201.into(),
            0x060504.into(),
            0x0.into(),
            0x060504.into(),
        );
    }

    fn test_ok(key: Word, value: Word, value_prev: Word, original_value: Word) {
        let bytecode_success = bytecode! {
            PUSH32(value_prev)
            PUSH32(key)
            SSTORE
            PUSH32(value)
            PUSH32(key)
            SSTORE
            STOP
        };
        let bytecode_failure = bytecode! {
            PUSH32(value_prev)
            PUSH32(key)
            SSTORE
            PUSH32(value)
            PUSH32(key)
            SSTORE
            REVERT
        };
        for bytecode in [bytecode_success, bytecode_failure] {
            let ctx = TestContext::<2, 1>::new(
                None,
                |accs| {
                    accs[0]
                        .address(MOCK_ACCOUNTS[0])
                        .balance(Word::from(10u64.pow(19)))
                        .code(bytecode)
                        .storage(vec![(key, original_value)].into_iter());
                    accs[1]
                        .address(MOCK_ACCOUNTS[1])
                        .balance(Word::from(10u64.pow(19)));
                },
                tx_from_1_to_0,
                |block, _txs| block,
            )
            .unwrap();
            let test_config = BytecodeTestConfig {
                enable_state_circuit_test: false,
                ..Default::default()
            };
            assert_eq!(run_test_circuits(ctx, Some(test_config),), Ok(()));
        }
    }
}
