use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        param::N_BYTES_GAS,
        step::ExecutionState,
        util::{
            common_gadget::UpdateBalanceGadget,
            constraint_builder::{
                ConstrainBuilderCommon, EVMConstraintBuilder, StepStateTransition,
                Transition::{Delta, Same},
            },
            math_gadget::{
                AddWordsGadget, ConstantDivisionGadget, IsEqualGadget, MinMaxGadget,
                MinMaxWordGadget, MulWordByU64Gadget,
            },
            CachedRegion, Cell, Word,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    table::{BlockContextFieldTag, CallContextFieldTag, TxContextFieldTag, TxReceiptFieldTag},
    util::Expr,
};
use bus_mapping::operation::Target;
use eth_types::{evm_types::MAX_REFUND_QUOTIENT_OF_GAS_USED, Field, ToLittleEndian, ToScalar};
use halo2_proofs::{circuit::Value, plonk::Error};
use strum::EnumCount;

#[derive(Clone, Debug)]
pub(crate) struct EndTxGadget<F> {
    tx_id: Cell<F>,
    tx_gas: Cell<F>,
    max_refund: ConstantDivisionGadget<F, N_BYTES_GAS>,
    refund: Cell<F>,
    effective_refund: MinMaxGadget<F, N_BYTES_GAS>,
    effective_gas_price: MinMaxWordGadget<F>,
    mul_gas_price_by_refund: MulWordByU64Gadget<F>,
    tx_caller_address: Cell<F>,
    gas_fee_refund: UpdateBalanceGadget<F, 2, true>,
    sub_gas_price_by_base_fee: AddWordsGadget<F, 2, true>,
    add_tip_cap_and_base_fee: AddWordsGadget<F, 2, true>,
    mul_effective_tip_by_gas_used: MulWordByU64Gadget<F>,
    mul_base_fee_by_gas_used: MulWordByU64Gadget<F>,
    coinbase: Cell<F>,
    coinbase_reward: UpdateBalanceGadget<F, 2, true>,
    treasury: Cell<F>,
    treasury_reward: UpdateBalanceGadget<F, 2, true>,
    current_cumulative_gas_used: Cell<F>,
    is_first_tx: IsEqualGadget<F>,
    is_persistent: Cell<F>,
    tx_gas_fee_cap: Word<F>,
}

impl<F: Field> ExecutionGadget<F> for EndTxGadget<F> {
    const NAME: &'static str = "EndTx";

    const EXECUTION_STATE: ExecutionState = ExecutionState::EndTx;

    fn configure(cb: &mut EVMConstraintBuilder<F>) -> Self {
        let tx_id = cb.call_context(None, CallContextFieldTag::TxId);
        let is_persistent = cb.call_context(None, CallContextFieldTag::IsPersistent);

        let [tx_gas, tx_caller_address] =
            [TxContextFieldTag::Gas, TxContextFieldTag::CallerAddress]
                .map(|field_tag| cb.tx_context(tx_id.expr(), field_tag, None));
        let [tx_gas_price, tx_gas_tip_cap, tx_gas_fee_cap] = [
            TxContextFieldTag::GasPrice,
            TxContextFieldTag::GasTipCap,
            TxContextFieldTag::GasFeeCap,
        ]
        .map(|field_tag| cb.tx_context_as_word(tx_id.expr(), field_tag, None));

        // Calculate effective gas to refund
        let gas_used = tx_gas.expr() - cb.curr.state.gas_left.expr();
        let max_refund = ConstantDivisionGadget::construct(
            cb,
            gas_used.clone(),
            MAX_REFUND_QUOTIENT_OF_GAS_USED as u64,
        );
        let refund = cb.query_cell();
        cb.tx_refund_read(tx_id.expr(), refund.expr());
        let effective_refund = MinMaxGadget::construct(cb, max_refund.quotient(), refund.expr());

        // Add effective_refund * tx_gas_price back to caller's balance
        let mul_gas_price_by_refund = MulWordByU64Gadget::construct(
            cb,
            tx_gas_price.clone(),
            effective_refund.min() + cb.curr.state.gas_left.expr(),
        );
        let gas_fee_refund = UpdateBalanceGadget::construct(
            cb,
            tx_caller_address.expr(),
            vec![mul_gas_price_by_refund.product().clone()],
            None,
        );

        let is_first_tx = IsEqualGadget::construct(cb, tx_id.expr(), 1.expr());

        // Add gas_used * effective_tip to coinbase's balance
        let coinbase = cb.query_cell();
        cb.block_lookup(BlockContextFieldTag::Coinbase.expr(), None, coinbase.expr());
        let base_fee = cb.query_word_rlc();
        cb.condition(is_first_tx.expr(), |cb| {
            cb.require_zero("base_fee is zero when tx is first tx", base_fee.expr());
        });
        cb.condition(not::expr(is_first_tx.expr()), |cb| {
            cb.block_lookup(BlockContextFieldTag::BaseFee.expr(), None, base_fee.expr());
        });

        let effective_tip = cb.query_word_rlc();
        // anchor's gas_price is 0, so gas_price != effective_tip + base_fee
        let sub_gas_price_by_base_fee = AddWordsGadget::construct(
            cb,
            [effective_tip.clone(), base_fee.clone()],
            tx_gas_price.clone(),
        );
        let mul_effective_tip_by_gas_used =
            MulWordByU64Gadget::construct(cb, effective_tip, gas_used.clone());
        let mul_base_fee_by_gas_used =
            MulWordByU64Gadget::construct(cb, base_fee.clone(), gas_used.clone());

        // check gas_price == min(base_fee + gas_tip_cap, gas_fee_cap)
        let base_fee_plus_tip = cb.query_word_rlc();
        let add_tip_cap_and_base_fee =
            AddWordsGadget::construct(cb, [base_fee, tx_gas_tip_cap], base_fee_plus_tip.clone());
        let effective_gas_price =
            MinMaxWordGadget::construct(cb, &base_fee_plus_tip, &tx_gas_fee_cap);
        cb.require_equal(
            "gas_price == min(gas_tip_cap + base_fee, gas_fee_cap)",
            tx_gas_price.expr(),
            effective_gas_price.min(),
        );

        // send base fee to treasury account
        let treasury = cb.query_cell();

        let coinbase_reward = UpdateBalanceGadget::construct(
            cb,
            coinbase.expr(),
            vec![mul_effective_tip_by_gas_used.product().clone()],
            None,
        );

        let treasury_reward = UpdateBalanceGadget::construct(
            cb,
            treasury.expr(),
            vec![mul_base_fee_by_gas_used.product().clone()],
            None,
        );

        // constrain tx receipt fields
        cb.tx_receipt_lookup(
            1.expr(),
            tx_id.expr(),
            TxReceiptFieldTag::PostStateOrStatus,
            is_persistent.expr(),
        );
        cb.tx_receipt_lookup(
            1.expr(),
            tx_id.expr(),
            TxReceiptFieldTag::LogLength,
            cb.curr.state.log_id.expr(),
        );

        let current_cumulative_gas_used = cb.query_cell();
        cb.condition(is_first_tx.expr(), |cb| {
            cb.require_zero(
                "current_cumulative_gas_used is zero when tx is first tx",
                current_cumulative_gas_used.expr(),
            );
        });

        cb.condition(1.expr() - is_first_tx.expr(), |cb| {
            cb.tx_receipt_lookup(
                0.expr(),
                tx_id.expr() - 1.expr(),
                TxReceiptFieldTag::CumulativeGasUsed,
                current_cumulative_gas_used.expr(),
            );
        });

        cb.tx_receipt_lookup(
            1.expr(),
            tx_id.expr(),
            TxReceiptFieldTag::CumulativeGasUsed,
            gas_used + current_cumulative_gas_used.expr(),
        );

        cb.condition(
            cb.next.execution_state_selector([ExecutionState::BeginTx]),
            |cb| {
                cb.call_context_lookup(
                    true.expr(),
                    Some(cb.next.state.rw_counter.expr()),
                    CallContextFieldTag::TxId,
                    tx_id.expr() + 1.expr(),
                );

                cb.require_step_state_transition(StepStateTransition {
                    rw_counter: Delta(11.expr() - is_first_tx.expr()),
                    ..StepStateTransition::any()
                });
            },
        );

        cb.condition(
            cb.next.execution_state_selector([ExecutionState::EndBlock]),
            |cb| {
                cb.require_step_state_transition(StepStateTransition {
                    rw_counter: Delta(10.expr() - is_first_tx.expr()),
                    // We propagate call_id so that EndBlock can get the last tx_id
                    // in order to count processed txs.
                    call_id: Same,
                    ..StepStateTransition::any()
                });
            },
        );

        Self {
            tx_id,
            tx_gas,
            max_refund,
            refund,
            effective_refund,
            effective_gas_price,
            mul_gas_price_by_refund,
            tx_caller_address,
            gas_fee_refund,
            sub_gas_price_by_base_fee,
            add_tip_cap_and_base_fee,
            mul_effective_tip_by_gas_used,
            mul_base_fee_by_gas_used,
            coinbase,
            coinbase_reward,
            treasury,
            treasury_reward,
            current_cumulative_gas_used,
            is_first_tx,
            is_persistent,
            tx_gas_fee_cap,
        }
    }

    fn assign_exec_step(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        block: &Block<F>,
        tx: &Transaction,
        call: &Call,
        step: &ExecStep,
    ) -> Result<(), Error> {
        let gas_used = tx.gas - step.gas_left.0;
        let (refund, _) = block.get_rws(step, 2).tx_refund_value_pair();
        let [(caller_balance, caller_balance_prev), (coinbase_balance, coinbase_balance_prev), (treasury_balance, treasury_balance_prev)] =
            [3, 4, 5].map(|index| block.get_rws(step, index).account_value_pair());
        self.tx_id
            .assign(region, offset, Value::known(F::from(tx.id as u64)))?;
        self.tx_gas
            .assign(region, offset, Value::known(F::from(tx.gas)))?;
        let (max_refund, _) = self.max_refund.assign(region, offset, gas_used as u128)?;
        self.refund
            .assign(region, offset, Value::known(F::from(refund)))?;
        self.effective_refund.assign(
            region,
            offset,
            F::from(max_refund as u64),
            F::from(refund),
        )?;

        let base_fee = if tx.id == 1 {
            0.into()
        } else {
            block.context.base_fee
        };
        self.tx_gas_fee_cap
            .assign(region, offset, Some(tx.gas_fee_cap.to_le_bytes()))?;
        self.add_tip_cap_and_base_fee.assign(
            region,
            offset,
            [tx.gas_tip_cap, base_fee],
            tx.gas_tip_cap + base_fee,
        )?;
        self.effective_gas_price.assign(
            region,
            offset,
            base_fee + tx.gas_tip_cap,
            tx.gas_fee_cap,
        )?;
        let effective_refund = refund.min(max_refund as u64);
        let gas_fee_refund = tx.gas_price * (effective_refund + step.gas_left.0);
        self.mul_gas_price_by_refund.assign(
            region,
            offset,
            tx.gas_price,
            effective_refund + step.gas_left.0,
            gas_fee_refund,
        )?;
        self.tx_caller_address.assign(
            region,
            offset,
            Value::known(
                tx.caller_address
                    .to_scalar()
                    .expect("unexpected Address -> Scalar conversion failure"),
            ),
        )?;
        self.gas_fee_refund.assign(
            region,
            offset,
            caller_balance_prev,
            vec![gas_fee_refund],
            caller_balance,
        )?;
        let effective_tip = tx.gas_price - base_fee;
        self.sub_gas_price_by_base_fee.assign(
            region,
            offset,
            [effective_tip, base_fee],
            tx.gas_price,
        )?;

        self.mul_effective_tip_by_gas_used.assign(
            region,
            offset,
            effective_tip,
            gas_used,
            effective_tip * gas_used,
        )?;
        self.mul_base_fee_by_gas_used.assign(
            region,
            offset,
            base_fee,
            gas_used,
            base_fee * gas_used,
        )?;
        self.coinbase.assign(
            region,
            offset,
            Value::known(
                block
                    .context
                    .coinbase
                    .to_scalar()
                    .expect("unexpected Address -> Scalar conversion failure"),
            ),
        )?;
        self.coinbase_reward.assign(
            region,
            offset,
            coinbase_balance_prev,
            vec![effective_tip * gas_used],
            coinbase_balance,
        )?;
        self.treasury.assign(
            region,
            offset,
            Value::known(
                block
                    .protocol_instance
                    .meta_hash
                    .treasury
                    .to_scalar()
                    .expect("unexpected Address -> Scalar conversion failure"),
            ),
        )?;
        self.treasury_reward.assign(
            region,
            offset,
            treasury_balance_prev,
            vec![base_fee * gas_used],
            treasury_balance,
        )?;

        let current_cumulative_gas_used: u64 = if tx.id == 1 {
            0
        } else {
            // first transaction needs TxReceiptFieldTag::COUNT(3) lookups to tx receipt,
            // while later transactions need 4 (with one extra cumulative gas read) lookups
            let rw = &block.rws[(
                Target::TxReceipt,
                (tx.id - 2) * (TxReceiptFieldTag::COUNT + 1) + 2,
            )];
            rw.receipt_value()
        };

        self.current_cumulative_gas_used.assign(
            region,
            offset,
            Value::known(F::from(current_cumulative_gas_used)),
        )?;
        self.is_first_tx
            .assign(region, offset, F::from(tx.id as u64), F::ONE)?;
        self.is_persistent.assign(
            region,
            offset,
            Value::known(F::from(call.is_persistent as u64)),
        )?;

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::test_util::CircuitTestBuilder;
    use bus_mapping::circuit_input_builder::CircuitsParams;
    use eth_types::{self, bytecode};

    use mock::{eth, test_ctx::helpers::account_0_code_account_1_no_code, TestContext};

    fn test_ok<const NACC: usize, const NTX: usize>(ctx: TestContext<NACC, NTX>) {
        CircuitTestBuilder::new_from_test_ctx(ctx)
            .params(CircuitsParams {
                max_txs: 5,
                ..Default::default()
            })
            .run();
    }

    #[test]
    fn end_tx_gadget_simple() {
        // TODO: Enable this with respective code when SSTORE is implemented.
        // Tx with non-capped refund
        // test_ok(vec![mock_tx(
        //     address!("0x00000000000000000000000000000000000000fe"),
        //     Some(27000),
        //     None,
        // )]);
        // Tx with capped refund
        // test_ok(vec![mock_tx(
        //     address!("0x00000000000000000000000000000000000000fe"),
        //     Some(65000),
        //     None,
        // )]);

        // Multiple txs
        test_ok(
            // Get the execution steps from the external tracer
            TestContext::<2, 3>::new(
                None,
                account_0_code_account_1_no_code(bytecode! { STOP }),
                |mut txs, accs| {
                    txs[0]
                        .to(accs[0].address)
                        .from(accs[1].address)
                        .value(eth(1));
                    txs[1]
                        .to(accs[0].address)
                        .from(accs[1].address)
                        .value(eth(1));
                    txs[2]
                        .to(accs[0].address)
                        .from(accs[1].address)
                        .value(eth(1));
                },
                |block, _tx| block.number(0xcafeu64),
            )
            .unwrap(),
        );
    }
}
