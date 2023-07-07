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
                MulWordByU64Gadget,
            },
            CachedRegion, Cell,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    table::{BlockContextFieldTag, CallContextFieldTag, TxContextFieldTag, TxReceiptFieldTag},
    util::{
        word::{Word, WordCell, WordExpr},
        Expr,
    },
};
use bus_mapping::operation::Target;
use eth_types::{evm_types::MAX_REFUND_QUOTIENT_OF_GAS_USED, Field};
use halo2_proofs::{circuit::Value, plonk::Error};
use strum::EnumCount;

#[derive(Clone, Debug)]
pub(crate) struct EndTxGadget<F> {
    tx_id: Cell<F>,
    tx_gas: Cell<F>,
    max_refund: ConstantDivisionGadget<F, N_BYTES_GAS>,
    refund: Cell<F>,
    effective_refund: MinMaxGadget<F, N_BYTES_GAS>,
    mul_gas_price_by_refund: MulWordByU64Gadget<F>,
    tx_caller_address: WordCell<F>,
    gas_fee_refund: UpdateBalanceGadget<F, 2, true>,
    sub_gas_price_by_base_fee: AddWordsGadget<F, 2, true>,
    mul_effective_tip_by_gas_used: MulWordByU64Gadget<F>,
    coinbase: WordCell<F>,
    coinbase_reward: UpdateBalanceGadget<F, 2, true>,
    current_cumulative_gas_used: Cell<F>,
    is_first_tx: IsEqualGadget<F>,
    is_persistent: Cell<F>,
}

impl<F: Field> ExecutionGadget<F> for EndTxGadget<F> {
    const NAME: &'static str = "EndTx";

    const EXECUTION_STATE: ExecutionState = ExecutionState::EndTx;

    fn configure(cb: &mut EVMConstraintBuilder<F>) -> Self {
        let tx_id = cb.call_context(None, CallContextFieldTag::TxId);
        let is_persistent = cb.call_context(None, CallContextFieldTag::IsPersistent);

        let tx_gas = cb.tx_context(tx_id.expr(), TxContextFieldTag::Gas, None);
        let tx_caller_address =
            cb.tx_context_as_word(tx_id.expr(), TxContextFieldTag::CallerAddress, None);
        let tx_gas_price = cb.tx_context_as_word32(tx_id.expr(), TxContextFieldTag::GasPrice, None);

        // Calculate effective gas to refund
        let gas_used = tx_gas.expr() - cb.curr.state.gas_left.expr();
        let max_refund = ConstantDivisionGadget::construct(
            cb,
            gas_used.clone(),
            MAX_REFUND_QUOTIENT_OF_GAS_USED as u64,
        );
        let refund = cb.query_cell();
        cb.tx_refund_read(tx_id.expr(), Word::from_lo_unchecked(refund.expr()));
        let effective_refund = MinMaxGadget::construct(cb, max_refund.quotient(), refund.expr());

        // Add effective_refund * tx_gas_price back to caller's balance
        let mul_gas_price_by_refund = MulWordByU64Gadget::construct(
            cb,
            tx_gas_price.clone(),
            effective_refund.min() + cb.curr.state.gas_left.expr(),
        );
        let gas_fee_refund = UpdateBalanceGadget::construct(
            cb,
            tx_caller_address.to_word(),
            vec![mul_gas_price_by_refund.product().clone()],
            None,
        );

        // Add gas_used * effective_tip to coinbase's balance
        let coinbase = cb.query_word_unchecked();
        let base_fee = cb.query_word32();
        // lookup && range check
        for (tag, value) in [
            (BlockContextFieldTag::Coinbase, coinbase.to_word()),
            (BlockContextFieldTag::BaseFee, base_fee.to_word()),
        ] {
            cb.block_lookup(tag.expr(), None, value);
        }
        let effective_tip = cb.query_word32();
        let sub_gas_price_by_base_fee =
            AddWordsGadget::construct(cb, [effective_tip.clone(), base_fee], tx_gas_price);
        let mul_effective_tip_by_gas_used =
            MulWordByU64Gadget::construct(cb, effective_tip, gas_used.clone());
        let coinbase_reward = UpdateBalanceGadget::construct(
            cb,
            coinbase.to_word(),
            vec![mul_effective_tip_by_gas_used.product().clone()],
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

        let is_first_tx = IsEqualGadget::construct(cb, tx_id.expr(), 1.expr());

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
                cb.call_context_lookup_write(
                    Some(cb.next.state.rw_counter.expr()),
                    CallContextFieldTag::TxId,
                    // tx_id has been lookup and range_check above
                    Word::from_lo_unchecked(tx_id.expr() + 1.expr()),
                );

                cb.require_step_state_transition(StepStateTransition {
                    rw_counter: Delta(10.expr() - is_first_tx.expr()),
                    ..StepStateTransition::any()
                });
            },
        );

        cb.condition(
            cb.next.execution_state_selector([ExecutionState::EndBlock]),
            |cb| {
                cb.require_step_state_transition(StepStateTransition {
                    rw_counter: Delta(9.expr() - is_first_tx.expr()),
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
            mul_gas_price_by_refund,
            tx_caller_address,
            gas_fee_refund,
            sub_gas_price_by_base_fee,
            mul_effective_tip_by_gas_used,
            coinbase,
            coinbase_reward,
            current_cumulative_gas_used,
            is_first_tx,
            is_persistent,
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
        let gas_used = tx.gas() - step.gas_left;
        let (refund, _) = block.get_rws(step, 2).tx_refund_value_pair();
        let [(caller_balance, caller_balance_prev), (coinbase_balance, coinbase_balance_prev)] =
            [3, 4].map(|index| block.get_rws(step, index).account_value_pair());

        self.tx_id
            .assign(region, offset, Value::known(F::from(tx.id)))?;
        self.tx_gas
            .assign(region, offset, Value::known(F::from(tx.gas())))?;
        let (max_refund, _) = self.max_refund.assign(region, offset, gas_used as u128)?;
        self.refund
            .assign(region, offset, Value::known(F::from(refund)))?;
        self.effective_refund.assign(
            region,
            offset,
            F::from(max_refund as u64),
            F::from(refund),
        )?;
        let effective_refund = refund.min(max_refund as u64);
        let gas_fee_refund = tx.gas_price * (effective_refund + step.gas_left);
        self.mul_gas_price_by_refund.assign(
            region,
            offset,
            tx.gas_price,
            effective_refund + step.gas_left,
            gas_fee_refund,
        )?;
        self.tx_caller_address
            .assign_h160(region, offset, tx.from)?;
        self.gas_fee_refund.assign(
            region,
            offset,
            caller_balance_prev,
            vec![gas_fee_refund],
            caller_balance,
        )?;
        let effective_tip = tx.gas_price - block.context.base_fee;
        self.sub_gas_price_by_base_fee.assign(
            region,
            offset,
            [effective_tip, block.context.base_fee],
            tx.gas_price,
        )?;
        self.mul_effective_tip_by_gas_used.assign(
            region,
            offset,
            effective_tip,
            gas_used,
            effective_tip * gas_used,
        )?;
        self.coinbase
            .assign_h160(region, offset, block.context.coinbase)?;
        self.coinbase_reward.assign(
            region,
            offset,
            coinbase_balance_prev,
            vec![effective_tip * gas_used],
            coinbase_balance,
        )?;

        let current_cumulative_gas_used: u64 = if tx.id == 1 {
            0
        } else {
            // first transaction needs TxReceiptFieldTag::COUNT(3) lookups to tx receipt,
            // while later transactions need 4 (with one extra cumulative gas read) lookups
            let rw = &block.rws[(
                Target::TxReceipt,
                (tx.id as usize - 2) * (TxReceiptFieldTag::COUNT + 1) + 2,
            )];
            rw.receipt_value()
        };

        self.current_cumulative_gas_used.assign(
            region,
            offset,
            Value::known(F::from(current_cumulative_gas_used)),
        )?;
        self.is_first_tx
            .assign(region, offset, F::from(tx.id), F::ONE)?;
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
    use bus_mapping::circuit_input_builder::FixedCParams;
    use eth_types::{self, bytecode, Word};
    use mock::{
        eth, gwei, test_ctx::helpers::account_0_code_account_1_no_code, TestContext, MOCK_ACCOUNTS,
    };

    fn test_ok<const NACC: usize, const NTX: usize>(ctx: TestContext<NACC, NTX>) {
        CircuitTestBuilder::new_from_test_ctx(ctx)
            .params(FixedCParams {
                max_txs: 5,
                ..Default::default()
            })
            .run();
    }

    #[test]
    fn end_tx_gadget_simple() {
        let key_1: Word = 0x030201.into();
        let original_value: Word = 0x060504.into();
        let zero_value: Word = 0x0.into();

        // Testing refunds
        // When setting smart contract's non-zero values in storage to zero,
        // the sender of the transaction receives some refund (each transaction's step may include a
        // non-zero refund field). Moreover, the sum of the refunds is capped at $max_refund
        // = gas_used / MAX_REFUND_QUOTIENT_OF_GAS_USED$ where MAX_REFUND_QUOTIENT_OF_GAS_USED = 5 (see EIP EIP 3529, https://eips.ethereum.org/EIPS/eip-3529)
        // We test here that the refunds, capped or uncapped, have been correctly implemented by
        // configuring an account, MOCK_ACCOUNTS[0], with a non null storage and some code cleaning
        // the storage.

        // 1) Testing Tx with non capped refunds
        // In this first test, we reset only one value to minimize the gas_used so that the refund
        // is smaller than max_refund. More particularly, we expect here to have 21_000 (tx)
        // + 5_000 (sstore) + 3 (push) + 3 (push) gas used, hence a max_refund of 5_201 while
        // the refund should add up to 4_800 (refund of 1 sstore). Hence, we can check after the
        // transaction that MOCK_ACCOUNTS[0]'s balance decreased by:
        // (21_000 + 5_000 + 3 + 3 - 4_800) * 2_000_000_000 (=gas_cost).
        // To see the refund and balances, uncomment the code below, set TestContext to
        // TestContext::<4, 2> and run the following command: cargo test
        // evm_circuit::execution::end_tx::test::end_tx_gadget_simple -- --exact --nocapture
        let bytecode_uncapped = bytecode! {
            PUSH32(zero_value)
            PUSH32(key_1)
            SSTORE
            STOP
        };
        let storage_uncapped = vec![(key_1, original_value)].into_iter();

        let ctx = TestContext::<2, 1>::new(
            None,
            |accs| {
                accs[0]
                    .address(MOCK_ACCOUNTS[0])
                    .balance(Word::from(10u64.pow(19)))
                    .code(bytecode_uncapped)
                    .storage(storage_uncapped.into_iter());
                accs[1]
                    .address(MOCK_ACCOUNTS[1])
                    .balance(Word::from(10u64.pow(19)));
                // accs[2]
                //     .address(MOCK_ACCOUNTS[2])
                //     .code(bytecode! {
                //         PUSH32(MOCK_ACCOUNTS[1])
                //         BALANCE
                //         STOP
                //     })
                //     .balance(Word::from(10u64.pow(19)));
                // accs[3]
                //     .address(MOCK_ACCOUNTS[3])
                //     .balance(Word::from(10u64.pow(19)));
            },
            |mut txs, accs| {
                txs[0]
                    .to(accs[0].address)
                    .from(accs[1].address)
                    .gas(Word::from(30_000))
                    .gas_price(gwei(2));
                // txs[1]
                //     .to(accs[2].address)
                //     .from(accs[3].address)
                //     .gas(Word::from(30_000))
                //     .gas_price(gwei(2))
                //     .nonce(0);
            },
            |block, _tx| block,
        )
        .unwrap();

        // for (i, trace) in ctx.geth_traces.iter().enumerate() {
        //     println!(
        //         "\n---------- trace {}: gas={}, failed={}, return_value={}",
        //         i, trace.gas, trace.failed, trace.return_value
        //     );
        //     for (j, step) in trace.struct_logs.iter().enumerate() {
        //         println!(
        //             "  step {}: gas={}, gas_cost={}, refund={}, top_stack={}",
        //             j,
        //             step.gas,
        //             step.gas_cost,
        //             step.refund,
        //             if step.stack.last().is_ok() {
        //                 step.stack.last().unwrap()
        //             } else {
        //                 Word::from(0)
        //             },
        //         )
        //     }
        // }
        test_ok(ctx);

        // 2) Testing Tx with capped refunds
        // In this second test, we reset several values so that the refund is greater than
        // max_refund and hence the effective refund is capped. More particularly, we expect
        // here to have 21_000 (tx) + 2 * (5_000 (sstore) + 3 (push) + 3 (push)) gas used, hence a
        // max_refund of 6_202 while the refund should add up to 9_600 (refund of 2 sstore).
        // Hence, we can check after the transaction that MOCK_ACCOUNTS[0]'s balance decreased by:
        // (21_000 + 2 * (5_000 + 3 + 3)  - 6_202) * 2_000_000_000 (=gas_cost).
        let key_2: Word = 0x030202.into();
        let bytecode_capped = bytecode! {
            PUSH32(zero_value)
            PUSH32(key_1)
            SSTORE
            PUSH32(zero_value)
            PUSH32(key_2)
            SSTORE
            STOP
        };
        let storage_capped = vec![(key_1, original_value), (key_2, original_value)].into_iter();

        test_ok(
            TestContext::<2, 1>::new(
                None,
                |accs| {
                    accs[0]
                        .address(MOCK_ACCOUNTS[0])
                        .balance(Word::from(10u64.pow(19)))
                        .code(bytecode_capped)
                        .storage(storage_capped);
                    accs[1]
                        .address(MOCK_ACCOUNTS[1])
                        .balance(Word::from(10u64.pow(19)));
                },
                |mut txs, accs| {
                    txs[0]
                        .to(accs[0].address)
                        .from(accs[1].address)
                        .gas(Word::from(50_000))
                        .gas_price(gwei(2));
                },
                |block, _tx| block,
            )
            .unwrap(),
        );

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
