use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        param::N_BYTES_GAS,
        step::ExecutionState,
        util::{
            common_gadget::{TransferToGadget, UpdateBalanceGadget},
            constraint_builder::EVMConstraintBuilder,
            math_gadget::{
                AddWordsGadget, ConstantDivisionGadget, IsZeroWordGadget, MinMaxGadget,
                MulWordByU64Gadget,
            },
            tx::EndTxHelperGadget,
            CachedRegion, Cell,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    table::{AccountFieldTag, BlockContextFieldTag, CallContextFieldTag, TxContextFieldTag},
    util::{
        word::{Word, WordCell, WordExpr},
        Expr,
    },
};
use eth_types::{evm_types::MAX_REFUND_QUOTIENT_OF_GAS_USED, Field};
use halo2_proofs::{circuit::Value, plonk::Error};

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
    coinbase_code_hash: WordCell<F>,
    coinbase_code_hash_is_zero: IsZeroWordGadget<F, WordCell<F>>,
    coinbase_reward: TransferToGadget<F>,
    is_persistent: Cell<F>,
    end_tx: EndTxHelperGadget<F>,
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
        let coinbase_code_hash = cb.query_word_unchecked();
        let coinbase_code_hash_is_zero = IsZeroWordGadget::construct(cb, &coinbase_code_hash);
        cb.account_read(
            coinbase.to_word(),
            AccountFieldTag::CodeHash,
            coinbase_code_hash.to_word(),
        );
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
        let coinbase_reward = TransferToGadget::construct(
            cb,
            coinbase.to_word(),
            1.expr() - coinbase_code_hash_is_zero.expr(),
            false.expr(),
            mul_effective_tip_by_gas_used.product().clone(),
            None,
            true,
        );

        let end_tx = EndTxHelperGadget::construct(
            cb,
            tx_id.expr(),
            is_persistent.expr(),
            gas_used,
            9.expr() + coinbase_reward.rw_delta(),
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
            coinbase_code_hash,
            coinbase_code_hash_is_zero,
            coinbase_reward,
            is_persistent,
            end_tx,
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
        let (caller_balance, caller_balance_prev) = block.get_rws(step, 3).account_balance_pair();
        let (coinbase_code_hash_prev, _) = block.get_rws(step, 4).account_codehash_pair();

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
        let coinbase_reward = effective_tip * gas_used;
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
            coinbase_reward,
        )?;
        self.coinbase
            .assign_h160(region, offset, block.context.coinbase)?;
        self.coinbase_code_hash
            .assign_u256(region, offset, coinbase_code_hash_prev)?;
        self.coinbase_code_hash_is_zero
            .assign_u256(region, offset, coinbase_code_hash_prev)?;
        if !coinbase_reward.is_zero() {
            let coinbase_balance_pair = block
                .get_rws(
                    step,
                    if coinbase_code_hash_prev.is_zero() {
                        6
                    } else {
                        5
                    },
                )
                .account_balance_pair();
            self.coinbase_reward.assign(
                region,
                offset,
                coinbase_balance_pair,
                effective_tip * gas_used,
            )?;
        }
        self.is_persistent.assign(
            region,
            offset,
            Value::known(F::from(call.is_persistent as u64)),
        )?;
        self.end_tx.assign(region, offset, block, tx)?;

        Ok(())
    }
}

#[cfg(test)]
mod test {

    use crate::{table::CallContextFieldTag, test_util::CircuitTestBuilder};
    use bus_mapping::{circuit_input_builder::FixedCParams, operation::Target};
    use eth_types::{self, bytecode, Word};
    use itertools::Itertools;
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

    #[test]
    fn end_tx_consistent_tx_id_write() {
        // check there is no consecutive txid write with same txid in rw_table

        let block = CircuitTestBuilder::new_from_test_ctx(
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
        )
        .params(FixedCParams {
            max_txs: 5,
            ..Default::default()
        })
        .build_block()
        .unwrap();

        block.rws.0[&Target::CallContext]
            .iter()
            .filter(|rw| {
                // filter all txid write operation
                rw.is_write()
                    && rw
                        .field_tag()
                        .is_some_and(|tag| tag == CallContextFieldTag::TxId as u64)
            })
            .sorted_by_key(|a| a.rw_counter())
            .tuple_windows()
            .for_each(|(a, b)| {
                // chech there is no consecutive write with same txid value
                assert!(a.rw_counter() != b.rw_counter());
                assert!(a.value_assignment() != b.value_assignment());
            })
    }

    #[test]
    fn end_tx_gadget_nonexisting_coinbase() {
        // Check that the code hash of the coinbase address is correctly set to be the empty code
        // hash when it is created because of receiving the gas fees from the first tx.
        test_ok(
            TestContext::<2, 2>::new(
                None,
                account_0_code_account_1_no_code(bytecode! {
                    COINBASE
                    EXTCODEHASH
                }), /* EXTCODEHASH will return 0 for the first tx and the empty code hash for
                     * the second tx. */
                |mut txs, accs| {
                    txs[0]
                        .to(accs[0].address)
                        .from(accs[1].address)
                        .value(eth(1));
                    txs[1]
                        .to(accs[0].address)
                        .from(accs[1].address)
                        .value(eth(1));
                },
                |block, _| block,
            )
            .unwrap(),
        );
    }
}
