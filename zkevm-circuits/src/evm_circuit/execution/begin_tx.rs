use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        param::N_BYTES_GAS,
        step::ExecutionState,
        util::{
            common_gadget::TransferWithGasFeeGadget,
            constraint_builder::{
                ConstraintBuilder, ReversionInfo, StepStateTransition,
                Transition::{Delta, To},
            },
            math_gadget::{
                AddWordsGadget, IsEqualGadget, IsZeroGadget, LtGadget, LtWordGadget,
                MulWordByU64Gadget,
            },
            select, CachedRegion, Cell, CellType, Word,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    table::{AccountFieldTag, CallContextFieldTag, TxFieldTag as TxContextFieldTag},
    util::Expr,
};
use eth_types::{evm_types::GasCost, Field, ToLittleEndian, ToScalar, U256};
use gadgets::util::{not, or};
use halo2_proofs::circuit::Value;
use halo2_proofs::plonk::Error;

#[derive(Clone, Debug)]
pub(crate) struct BeginTxGadget<F> {
    tx_id: Cell<F>,
    tx_nonce: Cell<F>,
    tx_gas: Cell<F>,
    tx_gas_price: Word<F>,
    gas_fee: MulWordByU64Gadget<F>,
    tx_caller_address: Cell<F>,
    tx_caller_address_is_zero: IsZeroGadget<F>,
    tx_callee_address: Cell<F>,
    tx_is_create: Cell<F>,
    tx_value: Word<F>,
    effective_tx_value: Word<F>,
    effective_gas_fee: Word<F>,
    tx_call_data_length: Cell<F>,
    tx_call_data_gas_cost: Cell<F>,
    tx_is_invalid: Cell<F>,
    tx_access_list_gas_cost: Cell<F>,
    nonce: Cell<F>,
    nonce_prev: Cell<F>,
    is_nonce_valid: IsEqualGadget<F>,
    reversion_info: ReversionInfo<F>,
    gas_not_enough: LtGadget<F, N_BYTES_GAS>,
    transfer_with_gas_fee: TransferWithGasFeeGadget<F>,
    phase2_code_hash: Cell<F>,
    is_empty_code_hash: IsEqualGadget<F>,
    total_eth_cost: AddWordsGadget<F, 2, true>,
    balance_not_enough: LtWordGadget<F>,
}

impl<F: Field> ExecutionGadget<F> for BeginTxGadget<F> {
    const NAME: &'static str = "BeginTx";

    const EXECUTION_STATE: ExecutionState = ExecutionState::BeginTx;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        // Use rw_counter of the step which triggers next call as its call_id.
        let call_id = cb.curr.state.rw_counter.clone();

        let tx_id = cb.query_cell();
        cb.call_context_lookup(
            1.expr(),
            Some(call_id.expr()),
            CallContextFieldTag::TxId,
            tx_id.expr(),
        );
        let mut reversion_info = cb.reversion_info_write(None);
        cb.call_context_lookup(
            1.expr(),
            Some(call_id.expr()),
            CallContextFieldTag::IsSuccess,
            reversion_info.is_persistent(),
        );

        let [tx_nonce, tx_gas, tx_caller_address, tx_callee_address, tx_is_create, tx_call_data_length, tx_call_data_gas_cost, tx_is_invalid, tx_access_list_gas_cost] =
            [
                TxContextFieldTag::Nonce,
                TxContextFieldTag::Gas,
                TxContextFieldTag::CallerAddress,
                TxContextFieldTag::CalleeAddress,
                TxContextFieldTag::IsCreate,
                TxContextFieldTag::CallDataLength,
                TxContextFieldTag::CallDataGasCost,
                TxContextFieldTag::TxInvalid,
                TxContextFieldTag::AccessListGasCost,
            ]
            .map(|field_tag| cb.tx_context(tx_id.expr(), field_tag, None));
        let tx_caller_address_is_zero = IsZeroGadget::construct(cb, tx_caller_address.expr());
        cb.require_equal(
            "CallerAddress != 0 (not a padding tx)",
            tx_caller_address_is_zero.expr(),
            false.expr(),
        );
        let [tx_gas_price, tx_value] = [TxContextFieldTag::GasPrice, TxContextFieldTag::Value]
            .map(|field_tag| cb.tx_context_as_word(tx_id.expr(), field_tag, None));

        // Add first BeginTx step constraint to have tx_id == 1
        cb.step_first(|cb| {
            cb.require_equal("tx_id is initialized to be 1", tx_id.expr(), 1.expr());
        });

        // Verify nonce
        let nonce = cb.query_cell();
        let nonce_prev = cb.query_cell();
        cb.account_write(
            tx_caller_address.expr(),
            AccountFieldTag::Nonce,
            nonce.expr(),
            nonce_prev.expr(),
            None,
        );
        let is_nonce_valid = IsEqualGadget::construct(cb, tx_nonce.expr(), nonce_prev.expr());
        // Increment the account nonce only if the tx is valid
        cb.require_equal(
            "update nonce",
            nonce.expr(),
            nonce_prev.expr() + 1.expr() - tx_is_invalid.expr(),
        );

        // TODO: Implement EIP 1559 (currently it only supports legacy
        // transaction format)
        // Calculate transaction gas fee
        let gas_fee = MulWordByU64Gadget::construct(cb, tx_gas_price.clone(), tx_gas.expr());

        // TODO: Take gas cost of access list (EIP 2930) into consideration.
        // Use intrinsic gas
        let intrinsic_gas = select::expr(
            tx_is_create.expr(),
            GasCost::CREATION_TX.expr(),
            GasCost::TX.expr(),
        ) + tx_call_data_gas_cost.expr()
            + tx_access_list_gas_cost.expr();

        // Check gas_left is sufficient
        let gas_not_enough = LtGadget::construct(cb, tx_gas.expr(), intrinsic_gas.clone());
        let gas_left = select::expr(
            gas_not_enough.expr(),
            tx_gas.expr(),
            tx_gas.expr() - intrinsic_gas,
        );

        // Prepare access list of caller and callee
        cb.account_access_list_write(
            tx_id.expr(),
            tx_caller_address.expr(),
            1.expr(),
            0.expr(),
            None,
        );
        cb.account_access_list_write(
            tx_id.expr(),
            tx_callee_address.expr(),
            1.expr(),
            0.expr(),
            None,
        );

        // Transfer value from caller to callee
        // Use cb.query_word as TransferWithGasFeeGadget
        // expects words instead of expressions for tx_value and gas_fee
        let effective_tx_value = cb.query_word_rlc();
        let effective_gas_fee = cb.query_word_rlc();
        cb.condition(tx_is_invalid.expr(), |cb| {
            cb.require_equal(
                "effective_tx_value == 0",
                effective_tx_value.expr(),
                0.expr(),
            );
            cb.require_equal("effective_gas_fee == 0", effective_gas_fee.expr(), 0.expr());
        });
        cb.condition(not::expr(tx_is_invalid.expr()), |cb| {
            cb.require_equal(
                "effective_tx_value == tx_value",
                effective_tx_value.expr(),
                tx_value.expr(),
            );
            cb.require_equal(
                "effective_gas_fee == gas_fee",
                effective_gas_fee.expr(),
                gas_fee.product().expr(),
            );
        });

        // Verify transfer
        let transfer_with_gas_fee = TransferWithGasFeeGadget::construct(
            cb,
            tx_caller_address.expr(),
            tx_callee_address.expr(),
            effective_tx_value.clone(),
            effective_gas_fee.clone(),
            &mut reversion_info,
        );
        let sender_balance_prev = transfer_with_gas_fee.sender.balance_prev();
        let total_eth_cost_sum = cb.query_word_rlc();
        let total_eth_cost = AddWordsGadget::construct(
            cb,
            [tx_value.clone(), gas_fee.product().clone()],
            total_eth_cost_sum,
        );

        // Check if the account ETH balance is sufficient
        let balance_not_enough =
            LtWordGadget::construct(cb, sender_balance_prev, total_eth_cost.sum());

        // A transaction is invalid when
        // - The transaction requires more ETH than the transaction needs
        // - The amount of gas specified in the transaction is lower than the intrinsic
        //   gas cost
        // - The transaction nonce does not match the current nonce expected in the
        //   account
        cb.require_equal(
            "is_tx_invalid is correct",
            or::expr([
                balance_not_enough.expr(),
                gas_not_enough.expr(),
                not::expr(is_nonce_valid.expr()),
            ]),
            tx_is_invalid.expr(),
        );

        // TODO: Handle creation transaction
        // TODO: Handle precompiled

        // Read code_hash of callee
        let phase2_code_hash = cb.query_cell_with_type(CellType::StoragePhase2);
        cb.account_read(
            tx_callee_address.expr(),
            AccountFieldTag::CodeHash,
            phase2_code_hash.expr(),
        );

        let is_empty_code_hash =
            IsEqualGadget::construct(cb, phase2_code_hash.expr(), cb.empty_hash_rlc());

        let do_not_run_code = or::expr([is_empty_code_hash.expr(), tx_is_invalid.expr()]);
        cb.condition(do_not_run_code.expr(), |cb| {
            cb.require_equal(
                "Tx to account with empty code should be persistent",
                reversion_info.is_persistent(),
                1.expr(),
            );
            cb.require_equal(
                "Go to EndTx when Tx to account with empty code",
                cb.next.execution_state_selector([ExecutionState::EndTx]),
                1.expr(),
            );

            cb.require_step_state_transition(StepStateTransition {
                // 10 reads and writes:
                //   - Write CallContext TxId
                //   - Write CallContext RwCounterEndOfReversion
                //   - Write CallContext IsPersistent
                //   - Write CallContext IsSuccess
                //   - Write Account Nonce
                //   - Write TxAccessListAccount
                //   - Write TxAccessListAccount
                //   - Write Account Balance
                //   - Write Account Balance
                //   - Read Account CodeHash
                rw_counter: Delta(10.expr()),
                call_id: To(call_id.expr()),
                ..StepStateTransition::any()
            });
        });
        cb.condition(not::expr(do_not_run_code.expr()), |cb| {
            // Setup first call's context.
            for (field_tag, value) in [
                (CallContextFieldTag::Depth, 1.expr()),
                (CallContextFieldTag::CallerAddress, tx_caller_address.expr()),
                (CallContextFieldTag::CalleeAddress, tx_callee_address.expr()),
                (CallContextFieldTag::CallDataOffset, 0.expr()),
                (
                    CallContextFieldTag::CallDataLength,
                    tx_call_data_length.expr(),
                ),
                (CallContextFieldTag::Value, tx_value.expr()),
                (CallContextFieldTag::IsStatic, 0.expr()),
                (CallContextFieldTag::LastCalleeId, 0.expr()),
                (CallContextFieldTag::LastCalleeReturnDataOffset, 0.expr()),
                (CallContextFieldTag::LastCalleeReturnDataLength, 0.expr()),
                (CallContextFieldTag::IsRoot, 1.expr()),
                (CallContextFieldTag::IsCreate, tx_is_create.expr()),
                (CallContextFieldTag::CodeHash, phase2_code_hash.expr()),
            ] {
                cb.call_context_lookup(true.expr(), Some(call_id.expr()), field_tag, value);
            }

            cb.require_step_state_transition(StepStateTransition {
                // 23 reads and writes:
                //   - Write CallContext TxId
                //   - Write CallContext RwCounterEndOfReversion
                //   - Write CallContext IsPersistent
                //   - Write CallContext IsSuccess
                //   - Write Account Nonce
                //   - Write TxAccessListAccount
                //   - Write TxAccessListAccount
                //   - Write Account Balance
                //   - Write Account Balance
                //   - Read Account CodeHash
                //   - Write CallContext Depth
                //   - Write CallContext CallerAddress
                //   - Write CallContext CalleeAddress
                //   - Write CallContext CallDataOffset
                //   - Write CallContext CallDataLength
                //   - Write CallContext Value
                //   - Write CallContext IsStatic
                //   - Write CallContext LastCalleeId
                //   - Write CallContext LastCalleeReturnDataOffset
                //   - Write CallContext LastCalleeReturnDataLength
                //   - Write CallContext IsRoot
                //   - Write CallContext IsCreate
                //   - Write CallContext CodeHash
                rw_counter: Delta(23.expr()),
                call_id: To(call_id.expr()),
                is_root: To(true.expr()),
                is_create: To(tx_is_create.expr()),
                code_hash: To(phase2_code_hash.expr()),
                gas_left: To(gas_left),
                reversible_write_counter: To(2.expr()),
                log_id: To(0.expr()),
                ..StepStateTransition::new_context()
            });
        });

        Self {
            tx_id,
            tx_nonce,
            tx_gas,
            tx_gas_price,
            gas_fee,
            tx_caller_address,
            tx_caller_address_is_zero,
            tx_callee_address,
            tx_is_create,
            tx_value,
            effective_tx_value,
            effective_gas_fee,
            tx_call_data_length,
            tx_call_data_gas_cost,
            tx_is_invalid,
            tx_access_list_gas_cost,
            nonce,
            nonce_prev,
            is_nonce_valid,
            reversion_info,
            gas_not_enough,
            transfer_with_gas_fee,
            phase2_code_hash,
            is_empty_code_hash,
            total_eth_cost,
            balance_not_enough,
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
        let gas_fee = tx.gas_price * tx.gas;
        let [caller_nonce_pair, caller_balance_pair, callee_balance_pair, (callee_code_hash, _)] =
            [4, 7, 8, 9].map(|idx| block.rws[step.rw_indices[idx]].account_value_pair());

        self.tx_id
            .assign(region, offset, Value::known(F::from(tx.id as u64)))?;
        self.tx_nonce
            .assign(region, offset, Value::known(F::from(tx.nonce)))?;
        self.tx_gas
            .assign(region, offset, Value::known(F::from(tx.gas)))?;
        self.tx_gas_price
            .assign(region, offset, Some(tx.gas_price.to_le_bytes()))?;
        self.gas_fee
            .assign(region, offset, tx.gas_price, tx.gas, gas_fee)?;
        let caller_address = tx
            .caller_address
            .to_scalar()
            .expect("unexpected Address -> Scalar conversion failure");
        self.tx_caller_address
            .assign(region, offset, Value::known(caller_address))?;
        self.tx_caller_address_is_zero
            .assign(region, offset, caller_address)?;
        self.tx_callee_address.assign(
            region,
            offset,
            Value::known(
                tx.callee_address
                    .to_scalar()
                    .expect("unexpected Address -> Scalar conversion failure"),
            ),
        )?;
        self.tx_is_create
            .assign(region, offset, Value::known(F::from(tx.is_create as u64)))?;
        self.tx_call_data_length.assign(
            region,
            offset,
            Value::known(F::from(tx.call_data_length as u64)),
        )?;
        self.tx_call_data_gas_cost.assign(
            region,
            offset,
            Value::known(F::from(tx.call_data_gas_cost)),
        )?;
        self.tx_is_invalid
            .assign(region, offset, Value::known(F::from(tx.invalid_tx)))?;
        self.tx_access_list_gas_cost.assign(
            region,
            offset,
            Value::known(F::from(tx.access_list_gas_cost)),
        )?;

        let (nonce, nonce_prev) = caller_nonce_pair;
        self.nonce
            .assign(region, offset, Value::known(nonce.to_scalar().unwrap()))?;
        self.nonce_prev.assign(
            region,
            offset,
            Value::known(nonce_prev.to_scalar().unwrap()),
        )?;

        self.is_nonce_valid.assign(
            region,
            offset,
            tx.nonce.to_scalar().unwrap(),
            nonce_prev.to_scalar().unwrap(),
        )?;

        self.reversion_info.assign(
            region,
            offset,
            call.rw_counter_end_of_reversion,
            call.is_persistent,
        )?;

        let intrinsic_gas = select::value(
            F::from(tx.is_create),
            F::from(GasCost::CREATION_TX.as_u64()),
            F::from(GasCost::TX.as_u64()),
        ) + F::from(tx.call_data_gas_cost)
            + F::from(tx.access_list_gas_cost);
        self.gas_not_enough
            .assign(region, offset, F::from(tx.gas), intrinsic_gas)?;

        let total_eth_cost = tx.value + gas_fee;
        self.total_eth_cost
            .assign(region, offset, [tx.value, gas_fee], total_eth_cost)?;

        self.balance_not_enough
            .assign(region, offset, caller_balance_pair.1, total_eth_cost)?;

        let (intrinsic_tx_value, intrinsic_gas_fee) = if tx.invalid_tx == false {
            (tx.value, gas_fee)
        } else {
            (U256::zero(), U256::zero())
        };
        self.effective_tx_value
            .assign(region, offset, Some(intrinsic_tx_value.to_le_bytes()))?;
        self.effective_gas_fee
            .assign(region, offset, Some(intrinsic_gas_fee.to_le_bytes()))?;
        self.transfer_with_gas_fee.assign(
            region,
            offset,
            caller_balance_pair,
            callee_balance_pair,
            intrinsic_tx_value,
            intrinsic_gas_fee,
        )?;
        self.phase2_code_hash
            .assign(region, offset, region.word_rlc(callee_code_hash))?;
        self.is_empty_code_hash.assign_value(
            region,
            offset,
            region.word_rlc(callee_code_hash),
            region.empty_hash_rlc(),
        )?;

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::evm_circuit::test::{rand_bytes, run_test_circuit_geth_data_default};
    use bus_mapping::evm::OpcodeId;
    use eth_types::{
        self, bytecode, evm_types::GasCost, geth_types::GethData, word, Bytecode, Word,
    };
    use halo2_proofs::halo2curves::bn256::Fr;
    use mock::{eth, gwei, TestContext, MOCK_ACCOUNTS};

    fn gas(call_data: &[u8]) -> Word {
        Word::from(
            GasCost::TX.as_u64()
                + 2 * OpcodeId::PUSH32.constant_gas_cost().as_u64()
                + call_data
                    .iter()
                    .map(|&x| if x == 0 { 4 } else { 16 })
                    .sum::<u64>(),
        )
    }

    fn code_with_return() -> Bytecode {
        bytecode! {
            PUSH1(0)
            PUSH1(0)
            RETURN
        }
    }

    fn code_with_revert() -> Bytecode {
        bytecode! {
            PUSH1(0)
            PUSH1(0)
            REVERT
        }
    }

    fn test_ok(tx: eth_types::Transaction, code: Option<Bytecode>) {
        // Get the execution steps from the external tracer
        let block: GethData = TestContext::<2, 1>::new(
            None,
            |accs| {
                accs[0].address(MOCK_ACCOUNTS[0]).balance(eth(10));
                if let Some(code) = code {
                    accs[0].code(code);
                }
                accs[1].address(MOCK_ACCOUNTS[1]).balance(eth(10));
            },
            |mut txs, _accs| {
                txs[0]
                    .to(tx.to.unwrap())
                    .from(tx.from)
                    .gas_price(tx.gas_price.unwrap())
                    .gas(tx.gas)
                    .input(tx.input)
                    .value(tx.value);
            },
            |block, _tx| block.number(0xcafeu64),
        )
        .unwrap()
        .into();

        assert_eq!(run_test_circuit_geth_data_default::<Fr>(block), Ok(()));
    }

    fn mock_tx(value: Word, gas_price: Word, calldata: Vec<u8>) -> eth_types::Transaction {
        let from = MOCK_ACCOUNTS[1];
        let to = MOCK_ACCOUNTS[0];
        eth_types::Transaction {
            from,
            to: Some(to),
            value,
            gas: gas(&calldata),
            gas_price: Some(gas_price),
            input: calldata.into(),
            ..Default::default()
        }
    }

    #[test]
    fn begin_tx_gadget_simple() {
        // Transfer 1 ether to account with empty code, successfully
        test_ok(mock_tx(eth(1), gwei(2), vec![]), None);

        // Transfer 1 ether, successfully
        test_ok(mock_tx(eth(1), gwei(2), vec![]), Some(code_with_return()));

        // Transfer 1 ether, tx reverts
        test_ok(mock_tx(eth(1), gwei(2), vec![]), Some(code_with_revert()));

        // Transfer nothing with some calldata
        test_ok(
            mock_tx(eth(0), gwei(2), vec![1, 2, 3, 4, 0, 0, 0, 0]),
            Some(code_with_return()),
        );
    }

    #[test]
    fn begin_tx_large_nonce() {
        // This test checks that the rw table assignment and evm circuit are consistent
        // in not applying an RLC to account and tx nonces.
        // https://github.com/privacy-scaling-explorations/zkevm-circuits/issues/592
        let multibyte_nonce = Word::from(700);

        let to = MOCK_ACCOUNTS[0];
        let from = MOCK_ACCOUNTS[1];

        let code = bytecode! {
            STOP
        };

        let block: GethData = TestContext::<2, 1>::new(
            None,
            |accs| {
                accs[0].address(to).balance(eth(1)).code(code);
                accs[1].address(from).balance(eth(1)).nonce(multibyte_nonce);
            },
            |mut txs, _| {
                txs[0].to(to).from(from).nonce(multibyte_nonce);
            },
            |block, _| block,
        )
        .unwrap()
        .into();

        assert_eq!(run_test_circuit_geth_data_default::<Fr>(block), Ok(()));
    }

    #[test]
    fn begin_tx_invalid_nonce() {
        // The nonce of the account doing the transaction is not correct
        // Use the same nonce value for two transactions.
        let multibyte_nonce = Word::from(1);

        let to = MOCK_ACCOUNTS[0];
        let from = MOCK_ACCOUNTS[1];

        let code = bytecode! {
            STOP
        };

        let block: GethData = TestContext::<2, 1>::new(
            None,
            |accs| {
                accs[0].address(to).balance(eth(1)).code(code);
                accs[1].address(from).balance(eth(1)).nonce(multibyte_nonce);
            },
            |mut txs, _| {
                //txs[0].to(to).from(from).nonce(Word::from(1));
                txs[0]
                    .to(to)
                    .from(from)
                    .nonce(Word::from(0))
                    .invalid_tx(Word::from(1));
            },
            |block, _| block,
        )
        .unwrap()
        .into();

        assert_eq!(run_test_circuit_geth_data_default::<Fr>(block), Ok(()));
    }

    #[test]
    fn begin_tx_not_enough_eth() {
        // The account does not have enough ETH to pay for eth_value + tx_gas *
        // tx_gas_price.
        let multibyte_nonce = Word::from(1);

        let to = MOCK_ACCOUNTS[0];
        let from = MOCK_ACCOUNTS[1];

        let balance = Word::from(1) * Word::from(10u64.pow(5));
        let block: GethData = TestContext::<2, 1>::new(
            None,
            |accs| {
                accs[0].address(to).balance(gwei(0));
                accs[1]
                    .address(from)
                    .balance(balance)
                    .nonce(multibyte_nonce);
            },
            |mut txs, _| {
                txs[0]
                    .to(to)
                    .from(from)
                    .nonce(multibyte_nonce)
                    .gas_price(gwei(1))
                    .gas(Word::from(10u64.pow(5)))
                    .value(gwei(1))
                    .invalid_tx(Word::from(1));
            },
            |block, _| block,
        )
        .unwrap()
        .into();

        assert_eq!(run_test_circuit_geth_data_default::<Fr>(block), Ok(()));
    }

    #[test]
    fn begin_tx_insufficient_gas() {
        let multibyte_nonce = Word::from(1);

        let to = MOCK_ACCOUNTS[0];
        let from = MOCK_ACCOUNTS[1];

        let balance = Word::from(1) * Word::from(10u64.pow(18));
        let block: GethData = TestContext::<2, 1>::new(
            None,
            |accs| {
                accs[0].address(to).balance(gwei(0));
                accs[1]
                    .address(from)
                    .balance(balance)
                    .nonce(multibyte_nonce);
            },
            |mut txs, _| {
                txs[0]
                    .to(to)
                    .from(from)
                    .nonce(multibyte_nonce)
                    .gas_price(gwei(1))
                    .gas(Word::from(1))
                    .value(gwei(1))
                    .invalid_tx(Word::from(1));
            },
            |block, _| block,
        )
        .unwrap()
        .into();

        assert_eq!(run_test_circuit_geth_data_default::<Fr>(block), Ok(()));
    }

    #[test]
    fn begin_tx_gadget_rand() {
        let random_amount = Word::from_little_endian(&rand_bytes(32)) % eth(1);
        let random_gas_price = Word::from_little_endian(&rand_bytes(32)) % gwei(2);
        // If this test fails, we want these values to appear in the CI logs.
        dbg!(random_amount, random_gas_price);

        for (value, gas_price, calldata, code) in [
            // Transfer random ether to account with empty code, successfully
            (random_amount, gwei(2), vec![], None),
            // Transfer nothing with random gas_price to account with empty code, successfully
            (eth(0), random_gas_price, vec![], None),
            // Transfer random ether, successfully
            (random_amount, gwei(2), vec![], Some(code_with_return())),
            // Transfer nothing with random gas_price, successfully
            (eth(0), random_gas_price, vec![], Some(code_with_return())),
            // Transfer random ether, tx reverts
            (random_amount, gwei(2), vec![], Some(code_with_revert())),
            // Transfer nothing with random gas_price, tx reverts
            (eth(0), random_gas_price, vec![], Some(code_with_revert())),
        ] {
            test_ok(mock_tx(value, gas_price, calldata), code);
        }
    }

    #[test]
    fn begin_tx_no_code() {
        let block: GethData = TestContext::<2, 1>::new(
            None,
            |accs| {
                accs[0].address(MOCK_ACCOUNTS[0]).balance(eth(20));
                accs[1].address(MOCK_ACCOUNTS[1]).balance(eth(10));
            },
            |mut txs, _accs| {
                txs[0]
                    .from(MOCK_ACCOUNTS[0])
                    .to(MOCK_ACCOUNTS[1])
                    .gas_price(gwei(2))
                    .gas(Word::from(0x10000))
                    .value(eth(2));
            },
            |block, _tx| block.number(0xcafeu64),
        )
        .unwrap()
        .into();

        assert_eq!(run_test_circuit_geth_data_default::<Fr>(block), Ok(()));
    }

    #[test]
    fn begin_tx_no_account() {
        let block: GethData = TestContext::<1, 1>::new(
            None,
            |accs| {
                accs[0].address(MOCK_ACCOUNTS[0]).balance(eth(20));
            },
            |mut txs, _accs| {
                txs[0]
                    .from(MOCK_ACCOUNTS[0])
                    .to(MOCK_ACCOUNTS[1])
                    .gas_price(gwei(2))
                    .gas(Word::from(0x10000))
                    .value(eth(2));
            },
            |block, _tx| block.number(0xcafeu64),
        )
        .unwrap()
        .into();

        assert_eq!(run_test_circuit_geth_data_default::<Fr>(block), Ok(()));
    }

    // TODO: Enable this test once we have support for contract deployment from
    // BeginTx.
    #[ignore]
    #[test]
    fn begin_tx_deploy() {
        let code = bytecode! {
            // [ADDRESS, STOP]
            PUSH32(word!("3000000000000000000000000000000000000000000000000000000000000000"))
            PUSH1(0)
            MSTORE

            PUSH1(2)
            PUSH1(0)
            RETURN
        };
        let block: GethData = TestContext::<1, 1>::new(
            None,
            |accs| {
                accs[0].address(MOCK_ACCOUNTS[0]).balance(eth(20));
            },
            |mut txs, _accs| {
                txs[0]
                    .from(MOCK_ACCOUNTS[0])
                    .gas_price(gwei(2))
                    .gas(Word::from(0x10000))
                    .value(eth(2))
                    .input(code.into());
            },
            |block, _tx| block.number(0xcafeu64),
        )
        .unwrap()
        .into();

        assert_eq!(run_test_circuit_geth_data_default::<Fr>(block), Ok(()));
    }
}
