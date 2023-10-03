use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        param::{N_BYTES_ACCOUNT_ADDRESS, N_BYTES_GAS, N_BYTES_U64},
        step::ExecutionState,
        util::{
            and,
            common_gadget::TransferWithGasFeeGadget,
            constraint_builder::{
                ConstrainBuilderCommon, EVMConstraintBuilder, ReversionInfo, StepStateTransition,
                Transition::{Delta, To},
            },
            is_precompiled,
            math_gadget::{
                ConstantDivisionGadget, ContractCreateGadget, IsEqualWordGadget, IsZeroWordGadget,
                MulWordByU64Gadget, RangeCheckGadget,
            },
            not, or, select, AccountAddress, CachedRegion, Cell, StepRws,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    table::{
        AccountFieldTag, BlockContextFieldTag, CallContextFieldTag, TxFieldTag as TxContextFieldTag,
    },
    util::{
        word::{Word, Word32Cell, WordCell, WordExpr},
        Expr,
    },
};
use bus_mapping::state_db::CodeDB;
use eth_types::{evm_types::GasCost, keccak256, Field, ToWord, U256};
use halo2_proofs::{
    circuit::Value,
    plonk::{Error, Expression},
};

const PRECOMPILE_COUNT: usize = 9;

#[derive(Clone, Debug)]
pub(crate) struct BeginTxGadget<F> {
    // tx_id is query in current scope. The range should be determined here
    tx_id: Cell<F>,
    tx_nonce: Cell<F>,
    tx_gas: Cell<F>,
    tx_gas_price: Word32Cell<F>,
    mul_gas_fee_by_gas: MulWordByU64Gadget<F>,
    tx_caller_address: WordCell<F>,
    tx_caller_address_is_zero: IsZeroWordGadget<F, WordCell<F>>,
    tx_callee_address: WordCell<F>,
    call_callee_address: AccountAddress<F>,
    tx_is_create: Cell<F>,
    tx_call_data_length: Cell<F>,
    tx_call_data_gas_cost: Cell<F>,
    tx_call_data_word_length: ConstantDivisionGadget<F, N_BYTES_U64>,
    reversion_info: ReversionInfo<F>,
    sufficient_gas_left: RangeCheckGadget<F, N_BYTES_GAS>,
    transfer_with_gas_fee: TransferWithGasFeeGadget<F>,
    code_hash: WordCell<F>,
    is_empty_code_hash: IsEqualWordGadget<F, Word<Expression<F>>, Word<Expression<F>>>,
    caller_nonce_hash_bytes: Word32Cell<F>,
    create: ContractCreateGadget<F, false>,
    callee_not_exists: IsZeroWordGadget<F, WordCell<F>>,
    is_caller_callee_equal: Cell<F>,
    // EIP-3651 (Warm COINBASE)
    coinbase: WordCell<F>,
    // Caller, callee and a list addresses are added to the access list before
    // coinbase, and may be duplicate.
    // <https://github.com/ethereum/go-ethereum/blob/604e215d1bb070dff98fb76aa965064c74e3633f/core/state/statedb.go#LL1119C9-L1119C9>
    is_coinbase_warm: Cell<F>,
}

impl<F: Field> ExecutionGadget<F> for BeginTxGadget<F> {
    const NAME: &'static str = "BeginTx";

    const EXECUTION_STATE: ExecutionState = ExecutionState::BeginTx;

    fn configure(cb: &mut EVMConstraintBuilder<F>) -> Self {
        // Use rw_counter of the step which triggers next call as its call_id.
        let call_id = cb.curr.state.rw_counter.clone();

        let tx_id = cb.query_cell(); // already constrain `if step_first && tx_id = 1` and `tx_id += 1` at EndTx

        cb.debug_expression("tx_id", tx_id.expr());
        cb.call_context_lookup_write(
            Some(call_id.expr()),
            CallContextFieldTag::TxId,
            Word::from_lo_unchecked(tx_id.expr()),
        ); // rwc_delta += 1
        let mut reversion_info = cb.reversion_info_write_unchecked(None); // rwc_delta += 2
        cb.call_context_lookup_write(
            Some(call_id.expr()),
            CallContextFieldTag::IsSuccess,
            Word::from_lo_unchecked(reversion_info.is_persistent()),
        ); // rwc_delta += 1
        cb.debug_expression(format!("call_id {}", 3), call_id.expr());

        let [tx_nonce, tx_gas, tx_is_create, tx_call_data_length, tx_call_data_gas_cost] = [
            TxContextFieldTag::Nonce,
            TxContextFieldTag::Gas,
            TxContextFieldTag::IsCreate,
            TxContextFieldTag::CallDataLength,
            TxContextFieldTag::CallDataGasCost,
        ]
        .map(|field_tag| cb.tx_context(tx_id.expr(), field_tag, None));
        let [tx_gas_price, tx_value] = [TxContextFieldTag::GasPrice, TxContextFieldTag::Value]
            .map(|field_tag| cb.tx_context_as_word32(tx_id.expr(), field_tag, None));

        let [tx_caller_address, tx_callee_address] = [
            TxContextFieldTag::CallerAddress,
            TxContextFieldTag::CalleeAddress,
        ]
        .map(|field_tag| cb.tx_context_as_word(tx_id.expr(), field_tag, None));

        let tx_caller_address_is_zero = IsZeroWordGadget::construct(cb, &tx_caller_address);
        cb.require_equal(
            "CallerAddress != 0 (not a padding tx)",
            tx_caller_address_is_zero.expr(),
            false.expr(),
        );

        let call_callee_address = cb.query_account_address();
        cb.condition(not::expr(tx_is_create.expr()), |cb| {
            cb.require_equal_word(
                "Tx to non-zero address",
                tx_callee_address.to_word(),
                call_callee_address.to_word(),
            );
        });

        // Add first BeginTx step constraint to have tx_id == 1
        cb.step_first(|cb| {
            cb.require_equal("tx_id is initialized to be 1", tx_id.expr(), 1.expr());
        });

        // Increase caller's nonce.
        // (tx caller's nonce always increases even tx ends with error)
        cb.account_write(
            tx_caller_address.to_word(),
            AccountFieldTag::Nonce,
            Word::from_lo_unchecked(tx_nonce.expr() + 1.expr()),
            Word::from_lo_unchecked(tx_nonce.expr()),
            None,
        ); // rwc_delta += 1

        // TODO: Implement EIP 1559 (currently it only supports legacy
        // transaction format)
        // Calculate transaction gas fee
        let mul_gas_fee_by_gas =
            MulWordByU64Gadget::construct(cb, tx_gas_price.clone(), tx_gas.expr());

        let tx_call_data_word_length =
            ConstantDivisionGadget::construct(cb, tx_call_data_length.expr() + 31.expr(), 32);

        // Calculate gas cost of init code for EIP-3860.
        let init_code_gas_cost = select::expr(
            tx_is_create.expr(),
            tx_call_data_word_length.quotient().expr()
                * eth_types::evm_types::INIT_CODE_WORD_GAS.expr(),
            0.expr(),
        );

        // TODO: Take gas cost of access list (EIP 2930) into consideration.
        // Use intrinsic gas
        let intrinsic_gas_cost = select::expr(
            tx_is_create.expr(),
            GasCost::CREATION_TX.expr(),
            GasCost::TX.expr(),
        ) + tx_call_data_gas_cost.expr()
            + init_code_gas_cost;

        // Check gas_left is sufficient
        let gas_left = tx_gas.expr() - intrinsic_gas_cost;
        let sufficient_gas_left = RangeCheckGadget::construct(cb, gas_left.clone());

        // Add precompile contract address to access list
        for addr in 1..=PRECOMPILE_COUNT {
            cb.account_access_list_write_unchecked(
                tx_id.expr(),
                Word::new([addr.expr(), 0.expr()]),
                1.expr(),
                0.expr(),
                None,
            );
        } // rwc_delta += PRECOMPILE_COUNT

        // Prepare access list of caller and callee
        cb.account_access_list_write_unchecked(
            tx_id.expr(),
            tx_caller_address.to_word(),
            1.expr(),
            0.expr(),
            None,
        ); // rwc_delta += 1
        let is_caller_callee_equal = cb.query_bool();
        cb.account_access_list_write_unchecked(
            tx_id.expr(),
            tx_callee_address.to_word(),
            1.expr(),
            // No extra constraint being used here.
            // Correctness will be enforced in build_tx_access_list_account_constraints
            is_caller_callee_equal.expr(),
            None,
        ); // rwc_delta += 1

        // Query coinbase address.
        let coinbase = cb.query_word_unchecked();
        let is_coinbase_warm = cb.query_bool();
        cb.block_lookup(
            BlockContextFieldTag::Coinbase.expr(),
            None,
            coinbase.to_word(),
        );
        cb.account_access_list_write_unchecked(
            tx_id.expr(),
            coinbase.to_word(),
            1.expr(),
            is_coinbase_warm.expr(),
            None,
        ); // rwc_delta += 1

        // Read code_hash of callee
        let code_hash = cb.query_word_unchecked();
        let is_empty_code_hash =
            IsEqualWordGadget::construct(cb, &code_hash.to_word(), &cb.empty_code_hash());
        let callee_not_exists = IsZeroWordGadget::construct(cb, &code_hash);
        // no_callee_code is true when the account exists and has empty
        // code hash, or when the account doesn't exist (which we encode with
        // code_hash = 0).
        let no_callee_code = is_empty_code_hash.expr() + callee_not_exists.expr();

        // TODO: And not precompile
        // i think this needs to be removed....

        cb.account_read(
            tx_callee_address.to_word(),
            AccountFieldTag::CodeHash,
            code_hash.to_word(),
        );

        // Transfer value from caller to callee, creating account if necessary.
        let transfer_with_gas_fee = TransferWithGasFeeGadget::construct(
            cb,
            tx_caller_address.to_word(),
            tx_callee_address.to_word(),
            not::expr(callee_not_exists.expr()),
            or::expr([tx_is_create.expr(), callee_not_exists.expr()]),
            tx_value.clone(),
            mul_gas_fee_by_gas.product().clone(),
            &mut reversion_info,
        );

        let caller_nonce_hash_bytes = cb.query_word32();
        let create = ContractCreateGadget::construct(cb);
        cb.require_equal_word(
            "tx caller address equivalence",
            tx_caller_address.to_word(),
            create.caller_address(),
        );
        cb.condition(tx_is_create.expr(), |cb| {
            cb.require_equal_word(
                "call callee address equivalence",
                call_callee_address.to_word(),
                AccountAddress::<F>::new(
                    caller_nonce_hash_bytes.limbs[0..N_BYTES_ACCOUNT_ADDRESS]
                        .to_vec()
                        .try_into()
                        .unwrap(),
                )
                .to_word(),
            );
        });
        cb.require_equal(
            "tx nonce equivalence",
            tx_nonce.expr(),
            create.caller_nonce(),
        );

        // 1. Handle contract creation transaction.
        cb.condition(tx_is_create.expr(), |cb| {
            cb.keccak_table_lookup(
                create.input_rlc(cb),
                create.input_length(),
                caller_nonce_hash_bytes.to_word(),
            );

            cb.account_write(
                call_callee_address.to_word(),
                AccountFieldTag::Nonce,
                Word::one(),
                Word::zero(),
                Some(&mut reversion_info),
            );
            for (field_tag, value) in [
                (CallContextFieldTag::Depth, Word::one()),
                (
                    CallContextFieldTag::CallerAddress,
                    tx_caller_address.to_word(),
                ),
                (
                    CallContextFieldTag::CalleeAddress,
                    call_callee_address.to_word(),
                ),
                (CallContextFieldTag::CallDataOffset, Word::zero()),
                (
                    CallContextFieldTag::CallDataLength,
                    Word::from_lo_unchecked(tx_call_data_length.expr()),
                ),
                (CallContextFieldTag::Value, tx_value.to_word()),
                (CallContextFieldTag::IsStatic, Word::zero()),
                (CallContextFieldTag::LastCalleeId, Word::zero()),
                (
                    CallContextFieldTag::LastCalleeReturnDataOffset,
                    Word::zero(),
                ),
                (
                    CallContextFieldTag::LastCalleeReturnDataLength,
                    Word::zero(),
                ),
                (CallContextFieldTag::IsRoot, Word::one()),
                (CallContextFieldTag::IsCreate, Word::one()),
                (
                    CallContextFieldTag::CodeHash,
                    cb.curr.state.code_hash.to_word(),
                ),
            ] {
                cb.call_context_lookup_write(Some(call_id.expr()), field_tag, value);
            }

            cb.require_step_state_transition(StepStateTransition {
                // 21 + a reads and writes:
                //   - Write CallContext TxId
                //   - Write CallContext RwCounterEndOfReversion
                //   - Write CallContext IsPersistent
                //   - Write CallContext IsSuccess
                //   - Write Account (Caller) Nonce
                //   - Write TxAccessListAccount (Precompile) x PRECOMPILE_COUNT
                //   - Write TxAccessListAccount (Caller)
                //   - Write TxAccessListAccount (Callee)
                //   - Write TxAccessListAccount (Coinbase) for EIP-3651
                //   - a TransferWithGasFeeGadget
                //   - Write Account (Callee) Nonce (Reversible)
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
                rw_counter: Delta(
                    23.expr() + transfer_with_gas_fee.rw_delta() + PRECOMPILE_COUNT.expr(),
                ),
                call_id: To(call_id.expr()),
                is_root: To(true.expr()),
                is_create: To(tx_is_create.expr()),
                code_hash: To(cb.curr.state.code_hash.to_word()),
                gas_left: To(gas_left.clone()),
                // There are a + 1 reversible writes:
                //  - a TransferWithGasFeeGadget
                //  - Callee Account Nonce
                reversible_write_counter: To(transfer_with_gas_fee.reversible_w_delta() + 1.expr()),
                log_id: To(0.expr()),
                ..StepStateTransition::new_context()
            });
        });

        // TODO: 2. Handle call to precompiled contracts.

        // 3. Call to account with empty code.
        cb.condition(
            and::expr([not::expr(tx_is_create.expr()), no_callee_code.clone()]),
            |cb| {
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
                    // 8 reads and writes:
                    //   - Write CallContext TxId
                    //   - Write CallContext RwCounterEndOfReversion
                    //   - Write CallContext IsPersistent
                    //   - Write CallContext IsSuccess
                    //   - Write Account Nonce
                    //   - Write TxAccessListAccount (Precompile) x PRECOMPILE_COUNT
                    //   - Write TxAccessListAccount (Caller)
                    //   - Write TxAccessListAccount (Callee)
                    //   - Write TxAccessListAccount (Coinbase) for EIP-3651
                    //   - Read Account CodeHash
                    //   - a TransferWithGasFeeGadget
                    rw_counter: Delta(
                        9.expr() + transfer_with_gas_fee.rw_delta() + PRECOMPILE_COUNT.expr(),
                    ),
                    call_id: To(call_id.expr()),
                    ..StepStateTransition::any()
                });
            },
        );

        // 4. Call to account with non-empty code.
        cb.condition(
            and::expr([not::expr(tx_is_create.expr()), not::expr(no_callee_code)]),
            |cb| {
                // Setup first call's context.
                for (field_tag, value) in [
                    (CallContextFieldTag::Depth, Word::one()),
                    (
                        CallContextFieldTag::CallerAddress,
                        tx_caller_address.to_word(),
                    ),
                    (
                        CallContextFieldTag::CalleeAddress,
                        tx_callee_address.to_word(),
                    ),
                    (CallContextFieldTag::CallDataOffset, Word::zero()),
                    (
                        CallContextFieldTag::CallDataLength,
                        Word::from_lo_unchecked(tx_call_data_length.expr()),
                    ),
                    (CallContextFieldTag::Value, tx_value.to_word()),
                    (CallContextFieldTag::IsStatic, Word::zero()),
                    (CallContextFieldTag::LastCalleeId, Word::zero()),
                    (
                        CallContextFieldTag::LastCalleeReturnDataOffset,
                        Word::zero(),
                    ),
                    (
                        CallContextFieldTag::LastCalleeReturnDataLength,
                        Word::zero(),
                    ),
                    (CallContextFieldTag::IsRoot, Word::one()),
                    (
                        CallContextFieldTag::IsCreate,
                        Word::from_lo_unchecked(tx_is_create.expr()),
                    ),
                    (CallContextFieldTag::CodeHash, code_hash.to_word()),
                ] {
                    cb.call_context_lookup_write(Some(call_id.expr()), field_tag, value);
                }

                cb.require_step_state_transition(StepStateTransition {
                    // 21 reads and writes:
                    //   - Write CallContext TxId
                    //   - Write CallContext RwCounterEndOfReversion
                    //   - Write CallContext IsPersistent
                    //   - Write CallContext IsSuccess
                    //   - Write Account Nonce
                    //   - Write TxAccessListAccount (Precompile) x PRECOMPILE_COUNT
                    //   - Write TxAccessListAccount (Caller)
                    //   - Write TxAccessListAccount (Callee)
                    //   - Write TxAccessListAccount (Coinbase) for EIP-3651
                    //   - Read Account CodeHash
                    //   - a TransferWithGasFeeGadget
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
                    rw_counter: Delta(
                        22.expr() + transfer_with_gas_fee.rw_delta() + PRECOMPILE_COUNT.expr(),
                    ),
                    call_id: To(call_id.expr()),
                    is_root: To(true.expr()),
                    is_create: To(tx_is_create.expr()),
                    code_hash: To(code_hash.to_word()),
                    gas_left: To(gas_left),
                    reversible_write_counter: To(transfer_with_gas_fee.reversible_w_delta()),
                    log_id: To(0.expr()),
                    ..StepStateTransition::new_context()
                });
            },
        );

        Self {
            tx_id,
            tx_nonce,
            tx_gas,
            tx_gas_price,
            mul_gas_fee_by_gas,
            tx_caller_address,
            tx_caller_address_is_zero,
            tx_callee_address,
            call_callee_address,
            tx_is_create,
            tx_call_data_length,
            tx_call_data_gas_cost,
            tx_call_data_word_length,
            reversion_info,
            sufficient_gas_left,
            transfer_with_gas_fee,
            code_hash,
            is_empty_code_hash,
            caller_nonce_hash_bytes,
            create,
            callee_not_exists,
            is_caller_callee_equal,
            coinbase,
            is_coinbase_warm,
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
        let gas_fee = tx.gas_price * tx.gas();
        let zero = eth_types::Word::zero();

        let mut rws = StepRws::new(block, step);
        rws.offset_add(7);

        rws.offset_add(PRECOMPILE_COUNT);

        let is_coinbase_warm = rws.next().tx_access_list_value_pair().1;
        let mut callee_code_hash = zero;
        if !is_precompiled(&tx.to_or_contract_addr()) {
            callee_code_hash = rws.next().account_codehash_pair().1;
        }
        let callee_exists =
            is_precompiled(&tx.to_or_contract_addr()) || !callee_code_hash.is_zero();
        let caller_balance_sub_fee_pair = rws.next().account_balance_pair();
        let must_create = tx.is_create();
        if !callee_exists && (!tx.value.is_zero() || must_create) {
            callee_code_hash = rws.next().account_codehash_pair().1;
        }
        let mut caller_balance_sub_value_pair = (zero, zero);
        let mut callee_balance_pair = (zero, zero);
        if !tx.value.is_zero() {
            caller_balance_sub_value_pair = rws.next().account_balance_pair();
            callee_balance_pair = rws.next().account_balance_pair();
        };

        self.tx_id
            .assign(region, offset, Value::known(F::from(tx.id)))?;
        self.tx_nonce
            .assign(region, offset, Value::known(F::from(tx.nonce.as_u64())))?;
        self.tx_gas
            .assign(region, offset, Value::known(F::from(tx.gas())))?;
        self.tx_gas_price
            .assign_u256(region, offset, tx.gas_price)?;
        self.mul_gas_fee_by_gas
            .assign(region, offset, tx.gas_price, tx.gas(), gas_fee)?;
        self.tx_caller_address
            .assign_h160(region, offset, tx.from)?;
        self.tx_caller_address_is_zero.assign_u256(
            region,
            offset,
            U256::from_big_endian(&tx.from.to_fixed_bytes()),
        )?;
        self.tx_callee_address
            .assign_h160(region, offset, tx.to_or_contract_addr())?;
        self.call_callee_address
            .assign_h160(region, offset, tx.to_or_contract_addr())?;
        self.is_caller_callee_equal.assign(
            region,
            offset,
            Value::known(F::from((tx.from == tx.to_or_contract_addr()) as u64)),
        )?;
        self.tx_is_create
            .assign(region, offset, Value::known(F::from(tx.is_create().into())))?;
        self.tx_call_data_length.assign(
            region,
            offset,
            Value::known(F::from(tx.call_data.len() as u64)),
        )?;
        self.tx_call_data_gas_cost.assign(
            region,
            offset,
            Value::known(F::from(tx.call_data_gas_cost())),
        )?;
        self.tx_call_data_word_length
            .assign(region, offset, tx.call_data.len() as u128 + 31)?;
        self.reversion_info.assign(
            region,
            offset,
            call.rw_counter_end_of_reversion,
            call.is_persistent,
        )?;
        self.sufficient_gas_left
            .assign(region, offset, F::from(tx.gas() - step.gas_cost))?;
        self.transfer_with_gas_fee.assign(
            region,
            offset,
            caller_balance_sub_fee_pair,
            caller_balance_sub_value_pair,
            callee_balance_pair,
            tx.value,
            gas_fee,
        )?;
        self.code_hash
            .assign_u256(region, offset, callee_code_hash)?;
        self.is_empty_code_hash.assign_u256(
            region,
            offset,
            callee_code_hash,
            CodeDB::empty_code_hash().to_word(),
        )?;
        self.callee_not_exists
            .assign_u256(region, offset, callee_code_hash)?;

        let untrimmed_contract_addr = {
            let mut stream = ethers_core::utils::rlp::RlpStream::new();
            stream.begin_list(2);
            stream.append(&tx.from);
            stream.append(&tx.nonce.to_word());
            let rlp_encoding = stream.out().to_vec();
            keccak256(&rlp_encoding)
        };
        self.caller_nonce_hash_bytes.assign_u256(
            region,
            offset,
            U256::from_big_endian(&untrimmed_contract_addr),
        )?;
        self.create.assign(
            region,
            offset,
            tx.from,
            tx.nonce.as_u64(),
            Some(callee_code_hash),
            None,
        )?;

        self.coinbase
            .assign_h160(region, offset, block.context.coinbase)?;
        self.is_coinbase_warm.assign(
            region,
            offset,
            Value::known(F::from(is_coinbase_warm as u64)),
        )?;

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::{evm_circuit::test::rand_bytes, test_util::CircuitTestBuilder};
    use bus_mapping::evm::OpcodeId;
    use eth_types::{self, bytecode, evm_types::GasCost, word, Address, Bytecode, Word};
    use ethers_core::utils::get_contract_address;
    use mock::{eth, gwei, MockTransaction, TestContext, MOCK_ACCOUNTS};
    use std::vec;

    fn gas(call_data: &[u8]) -> Word {
        Word::from(
            GasCost::TX
                + 2 * OpcodeId::PUSH32.constant_gas_cost()
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
        let ctx = TestContext::<2, 1>::new(
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
        .unwrap();

        CircuitTestBuilder::new_from_test_ctx(ctx).run();
    }

    fn mock_tx(value: Word, gas_price: Word, calldata: Vec<u8>) -> eth_types::Transaction {
        let from = MOCK_ACCOUNTS[1];
        let to = MOCK_ACCOUNTS[0];

        let mock_transaction = MockTransaction::default()
            .from(from)
            .to(to)
            .value(value)
            .gas(gas(&calldata))
            .gas_price(gas_price)
            .input(calldata.into())
            .build();

        eth_types::Transaction::from(mock_transaction)
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
        let multibyte_nonce = 700;

        let to = MOCK_ACCOUNTS[0];
        let from = MOCK_ACCOUNTS[1];

        let code = bytecode! {
            STOP
        };

        let ctx = TestContext::<2, 1>::new(
            None,
            |accs| {
                accs[0].address(to).balance(eth(1)).code(code);
                accs[1].address(from).balance(eth(1)).nonce(multibyte_nonce);
            },
            |mut txs, _| {
                txs[0].to(to).from(from);
            },
            |block, _| block,
        )
        .unwrap();

        CircuitTestBuilder::new_from_test_ctx(ctx).run();
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
        let ctx = TestContext::<2, 1>::new(
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
        .unwrap();

        CircuitTestBuilder::new_from_test_ctx(ctx).run();
    }

    #[test]
    fn begin_tx_no_account() {
        let ctx = TestContext::<1, 1>::new(
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
        .unwrap();

        CircuitTestBuilder::new_from_test_ctx(ctx).run();
    }

    fn begin_tx_deploy(nonce: u64) {
        let code = bytecode! {
            // [ADDRESS, STOP]
            PUSH32(word!("3000000000000000000000000000000000000000000000000000000000000000"))
            PUSH1(0)
            MSTORE

            PUSH1(2)
            PUSH1(0)
            RETURN
        };
        let ctx = TestContext::<1, 1>::new(
            None,
            |accs| {
                accs[0]
                    .address(MOCK_ACCOUNTS[0])
                    .balance(eth(20))
                    .nonce(nonce);
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
        .unwrap();

        CircuitTestBuilder::new_from_test_ctx(ctx).run();
    }

    #[test]
    fn begin_tx_deploy_nonce_zero() {
        begin_tx_deploy(0);
    }
    #[test]
    fn begin_tx_deploy_nonce_small_1byte() {
        begin_tx_deploy(1);
        begin_tx_deploy(127);
    }
    #[test]
    fn begin_tx_deploy_nonce_big_1byte() {
        begin_tx_deploy(128);
        begin_tx_deploy(255);
    }
    #[test]
    fn begin_tx_deploy_nonce_2bytes() {
        begin_tx_deploy(0x0100u64);
        begin_tx_deploy(0x1020u64);
        begin_tx_deploy(0xffffu64);
    }
    #[test]
    fn begin_tx_deploy_nonce_3bytes() {
        begin_tx_deploy(0x010000u64);
        begin_tx_deploy(0x102030u64);
        begin_tx_deploy(0xffffffu64);
    }
    #[test]
    fn begin_tx_deploy_nonce_4bytes() {
        begin_tx_deploy(0x01000000u64);
        begin_tx_deploy(0x10203040u64);
        begin_tx_deploy(0xffffffffu64);
    }
    #[test]
    fn begin_tx_deploy_nonce_5bytes() {
        begin_tx_deploy(0x0100000000u64);
        begin_tx_deploy(0x1020304050u64);
        begin_tx_deploy(0xffffffffffu64);
    }
    #[test]
    fn begin_tx_deploy_nonce_6bytes() {
        begin_tx_deploy(0x010000000000u64);
        begin_tx_deploy(0x102030405060u64);
        begin_tx_deploy(0xffffffffffffu64);
    }
    #[test]
    fn begin_tx_deploy_nonce_7bytes() {
        begin_tx_deploy(0x01000000000000u64);
        begin_tx_deploy(0x10203040506070u64);
        begin_tx_deploy(0xffffffffffffffu64);
    }
    #[test]
    fn begin_tx_deploy_nonce_8bytes() {
        begin_tx_deploy(0x0100000000000000u64);
        begin_tx_deploy(0x1020304050607080u64);
        begin_tx_deploy(0xfffffffffffffffeu64);
    }

    #[test]
    fn create_tx_for_existing_account() {
        let address = Address::repeat_byte(23);
        let nonce = 10;
        let new_address = get_contract_address(address, nonce + 1);

        let ctx = TestContext::<1, 2>::new(
            None,
            |accs| {
                accs[0].address(address).nonce(nonce).balance(eth(10));
            },
            |mut txs, _| {
                txs[0].from(address).to(new_address).value(eth(2)); // Initialize new_address with some balance and an empty code hash
                txs[1].from(address); // Run a CREATE tx on new_address
            },
            |block, _| block,
        )
        .unwrap();

        CircuitTestBuilder::new_from_test_ctx(ctx).run();
    }
}
