use super::{
    constraint_builder::ConstrainBuilderCommon,
    from_bytes,
    math_gadget::{IsEqualWordGadget, IsZeroGadget, IsZeroWordGadget, LtGadget},
    memory_gadget::{CommonMemoryAddressGadget, MemoryExpansionGadget},
    AccountAddress, CachedRegion,
};
use crate::{
    evm_circuit::{
        param::{N_BYTES_GAS, N_BYTES_MEMORY_WORD_SIZE},
        step::ExecutionState,
        table::{FixedTableTag, Lookup},
        util::{
            and,
            constraint_builder::{
                EVMConstraintBuilder, ReversionInfo, StepStateTransition,
                Transition::{Delta, Same, To},
            },
            math_gadget::{AddWordsGadget, RangeCheckGadget},
            not, or, Cell,
        },
    },
    table::{chunk_ctx_table::chunk_ctxFieldTag, AccountFieldTag, CallContextFieldTag},
    util::{
        word::{Word, Word32, Word32Cell, WordCell, WordExpr},
        Expr,
    },
    witness::{Block, Call, Chunk, ExecStep},
};
use bus_mapping::state_db::CodeDB;
use eth_types::{evm_types::GasCost, Field, ToAddress, ToLittleEndian, ToScalar, ToWord, U256};
use gadgets::util::{select, sum};
use halo2_proofs::{
    circuit::Value,
    plonk::{Error, Expression},
};

/// Construction of execution state that stays in the same call context, which
/// lookups the opcode and verifies the execution state is responsible for it,
/// then calculates the gas_cost and constrain the state transition.
#[derive(Clone, Debug)]
pub(crate) struct SameContextGadget<F> {
    opcode: Cell<F>,
    sufficient_gas_left: RangeCheckGadget<F, N_BYTES_GAS>,
}

impl<F: Field> SameContextGadget<F> {
    pub(crate) fn construct(
        cb: &mut EVMConstraintBuilder<F>,
        opcode: Cell<F>,
        step_state_transition: StepStateTransition<F>,
    ) -> Self {
        cb.opcode_lookup(opcode.expr(), 1.expr());
        cb.add_lookup(
            "Responsible opcode lookup",
            Lookup::Fixed {
                tag: FixedTableTag::ResponsibleOpcode.expr(),
                values: [
                    cb.execution_state().as_u64().expr(),
                    opcode.expr(),
                    0.expr(),
                ],
            },
        );

        // Check gas_left is sufficient
        let sufficient_gas_left = RangeCheckGadget::construct(cb, cb.next.state.gas_left.expr());

        // Do step state transition
        cb.require_step_state_transition(step_state_transition);

        Self {
            opcode,
            sufficient_gas_left,
        }
    }

    pub(crate) fn assign_exec_step(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        step: &ExecStep,
    ) -> Result<(), Error> {
        let opcode = step.opcode().unwrap();
        self.opcode
            .assign(region, offset, Value::known(F::from(opcode.as_u64())))?;

        self.sufficient_gas_left
            .assign(region, offset, F::from(step.gas_left - step.gas_cost))?;

        Ok(())
    }
}

/// Construction of step state transition that restores caller's state.
#[derive(Clone, Debug)]
pub(crate) struct RestoreContextGadget<F> {
    caller_id: Cell<F>,
    caller_is_root: Cell<F>,
    caller_is_create: Cell<F>,
    caller_code_hash: WordCell<F>,
    caller_program_counter: Cell<F>,
    caller_stack_pointer: Cell<F>,
    caller_gas_left: Cell<F>,
    caller_memory_word_size: Cell<F>,
    caller_reversible_write_counter: Cell<F>,
}

impl<F: Field> RestoreContextGadget<F> {
    pub(crate) fn construct(
        cb: &mut EVMConstraintBuilder<F>,
        is_success: Expression<F>,
        // Expression for the number of rw lookups that occur after this gadget is constructed.
        subsequent_rw_lookups: Expression<F>,
        return_data_offset: Expression<F>,
        return_data_length: Expression<F>,
        memory_expansion_cost: Expression<F>,
        reversible_write_counter_increase: Expression<F>,
    ) -> Self {
        // Read caller's context for restore
        let caller_id = cb.call_context(None, CallContextFieldTag::CallerId);
        let [caller_is_root, caller_is_create] =
            [CallContextFieldTag::IsRoot, CallContextFieldTag::IsCreate]
                .map(|field_tag| cb.call_context(Some(caller_id.expr()), field_tag));

        let caller_code_hash =
            cb.call_context_read_as_word(Some(caller_id.expr()), CallContextFieldTag::CodeHash);

        let [caller_program_counter, caller_stack_pointer, caller_gas_left, caller_memory_word_size, caller_reversible_write_counter] =
            [
                CallContextFieldTag::ProgramCounter,
                CallContextFieldTag::StackPointer,
                CallContextFieldTag::GasLeft,
                CallContextFieldTag::MemorySize,
                CallContextFieldTag::ReversibleWriteCounter,
            ]
            .map(|field_tag| cb.call_context(Some(caller_id.expr()), field_tag));

        // Update caller's last callee information
        // EIP-211 CREATE/CREATE2 call successful case should set RETURNDATASIZE = 0
        let is_call_create_and_success_expr = cb.curr.state.is_create.expr() * is_success.clone();
        for (field_tag, value) in [
            (
                CallContextFieldTag::LastCalleeId,
                cb.curr.state.call_id.expr(),
            ),
            (
                CallContextFieldTag::LastCalleeReturnDataOffset,
                select::expr(
                    is_call_create_and_success_expr.clone(),
                    0.expr(),
                    return_data_offset,
                ),
            ),
            (
                CallContextFieldTag::LastCalleeReturnDataLength,
                select::expr(
                    is_call_create_and_success_expr,
                    0.expr(),
                    return_data_length.clone(),
                ),
            ),
        ] {
            // TODO review and assure range check
            cb.call_context_lookup_write(
                Some(caller_id.expr()),
                field_tag,
                Word::from_lo_unchecked(value),
            );
        }

        let code_deposit_cost = cb.curr.state.is_create.expr()
            * is_success.clone()
            * GasCost::CODE_DEPOSIT_BYTE_COST.expr()
            * return_data_length;

        let gas_refund = if cb.execution_state().halts_in_exception() {
            0.expr() // no gas refund if call halts in exception
        } else {
            cb.curr.state.gas_left.expr() - memory_expansion_cost - code_deposit_cost
        };

        let gas_left = caller_gas_left.expr() + gas_refund;

        // Accumulate reversible_write_counter in case this call stack reverts in the
        // future even it itself succeeds. Note that when sub-call halts in
        // failure, we don't need to accumulate reversible_write_counter because
        // what happened in the sub-call has been reverted.
        let reversible_write_counter = caller_reversible_write_counter.expr()
            + reversible_write_counter_increase
            + is_success.clone() * cb.curr.state.reversible_write_counter.expr();

        let rw_counter_offset = cb.rw_counter_offset()
            + subsequent_rw_lookups
            + not::expr(is_success.expr()) * cb.curr.state.reversible_write_counter.expr();

        // Do step state transition
        cb.require_step_state_transition(StepStateTransition {
            rw_counter: Delta(rw_counter_offset),
            call_id: To(caller_id.expr()),
            is_root: To(caller_is_root.expr()),
            is_create: To(caller_is_create.expr()),
            code_hash: To(caller_code_hash.to_word()),
            program_counter: To(caller_program_counter.expr()),
            stack_pointer: To(caller_stack_pointer.expr()),
            gas_left: To(gas_left),
            memory_word_size: To(caller_memory_word_size.expr()),
            reversible_write_counter: To(reversible_write_counter),
            ..Default::default()
        });

        Self {
            caller_id,
            caller_is_root,
            caller_is_create,
            caller_code_hash,
            caller_program_counter,
            caller_stack_pointer,
            caller_gas_left,
            caller_memory_word_size,
            caller_reversible_write_counter,
        }
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        block: &Block<F>,
        call: &Call,
        step: &ExecStep,
        rw_offset: usize,
    ) -> Result<(), Error> {
        let [caller_id, caller_is_root, caller_is_create, caller_code_hash, caller_program_counter, caller_stack_pointer, caller_gas_left, caller_memory_word_size, caller_reversible_write_counter] =
            if call.is_root {
                [U256::zero(); 9]
            } else {
                [0, 1, 2, 3, 4, 5, 6, 7, 8]
                    .map(|i| block.get_rws(step, i + rw_offset).call_context_value())
            };

        for (cell, value) in [
            (&self.caller_id, caller_id),
            (&self.caller_is_root, caller_is_root),
            (&self.caller_is_create, caller_is_create),
            (&self.caller_program_counter, caller_program_counter),
            (&self.caller_stack_pointer, caller_stack_pointer),
            (&self.caller_gas_left, caller_gas_left),
            (&self.caller_memory_word_size, caller_memory_word_size),
            (
                &self.caller_reversible_write_counter,
                caller_reversible_write_counter,
            ),
        ] {
            cell.assign(
                region,
                offset,
                Value::known(
                    value
                        .to_scalar()
                        .expect("unexpected U256 -> Scalar conversion failure"),
                ),
            )?;
        }

        self.caller_code_hash
            .assign_u256(region, offset, caller_code_hash)?;

        Ok(())
    }
}

#[derive(Clone, Debug)]
pub(crate) struct UpdateBalanceGadget<F, const N_ADDENDS: usize, const INCREASE: bool> {
    add_words: AddWordsGadget<F, N_ADDENDS, true>,
}

impl<F: Field, const N_ADDENDS: usize, const INCREASE: bool>
    UpdateBalanceGadget<F, N_ADDENDS, INCREASE>
{
    pub(crate) fn construct(
        cb: &mut EVMConstraintBuilder<F>,
        address: Word<Expression<F>>,
        updates: Vec<Word32Cell<F>>,
        reversion_info: Option<&mut ReversionInfo<F>>,
    ) -> Self {
        debug_assert!(updates.len() == N_ADDENDS - 1);

        let balance_addend = cb.query_word32();
        let balance_sum = cb.query_word32();

        let [value, value_prev]: [Word32<Expression<F>>; 2] = if INCREASE {
            [balance_sum.to_word_n(), balance_addend.to_word_n()]
        } else {
            [balance_addend.to_word_n(), balance_sum.to_word_n()]
        };

        let add_words = AddWordsGadget::construct(
            cb,
            std::iter::once(balance_addend)
                .chain(updates.to_vec())
                .collect::<Vec<_>>()
                .try_into()
                .unwrap(),
            balance_sum,
        );

        cb.account_write(
            address,
            AccountFieldTag::Balance,
            value.to_word(),
            value_prev.to_word(),
            reversion_info,
        );

        Self { add_words }
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        value_prev: U256,
        updates: Vec<U256>,
        value: U256,
    ) -> Result<(), Error> {
        debug_assert!(updates.len() + 1 == N_ADDENDS);

        let [value, value_prev] = if INCREASE {
            [value, value_prev]
        } else {
            [value_prev, value]
        };
        let mut addends = vec![value_prev];
        addends.extend(updates);
        self.add_words
            .assign(region, offset, addends.try_into().unwrap(), value)
    }
}

#[derive(Clone, Debug)]
pub(crate) struct TransferToGadget<F> {
    receiver: UpdateBalanceGadget<F, 2, true>,
    receiver_exists: Expression<F>,
    must_create: Expression<F>,
    pub(crate) value_is_zero: IsZeroWordGadget<F, Word32Cell<F>>,
}

impl<F: Field> TransferToGadget<F> {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn construct(
        cb: &mut EVMConstraintBuilder<F>,
        receiver_address: Word<Expression<F>>,
        receiver_exists: Expression<F>,
        must_create: Expression<F>,
        value: Word32Cell<F>,
        mut reversion_info: Option<&mut ReversionInfo<F>>,
        account_write: bool,
    ) -> Self {
        let value_is_zero = IsZeroWordGadget::construct(cb, &value);
        if account_write {
            Self::create_account(
                cb,
                receiver_address.clone(),
                receiver_exists.clone(),
                must_create.clone(),
                value_is_zero.expr(),
                reversion_info.as_deref_mut(),
            );
        }
        let receiver = cb.condition(not::expr(value_is_zero.expr()), |cb| {
            UpdateBalanceGadget::construct(
                cb,
                receiver_address,
                vec![value.clone()],
                reversion_info,
            )
        });

        Self {
            receiver,
            receiver_exists,
            must_create,
            value_is_zero,
        }
    }

    pub(crate) fn create_account(
        cb: &mut EVMConstraintBuilder<F>,
        receiver_address: Word<Expression<F>>,
        receiver_exists: Expression<F>,
        must_create: Expression<F>,
        value_is_zero: Expression<F>,
        reversion_info: Option<&mut ReversionInfo<F>>,
    ) {
        cb.condition(
            and::expr([
                not::expr(receiver_exists.expr()),
                or::expr([not::expr(value_is_zero.expr()), must_create]),
            ]),
            |cb| {
                cb.account_write(
                    receiver_address.clone(),
                    AccountFieldTag::CodeHash,
                    cb.empty_code_hash(),
                    Word::zero(),
                    reversion_info,
                );
            },
        );
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        (receiver_balance, prev_receiver_balance): (U256, U256),
        value: U256,
    ) -> Result<(), Error> {
        self.receiver.assign(
            region,
            offset,
            prev_receiver_balance,
            vec![value],
            receiver_balance,
        )?;
        self.value_is_zero
            .assign_value(region, offset, Value::known(Word::from(value)))?;
        Ok(())
    }

    pub(crate) fn rw_delta(&self) -> Expression<F> {
        // +1 Write Account (receiver) CodeHash (account creation via code_hash update)
        and::expr([
                not::expr(self.receiver_exists.expr()),
                or::expr([not::expr(self.value_is_zero.expr()), self.must_create.clone()]),
            ]) +
        // +1 Write Account (receiver) Balance
        not::expr(self.value_is_zero.expr())
    }
}

// TODO: Merge with TransferGadget
/// The TransferWithGasFeeGadget handles an irreversible gas fee subtraction to
/// the sender and a transfer of value from sender to receiver.  The value
/// transfer is only performed if the value is not zero.  If the transfer is
/// performed and the receiver account doesn't exist, it will be created by
/// setting it's code_hash = EMPTY_HASH.   The receiver account is also created
/// unconditionally if must_create is true.  This gadget is used in BeginTx.
#[derive(Clone, Debug)]
pub(crate) struct TransferWithGasFeeGadget<F> {
    sender_sub_fee: UpdateBalanceGadget<F, 2, false>,
    sender_sub_value: UpdateBalanceGadget<F, 2, false>,
    receiver: TransferToGadget<F>,
    pub(crate) value_is_zero: IsZeroWordGadget<F, Word32Cell<F>>,
}

impl<F: Field> TransferWithGasFeeGadget<F> {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn construct(
        cb: &mut EVMConstraintBuilder<F>,
        sender_address: Word<Expression<F>>,
        receiver_address: Word<Expression<F>>,
        receiver_exists: Expression<F>,
        must_create: Expression<F>,
        value: Word32Cell<F>,
        gas_fee: Word32Cell<F>,
        reversion_info: &mut ReversionInfo<F>,
    ) -> Self {
        let sender_sub_fee =
            UpdateBalanceGadget::construct(cb, sender_address.to_word(), vec![gas_fee], None);
        let value_is_zero = IsZeroWordGadget::construct(cb, &value);
        // If receiver doesn't exist, create it
        TransferToGadget::create_account(
            cb,
            receiver_address.clone(),
            receiver_exists.clone(),
            must_create.clone(),
            value_is_zero.expr(),
            Some(reversion_info),
        );
        // Skip transfer if value == 0
        let sender_sub_value = cb.condition(not::expr(value_is_zero.expr()), |cb| {
            UpdateBalanceGadget::construct(
                cb,
                sender_address,
                vec![value.clone()],
                Some(reversion_info),
            )
        });
        let receiver = TransferToGadget::construct(
            cb,
            receiver_address,
            receiver_exists,
            must_create,
            value,
            Some(reversion_info),
            false,
        );

        Self {
            sender_sub_fee,
            sender_sub_value,
            receiver,
            value_is_zero,
        }
    }

    pub(crate) fn rw_delta(&self) -> Expression<F> {
        // +1 Write Account (sender) Balance (Not Reversible tx fee)
        1.expr() +
        // +1 Write Account (receiver) CodeHash (account creation via code_hash update)
        and::expr([not::expr(self.receiver.receiver_exists.expr()), or::expr([
            not::expr(self.value_is_zero.expr()),
            self.receiver.must_create.clone()]
        )]) * 1.expr() +
        // +1 Write Account (sender) Balance
        // +1 Write Account (receiver) Balance
        not::expr(self.value_is_zero.expr()) * 2.expr()
    }

    pub(crate) fn reversible_w_delta(&self) -> Expression<F> {
        // NOTE: Write Account (sender) Balance (Not Reversible tx fee)
        // +1 Write Account (receiver) CodeHash (account creation via code_hash update)
        and::expr([not::expr(self.receiver.receiver_exists.expr()), or::expr([
            not::expr(self.value_is_zero.expr()),
            self.receiver.must_create.clone()]
        )]) +
        // +1 Write Account (sender) Balance
        // +1 Write Account (receiver) Balance
        not::expr(self.value_is_zero.expr()) * 2.expr()
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        (sender_balance_sub_fee, prev_sender_balance_sub_fee): (U256, U256),
        (sender_balance_sub_value, prev_sender_balance_sub_value): (U256, U256),
        (receiver_balance, prev_receiver_balance): (U256, U256),
        value: U256,
        gas_fee: U256,
    ) -> Result<(), Error> {
        self.sender_sub_fee.assign(
            region,
            offset,
            prev_sender_balance_sub_fee,
            vec![gas_fee],
            sender_balance_sub_fee,
        )?;
        self.sender_sub_value.assign(
            region,
            offset,
            prev_sender_balance_sub_value,
            vec![value],
            sender_balance_sub_value,
        )?;
        self.receiver.assign(
            region,
            offset,
            (receiver_balance, prev_receiver_balance),
            value,
        )?;
        self.value_is_zero
            .assign_value(region, offset, Value::known(Word::from(value)))?;
        Ok(())
    }
}

/// The TransferGadget handles a transfer of value from sender to receiver.  The
/// transfer is only performed if the value is not zero.  If the transfer is
/// performed and the receiver account doesn't exist, it will be created by
/// setting it's code_hash = EMPTY_HASH. This gadget is used in callop.
#[derive(Clone, Debug)]
pub(crate) struct TransferGadget<F> {
    sender: UpdateBalanceGadget<F, 2, false>,
    receiver: TransferToGadget<F>,
    pub(crate) value_is_zero: IsZeroWordGadget<F, Word32Cell<F>>,
}

impl<F: Field> TransferGadget<F> {
    pub(crate) fn construct(
        cb: &mut EVMConstraintBuilder<F>,
        sender_address: Word<Expression<F>>,
        receiver_address: Word<Expression<F>>,
        receiver_exists: Expression<F>,
        must_create: Expression<F>,
        value: Word32Cell<F>,
        reversion_info: &mut ReversionInfo<F>,
    ) -> Self {
        let value_is_zero = IsZeroWordGadget::construct(cb, &value);
        // If receiver doesn't exist, create it
        TransferToGadget::create_account(
            cb,
            receiver_address.clone(),
            receiver_exists.clone(),
            must_create.clone(),
            value_is_zero.expr(),
            Some(reversion_info),
        );
        // Skip transfer if value == 0
        let sender = cb.condition(not::expr(value_is_zero.expr()), |cb| {
            UpdateBalanceGadget::construct(
                cb,
                sender_address,
                vec![value.clone()],
                Some(reversion_info),
            )
        });
        let receiver = TransferToGadget::construct(
            cb,
            receiver_address,
            receiver_exists,
            must_create,
            value,
            Some(reversion_info),
            false,
        );

        Self {
            sender,
            receiver,
            value_is_zero,
        }
    }

    pub(crate) fn reversible_w_delta(&self) -> Expression<F> {
        // +1 Write Account (receiver) CodeHash (account creation via code_hash update)
        or::expr([
                        not::expr(self.value_is_zero.expr()) * not::expr(self.receiver.receiver_exists.clone()),
                        self.receiver.must_create.clone()]
                    ) * 1.expr() +
        // +1 Write Account (sender) Balance
        // +1 Write Account (receiver) Balance
        not::expr(self.value_is_zero.expr()) * 2.expr()
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        (sender_balance, sender_balance_prev): (U256, U256),
        (receiver_balance, receiver_balance_prev): (U256, U256),
        value: U256,
    ) -> Result<(), Error> {
        self.sender.assign(
            region,
            offset,
            sender_balance_prev,
            vec![value],
            sender_balance,
        )?;
        self.receiver.assign(
            region,
            offset,
            (receiver_balance, receiver_balance_prev),
            value,
        )?;
        self.value_is_zero
            .assign_value(region, offset, Value::known(Word::from(value)))?;
        Ok(())
    }
}

#[derive(Clone, Debug)]
pub(crate) struct CommonCallGadget<F, MemAddrGadget, const IS_SUCCESS_CALL: bool> {
    pub is_success: Cell<F>,

    pub gas: Word32Cell<F>,
    pub gas_is_u64: IsZeroGadget<F>,
    pub callee_address: AccountAddress<F>,
    pub value: Word32Cell<F>,
    pub cd_address: MemAddrGadget,
    pub rd_address: MemAddrGadget,
    pub memory_expansion: MemoryExpansionGadget<F, 2, N_BYTES_MEMORY_WORD_SIZE>,

    value_is_zero: IsZeroWordGadget<F, Word32Cell<F>>,
    pub has_value: Expression<F>,
    pub callee_code_hash: WordCell<F>,
    pub is_empty_code_hash: IsEqualWordGadget<F, WordCell<F>, Word<Expression<F>>>,

    pub callee_not_exists: IsZeroWordGadget<F, WordCell<F>>,
}

impl<F: Field, MemAddrGadget: CommonMemoryAddressGadget<F>, const IS_SUCCESS_CALL: bool>
    CommonCallGadget<F, MemAddrGadget, IS_SUCCESS_CALL>
{
    pub(crate) fn construct(
        cb: &mut EVMConstraintBuilder<F>,
        is_call: Expression<F>,
        is_callcode: Expression<F>,
        is_delegatecall: Expression<F>,
        is_staticcall: Expression<F>,
    ) -> Self {
        // Constrain opcode must be one of CALL, CALLCODE, DELEGATECALL or STATICCALL.
        cb.require_equal(
            "Opcode should be CALL, CALLCODE, DELEGATECALL or STATICCALL",
            is_call.expr() + is_callcode.expr() + is_delegatecall.expr() + is_staticcall.expr(),
            1.expr(),
        );

        let gas_word = cb.query_word32();
        let callee_address = cb.query_account_address();
        let value = cb.query_word32();
        let is_success = cb.query_bool();

        let cd_address = MemAddrGadget::construct_self(cb);
        let rd_address = MemAddrGadget::construct_self(cb);
        // Lookup values from stack
        // `callee_address` is poped from stack and used to check if it exists in
        // access list and get code hash.
        // For CALLCODE, both caller and callee addresses are `current_callee_address`.
        // For DELEGATECALL, caller address is `current_caller_address` and
        // callee address is `current_callee_address`.
        // For both CALL and STATICCALL, caller address is
        // `current_callee_address` and callee address is `callee_address`.
        cb.stack_pop(gas_word.to_word());
        cb.stack_pop(callee_address.to_word());

        // `CALL` and `CALLCODE` opcodes have an additional stack pop `value`.
        cb.condition(is_call + is_callcode, |cb| cb.stack_pop(value.to_word()));
        cb.stack_pop(cd_address.offset_word());
        cb.stack_pop(cd_address.length_word());
        cb.stack_pop(rd_address.offset_word());
        cb.stack_pop(rd_address.length_word());
        cb.stack_push(if IS_SUCCESS_CALL {
            Word::from_lo_unchecked(is_success.expr()) // is_success is bool
        } else {
            Word::zero()
        });

        // Recomposition of random linear combination to integer
        let gas_is_u64 = IsZeroGadget::construct(cb, sum::expr(&gas_word.limbs[N_BYTES_GAS..]));
        let memory_expansion =
            MemoryExpansionGadget::construct(cb, [cd_address.address(), rd_address.address()]);

        // construct common gadget
        let value_is_zero = IsZeroWordGadget::construct(cb, &value);
        let has_value = select::expr(
            is_delegatecall.expr() + is_staticcall.expr(),
            0.expr(),
            1.expr() - value_is_zero.expr(),
        );

        let callee_code_hash = cb.query_word_unchecked();
        cb.account_read(
            callee_address.to_word(),
            AccountFieldTag::CodeHash,
            callee_code_hash.to_word(),
        );
        let is_empty_code_hash =
            IsEqualWordGadget::construct(cb, &callee_code_hash, &cb.empty_code_hash());
        let callee_not_exists = IsZeroWordGadget::construct(cb, &callee_code_hash);

        Self {
            is_success,
            callee_address,
            gas: gas_word,
            gas_is_u64,
            value,
            cd_address,
            rd_address,
            memory_expansion,
            value_is_zero,
            has_value,
            callee_code_hash,
            is_empty_code_hash,
            callee_not_exists,
        }
    }

    pub fn callee_address(&self) -> Word<Expression<F>> {
        self.callee_address.to_word()
    }

    pub fn gas_expr(&self) -> Expression<F> {
        from_bytes::expr(&self.gas.limbs[..N_BYTES_GAS])
    }

    pub fn gas_cost_expr(
        &self,
        is_warm_prev: Expression<F>,
        is_call: Expression<F>,
    ) -> Expression<F> {
        select::expr(
            is_warm_prev,
            GasCost::WARM_ACCESS.expr(),
            GasCost::COLD_ACCOUNT_ACCESS.expr(),
        ) + self.has_value.clone()
            * (GasCost::CALL_WITH_VALUE.expr()
                // Only CALL opcode could invoke transfer to make empty account into non-empty.
                + is_call * self.callee_not_exists.expr() * GasCost::NEW_ACCOUNT.expr())
            + self.memory_expansion.gas_cost()
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        gas: U256,
        callee_address: U256,
        value: U256,
        is_success: U256,
        cd_offset: U256,
        cd_length: U256,
        rd_offset: U256,
        rd_length: U256,
        memory_word_size: u64,
        callee_code_hash: U256,
    ) -> Result<u64, Error> {
        self.gas.assign_u256(region, offset, gas)?;
        self.callee_address
            .assign_h160(region, offset, callee_address.to_address())?;
        self.value.assign_u256(region, offset, value)?;
        if IS_SUCCESS_CALL {
            self.is_success
                .assign(region, offset, Value::known(F::from(is_success.low_u64())))?;
        }
        self.gas_is_u64.assign(
            region,
            offset,
            sum::value(&gas.to_le_bytes()[N_BYTES_GAS..]),
        )?;
        let cd_address = self
            .cd_address
            .assign(region, offset, cd_offset, cd_length)?;
        let rd_address = self
            .rd_address
            .assign(region, offset, rd_offset, rd_length)?;
        let (_, memory_expansion_gas_cost) = self.memory_expansion.assign(
            region,
            offset,
            memory_word_size,
            [cd_address, rd_address],
        )?;

        self.value_is_zero
            .assign(region, offset, Word::from(value))?;
        self.callee_code_hash
            .assign_u256(region, offset, callee_code_hash)?;
        self.is_empty_code_hash.assign_value(
            region,
            offset,
            Value::known(Word::from(callee_code_hash)),
            Value::known(Word::from(CodeDB::empty_code_hash().to_word())),
        )?;
        self.callee_not_exists.assign_value(
            region,
            offset,
            Value::known(Word::from(callee_code_hash)),
        )?;
        Ok(memory_expansion_gas_cost)
    }

    pub(crate) fn cal_gas_cost_for_assignment(
        &self,
        memory_expansion_gas_cost: u64,
        is_warm_prev: bool,
        is_call: bool,
        has_value: bool,
        is_empty_account: bool,
    ) -> Result<u64, Error> {
        let gas_cost = if is_warm_prev {
            GasCost::WARM_ACCESS
        } else {
            GasCost::COLD_ACCOUNT_ACCESS
        } + if has_value {
            GasCost::CALL_WITH_VALUE
                // Only CALL opcode could invoke transfer to make empty account into non-empty.
                + if is_call && is_empty_account {
                    GasCost::NEW_ACCOUNT
                } else {
                    0
                }
        } else {
            0
        } + memory_expansion_gas_cost;

        Ok(gas_cost)
    }
}

#[derive(Clone, Debug)]
pub(crate) struct SloadGasGadget<F> {
    gas_cost: Expression<F>,
}

impl<F: Field> SloadGasGadget<F> {
    pub(crate) fn construct(_cb: &mut EVMConstraintBuilder<F>, is_warm: Expression<F>) -> Self {
        let gas_cost = select::expr(
            is_warm.expr(),
            GasCost::WARM_ACCESS.expr(),
            GasCost::COLD_SLOAD.expr(),
        );

        Self { gas_cost }
    }

    pub(crate) fn expr(&self) -> Expression<F> {
        // Return the gas cost
        self.gas_cost.clone()
    }
}

#[derive(Clone, Debug)]
pub(crate) struct SstoreGasGadget<F, T> {
    is_warm: Cell<F>,
    gas_cost: Expression<F>,
    value_eq_prev: IsEqualWordGadget<F, T, T>,
    original_eq_prev: IsEqualWordGadget<F, T, T>,
    original_is_zero: IsZeroWordGadget<F, T>,
}

impl<F: Field, T: WordExpr<F> + Clone> SstoreGasGadget<F, T> {
    pub(crate) fn construct(
        cb: &mut EVMConstraintBuilder<F>,
        is_warm: Cell<F>,
        value: T,
        value_prev: T,
        original_value: T,
    ) -> Self {
        let value_eq_prev = IsEqualWordGadget::construct(cb, &value, &value_prev);
        let original_eq_prev = IsEqualWordGadget::construct(cb, &original_value, &value_prev);
        let original_is_zero = IsZeroWordGadget::construct(cb, &original_value);
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
    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        value: eth_types::Word,
        value_prev: eth_types::Word,
        original_value: eth_types::Word,
        is_warm: bool,
    ) -> Result<(), Error> {
        self.is_warm
            .assign(region, offset, Value::known(F::from(is_warm as u64)))?;
        self.value_eq_prev.assign_value(
            region,
            offset,
            Value::known(Word::from(value)),
            Value::known(Word::from(value_prev)),
        )?;
        self.original_eq_prev.assign_value(
            region,
            offset,
            Value::known(Word::from(original_value)),
            Value::known(Word::from(value_prev)),
        )?;
        self.original_is_zero.assign_value(
            region,
            offset,
            Value::known(Word::from(original_value)),
        )?;
        Ok(())
    }
}

pub(crate) fn cal_sload_gas_cost_for_assignment(is_warm: bool) -> u64 {
    if is_warm {
        GasCost::WARM_ACCESS
    } else {
        GasCost::COLD_SLOAD
    }
}

pub(crate) fn cal_sstore_gas_cost_for_assignment(
    value: U256,
    value_prev: U256,
    original_value: U256,
    is_warm: bool,
) -> u64 {
    let warm_case_gas = if value_prev == value {
        GasCost::WARM_ACCESS
    } else if original_value == value_prev {
        if original_value.is_zero() {
            GasCost::SSTORE_SET
        } else {
            GasCost::SSTORE_RESET
        }
    } else {
        GasCost::WARM_ACCESS
    };
    if is_warm {
        warm_case_gas
    } else {
        warm_case_gas + GasCost::COLD_SLOAD
    }
}

#[derive(Clone, Debug)]
pub(crate) struct CommonErrorGadget<F> {
    rw_counter_end_of_reversion: WordCell<F>,
    restore_context: RestoreContextGadget<F>,
}

impl<F: Field> CommonErrorGadget<F> {
    pub(crate) fn construct(
        cb: &mut EVMConstraintBuilder<F>,
        opcode: Expression<F>,
        rw_counter_delta: Expression<F>,
    ) -> Self {
        Self::construct_with_return_data(cb, opcode, rw_counter_delta, 0.expr(), 0.expr())
    }

    pub(crate) fn construct_with_return_data(
        cb: &mut EVMConstraintBuilder<F>,
        opcode: Expression<F>,
        rw_counter_delta: Expression<F>,
        return_data_offset: Expression<F>,
        return_data_length: Expression<F>,
    ) -> Self {
        cb.opcode_lookup(opcode.expr(), 1.expr());

        let rw_counter_end_of_reversion = cb.query_word_unchecked(); // rw_counter_end_of_reversion just used for read lookup, therefore skip range check

        // current call must be failed.
        cb.call_context_lookup_read(None, CallContextFieldTag::IsSuccess, Word::zero());

        cb.call_context_lookup_read(
            None,
            CallContextFieldTag::RwCounterEndOfReversion,
            rw_counter_end_of_reversion.to_word(),
        );
        // Have two rw lookups, `IsSuccess` and `RwCounterEndOfReversion` so we add `2` here.
        let updated_rw_counter_delta = rw_counter_delta + 2.expr();

        // Go to EndTx only when is_root
        let is_to_end_tx = cb.next.execution_state_selector([ExecutionState::EndTx]);
        cb.require_equal(
            "Go to EndTx only when is_root",
            cb.curr.state.is_root.expr(),
            is_to_end_tx,
        );

        // When it's a root call
        cb.condition(cb.curr.state.is_root.expr(), |cb| {
            // Do step state transition
            cb.require_step_state_transition(StepStateTransition {
                call_id: Same,
                rw_counter: Delta(
                    updated_rw_counter_delta + cb.curr.state.reversible_write_counter.expr(),
                ),
                ..StepStateTransition::any()
            });
        });

        // When it's an internal call, need to restore caller's state as finishing this
        // call. Restore caller state to next StepState
        let restore_context = cb.condition(1.expr() - cb.curr.state.is_root.expr(), |cb| {
            RestoreContextGadget::construct(
                cb,
                0.expr(),
                0.expr(),
                return_data_offset,
                return_data_length,
                0.expr(),
                0.expr(),
            )
        });

        // constrain RwCounterEndOfReversion
        let rw_counter_end_of_step =
            cb.curr.state.rw_counter.expr() + cb.rw_counter_offset() - 1.expr();
        cb.require_equal(
            "rw_counter_end_of_reversion = rw_counter_end_of_step + reversible_counter",
            rw_counter_end_of_reversion.lo().expr(),
            rw_counter_end_of_step + cb.curr.state.reversible_write_counter.expr(),
        );

        Self {
            rw_counter_end_of_reversion,
            restore_context,
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        block: &Block<F>,
        call: &Call,
        step: &ExecStep,
        rw_offset: usize,
    ) -> Result<u64, Error> {
        self.rw_counter_end_of_reversion.assign_u64(
            region,
            offset,
            call.rw_counter_end_of_reversion as u64,
        )?;
        self.restore_context
            .assign(region, offset, block, call, step, rw_offset)?;

        // NOTE: return value not use for now.
        Ok(1u64)
    }
}

/// Check if the passed in word is within the specified byte range
/// (not overflow) and less than a maximum cap.
#[derive(Clone, Debug)]
pub(crate) struct WordByteCapGadget<F, const VALID_BYTES: usize> {
    word: WordByteRangeGadget<F, VALID_BYTES>,
    lt_cap: LtGadget<F, VALID_BYTES>,
}

impl<F: Field, const VALID_BYTES: usize> WordByteCapGadget<F, VALID_BYTES> {
    pub(crate) fn construct(cb: &mut EVMConstraintBuilder<F>, cap: Expression<F>) -> Self {
        let word = WordByteRangeGadget::construct(cb);
        let value = select::expr(word.overflow(), cap.expr(), word.valid_value());
        let lt_cap = LtGadget::construct(cb, value, cap);

        Self { word, lt_cap }
    }

    /// Return true if within the specified byte range (not overflow), false if
    /// overflow. No matter whether it is less than the cap.
    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        original: U256,
        cap: F,
    ) -> Result<bool, Error> {
        let not_overflow = self.word.assign(region, offset, original)?;

        let value = if not_overflow {
            let mut bytes = [0; 32];
            bytes[0..VALID_BYTES].copy_from_slice(&original.to_le_bytes()[0..VALID_BYTES]);
            F::from_repr(bytes).unwrap()
        } else {
            cap
        };

        self.lt_cap.assign(region, offset, value, cap)?;

        Ok(not_overflow)
    }

    pub(crate) fn lt_cap(&self) -> Expression<F> {
        self.lt_cap.expr()
    }

    pub(crate) fn original_word(&self) -> Word32Cell<F> {
        self.word.original.clone()
    }

    pub(crate) fn overflow(&self) -> Expression<F> {
        self.word.overflow()
    }

    pub(crate) fn valid_value(&self) -> Expression<F> {
        self.word.valid_value()
    }

    pub(crate) fn not_overflow(&self) -> Expression<F> {
        self.word.not_overflow()
    }
}

/// Check if the passed in word is within the specified byte range (not overflow).
#[derive(Clone, Debug)]
pub(crate) struct WordByteRangeGadget<F, const VALID_BYTES: usize> {
    original: Word32Cell<F>,
    not_overflow: IsZeroGadget<F>,
}

impl<F: Field, const VALID_BYTES: usize> WordByteRangeGadget<F, VALID_BYTES> {
    pub(crate) fn construct(cb: &mut EVMConstraintBuilder<F>) -> Self {
        debug_assert!(VALID_BYTES < 32);

        let original = cb.query_word32();
        let not_overflow = IsZeroGadget::construct(cb, sum::expr(&original.limbs[VALID_BYTES..]));

        Self {
            original,
            not_overflow,
        }
    }

    /// Return true if within the range, false if overflow.
    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        original: U256,
    ) -> Result<bool, Error> {
        self.original.assign_u256(region, offset, original)?;

        let overflow_hi = original.to_le_bytes()[VALID_BYTES..]
            .iter()
            .fold(0, |acc, val| acc + u64::from(*val));
        self.not_overflow
            .assign(region, offset, F::from(overflow_hi))?;

        Ok(overflow_hi == 0)
    }

    pub(crate) fn overflow(&self) -> Expression<F> {
        not::expr(self.not_overflow())
    }

    pub(crate) fn original(&self) -> Word<Expression<F>> {
        self.original.to_word()
    }

    pub(crate) fn valid_value(&self) -> Expression<F> {
        from_bytes::expr(&self.original.limbs[..VALID_BYTES])
    }

    pub(crate) fn not_overflow(&self) -> Expression<F> {
        self.not_overflow.expr()
    }
}

/// current SRS size < 2^30 so use 4 bytes (2^32) in LtGadet should be enough
const MAX_RW_BYTES: usize = u32::BITS as usize / 8;

/// Check consecutive Rw::Padding in rw_table to assure rw_table no malicious insertion
#[derive(Clone, Debug)]
pub(crate) struct RwTablePaddingGadget<F> {
    is_empty_rwc: IsZeroGadget<F>,
    max_rws: Cell<F>,
    chunk_index: Cell<F>,
    is_end_padding_exist: LtGadget<F, MAX_RW_BYTES>,
    is_first_chunk: IsZeroGadget<F>,
}

impl<F: Field> RwTablePaddingGadget<F> {
    pub(crate) fn construct(
        cb: &mut EVMConstraintBuilder<F>,
        inner_rws_before_padding: Expression<F>,
    ) -> Self {
        let max_rws = cb.query_copy_cell();
        let chunk_index = cb.query_cell();
        let is_empty_rwc =
            IsZeroGadget::construct(cb, cb.curr.state.rw_counter.clone().expr() - 1.expr());

        cb.chunk_context_lookup(chunk_ctxFieldTag::CurrentChunkIndex, chunk_index.expr());
        let is_first_chunk = IsZeroGadget::construct(cb, chunk_index.expr());

        // Verify rw_counter counts to the same number of meaningful rows in
        // rw_table to ensure there is no malicious insertion.
        // Verify that there are at most total_rws meaningful entries in the rw_table
        // - startop only exist in first chunk
        // - end paddings are consecutively
        cb.condition(is_first_chunk.expr(), |cb| {
            cb.rw_table_start_lookup(1.expr());
        });

        let is_end_padding_exist = LtGadget::<_, MAX_RW_BYTES>::construct(
            cb,
            1.expr(),
            max_rws.expr() - inner_rws_before_padding.expr(),
        );
        cb.condition(is_end_padding_exist.expr(), |cb| {
            cb.rw_table_padding_lookup(inner_rws_before_padding.expr() + 1.expr());
            cb.rw_table_padding_lookup(max_rws.expr() - 1.expr());
        });
        // Since every lookup done in the EVM circuit must succeed and uses
        // a unique rw_counter, we know that at least there are
        // total_rws meaningful entries in the rw_table.
        // We conclude that the number of meaningful entries in the rw_table
        // is total_rws.

        Self {
            is_empty_rwc,
            max_rws,
            chunk_index,
            is_first_chunk,
            is_end_padding_exist,
        }
    }

    pub(crate) fn assign_exec_step(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        _block: &Block<F>,
        chunk: &Chunk<F>,
        inner_rws_before_padding: u64,
        step: &ExecStep,
    ) -> Result<(), Error> {
        let total_rwc = u64::from(step.rwc) - 1;
        self.is_empty_rwc
            .assign(region, offset, F::from(total_rwc))?;
        let max_rws = F::from(chunk.fixed_param.max_rws as u64);
        let max_rws_assigned = self.max_rws.assign(region, offset, Value::known(max_rws))?;

        self.chunk_index.assign(
            region,
            offset,
            Value::known(F::from(chunk.chunk_context.idx as u64)),
        )?;

        self.is_first_chunk
            .assign(region, offset, F::from(chunk.chunk_context.idx as u64))?;

        self.is_end_padding_exist.assign(
            region,
            offset,
            F::ONE,
            max_rws.sub(F::from(inner_rws_before_padding)),
        )?;

        // When rw_indices is not empty, means current step is non-padding step, we're at the
        // last row (at a fixed offset), where we need to access the max_rws
        // constant.
        if step.rw_indices_len() != 0 {
            region.constrain_constant(max_rws_assigned, max_rws)?;
        }
        Ok(())
    }
}
