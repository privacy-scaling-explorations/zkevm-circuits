use super::{
    from_bytes,
    math_gadget::IsZeroGadget,
    memory_gadget::{MemoryAddressGadget, MemoryExpansionGadget},
    CachedRegion,
};
use crate::{
    evm_circuit::{
        param::{N_BYTES_ACCOUNT_ADDRESS, N_BYTES_GAS, N_BYTES_MEMORY_WORD_SIZE},
        table::{FixedTableTag, Lookup},
        util::{
            constraint_builder::{
                ConstraintBuilder, ReversionInfo, StepStateTransition,
                Transition::{Delta, Same, To},
            },
            math_gadget::{AddWordsGadget, RangeCheckGadget},
            not, Cell, Word,
        },
    },
    table::{AccountFieldTag, CallContextFieldTag},
    util::Expr,
    witness::{Block, Call, ExecStep},
};
use eth_types::{evm_types::GasCost, Field, ToLittleEndian, ToScalar, U256};
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
        cb: &mut ConstraintBuilder<F>,
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
        let opcode = step.opcode.unwrap();
        self.opcode
            .assign(region, offset, Value::known(F::from(opcode.as_u64())))?;

        self.sufficient_gas_left.assign(
            region,
            offset,
            F::from((step.gas_left - step.gas_cost) as u64),
        )?;

        Ok(())
    }
}

/// Construction of step state transition that restores caller's state.
#[derive(Clone, Debug)]
pub(crate) struct RestoreContextGadget<F> {
    caller_id: Cell<F>,
    caller_is_root: Cell<F>,
    caller_is_create: Cell<F>,
    caller_code_hash: Cell<F>,
    caller_program_counter: Cell<F>,
    caller_stack_pointer: Cell<F>,
    caller_gas_left: Cell<F>,
    caller_memory_word_size: Cell<F>,
    caller_reversible_write_counter: Cell<F>,
}

impl<F: Field> RestoreContextGadget<F> {
    pub(crate) fn construct(
        cb: &mut ConstraintBuilder<F>,
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
        let [caller_is_root, caller_is_create, caller_code_hash, caller_program_counter, caller_stack_pointer, caller_gas_left, caller_memory_word_size, caller_reversible_write_counter] =
            [
                CallContextFieldTag::IsRoot,
                CallContextFieldTag::IsCreate,
                CallContextFieldTag::CodeHash,
                CallContextFieldTag::ProgramCounter,
                CallContextFieldTag::StackPointer,
                CallContextFieldTag::GasLeft,
                CallContextFieldTag::MemorySize,
                CallContextFieldTag::ReversibleWriteCounter,
            ]
            .map(|field_tag| cb.call_context(Some(caller_id.expr()), field_tag));

        // Update caller's last callee information
        for (field_tag, value) in [
            (
                CallContextFieldTag::LastCalleeId,
                cb.curr.state.call_id.expr(),
            ),
            (
                CallContextFieldTag::LastCalleeReturnDataOffset,
                return_data_offset,
            ),
            (
                CallContextFieldTag::LastCalleeReturnDataLength,
                return_data_length.clone(),
            ),
        ] {
            cb.call_context_lookup(true.expr(), Some(caller_id.expr()), field_tag, value);
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
            code_hash: To(caller_code_hash.expr()),
            program_counter: To(caller_program_counter.expr()),
            stack_pointer: To(caller_stack_pointer.expr()),
            gas_left: To(gas_left),
            memory_word_size: To(caller_memory_word_size.expr()),
            reversible_write_counter: To(reversible_write_counter),
            log_id: Same,
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
                    .map(|i| step.rw_indices[i + rw_offset])
                    .map(|idx| block.rws[idx].call_context_value())
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

        self.caller_code_hash.assign(
            region,
            offset,
            Value::known(Word::random_linear_combine(
                caller_code_hash.to_le_bytes(),
                block.randomness,
            )),
        )?;

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
        cb: &mut ConstraintBuilder<F>,
        address: Expression<F>,
        updates: Vec<Word<F>>,
        reversion_info: Option<&mut ReversionInfo<F>>,
    ) -> Self {
        debug_assert!(updates.len() == N_ADDENDS - 1);

        let balance_addend = cb.query_word();
        let balance_sum = cb.query_word();

        let [value, value_prev] = if INCREASE {
            [balance_sum.expr(), balance_addend.expr()]
        } else {
            [balance_addend.expr(), balance_sum.expr()]
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
            value,
            value_prev,
            reversion_info,
        );

        Self { add_words }
    }

    pub(crate) fn balance(&self) -> &Word<F> {
        if INCREASE {
            self.add_words.sum()
        } else {
            &self.add_words.addends()[0]
        }
    }

    pub(crate) fn balance_prev(&self) -> &Word<F> {
        if INCREASE {
            &self.add_words.addends()[0]
        } else {
            self.add_words.sum()
        }
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
pub(crate) struct TransferWithGasFeeGadget<F> {
    sender: UpdateBalanceGadget<F, 3, false>,
    receiver: UpdateBalanceGadget<F, 2, true>,
}

impl<F: Field> TransferWithGasFeeGadget<F> {
    pub(crate) fn construct(
        cb: &mut ConstraintBuilder<F>,
        sender_address: Expression<F>,
        receiver_address: Expression<F>,
        value: Word<F>,
        gas_fee: Word<F>,
        reversion_info: &mut ReversionInfo<F>,
    ) -> Self {
        let sender = UpdateBalanceGadget::construct(
            cb,
            sender_address,
            vec![value.clone(), gas_fee],
            Some(reversion_info),
        );
        let receiver =
            UpdateBalanceGadget::construct(cb, receiver_address, vec![value], Some(reversion_info));

        Self { sender, receiver }
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        (sender_balance, sender_balance_prev): (U256, U256),
        (receiver_balance, receiver_balance_prev): (U256, U256),
        value: U256,
        gas_fee: U256,
    ) -> Result<(), Error> {
        self.sender.assign(
            region,
            offset,
            sender_balance_prev,
            vec![value, gas_fee],
            sender_balance,
        )?;
        self.receiver.assign(
            region,
            offset,
            receiver_balance_prev,
            vec![value],
            receiver_balance,
        )?;
        Ok(())
    }
}

#[derive(Clone, Debug)]
pub(crate) struct TransferGadget<F> {
    sender: UpdateBalanceGadget<F, 2, false>,
    receiver: UpdateBalanceGadget<F, 2, true>,
}

impl<F: Field> TransferGadget<F> {
    pub(crate) fn construct(
        cb: &mut ConstraintBuilder<F>,
        sender_address: Expression<F>,
        receiver_address: Expression<F>,
        value: Word<F>,
        reversion_info: &mut ReversionInfo<F>,
    ) -> Self {
        let sender = UpdateBalanceGadget::construct(
            cb,
            sender_address,
            vec![value.clone()],
            Some(reversion_info),
        );
        let receiver =
            UpdateBalanceGadget::construct(cb, receiver_address, vec![value], Some(reversion_info));

        Self { sender, receiver }
    }

    pub(crate) fn sender(&self) -> &UpdateBalanceGadget<F, 2, false> {
        &self.sender
    }

    pub(crate) fn receiver(&self) -> &UpdateBalanceGadget<F, 2, true> {
        &self.receiver
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
            receiver_balance_prev,
            vec![value],
            receiver_balance,
        )?;
        Ok(())
    }
}

#[derive(Clone, Debug)]
pub(crate) struct CallGadget<F, const NORMAL: bool> {
    is_success: Cell<F>,

    gas: Word<F>,
    gas_is_u64: IsZeroGadget<F>,
    code_address: Word<F>,
    value: Word<F>,
    cd_address: MemoryAddressGadget<F>,
    rd_address: MemoryAddressGadget<F>,
    memory_expansion: MemoryExpansionGadget<F, 2, N_BYTES_MEMORY_WORD_SIZE>,
}

impl<F: Field, const NORMAL: bool> CallGadget<F, NORMAL> {
    pub(crate) fn construct(
        cb: &mut ConstraintBuilder<F>,
        is_call_or_is_call_code: Expression<F>,
    ) -> Self {
        let gas_word = cb.query_word();
        let code_address_word = cb.query_word();
        let value = cb.query_word();
        let cd_offset = cb.query_cell();
        let cd_length = cb.query_rlc();
        let rd_offset = cb.query_cell();
        let rd_length = cb.query_rlc();
        let is_success = cb.query_bool();

        // Lookup values from stack
        cb.stack_pop(gas_word.expr());
        cb.stack_pop(code_address_word.expr());

        // `CALL` opcode has an additional stack pop `value`.
        cb.condition(is_call_or_is_call_code, |cb| cb.stack_pop(value.expr()));

        [
            cd_offset.expr(),
            cd_length.expr(),
            rd_offset.expr(),
            rd_length.expr(),
        ]
        .map(|expression| cb.stack_pop(expression));
        cb.stack_push(is_success.expr());

        // Recomposition of random linear combination to integer
        // let gas = from_bytes::expr(&gas_word.cells[..N_BYTES_GAS]);
        let gas_is_u64 = IsZeroGadget::construct(cb, sum::expr(&gas_word.cells[N_BYTES_GAS..]));
        let cd_address = MemoryAddressGadget::construct(cb, cd_offset, cd_length);
        let rd_address = MemoryAddressGadget::construct(cb, rd_offset, rd_length);
        let memory_expansion =
            MemoryExpansionGadget::construct(cb, [cd_address.address(), rd_address.address()]);
        // `code_address` is poped from stack and used to check if it exists in
        // access list and get code hash.
        // For CALLCODE, both caller and callee addresses are `current_callee_address`.
        // For DELEGATECALL, caller address is `current_caller_address` and
        // callee address is `current_callee_address`.
        // For both CALL and STATICCALL, caller address is
        // `current_callee_address` and callee address is `code_address`.
        // let code_address =
        // from_bytes::expr(&code_address_word.cells[..N_BYTES_ACCOUNT_ADDRESS]);

        Self {
            is_success,
            code_address: code_address_word,
            gas: gas_word,
            gas_is_u64,
            value,
            cd_address,
            rd_address,
            memory_expansion,
        }
    }

    pub fn code_address(&self) -> Word<F> {
        self.code_address.clone()
    }

    pub fn code_address_expr(&self) -> Expression<F> {
        from_bytes::expr(&self.code_address.cells[..N_BYTES_GAS])
    }

    pub fn cd_address(&self) -> MemoryAddressGadget<F> {
        self.cd_address.clone()
    }

    pub fn rd_address(&self) -> MemoryAddressGadget<F> {
        self.rd_address.clone()
    }

    // TODO: try to return by ref
    pub fn value(&self) -> Word<F> {
        self.value.clone()
    }

    pub fn gas(&self) -> Word<F> {
        self.gas.clone()
    }

    pub fn gas_expr(&self) -> Expression<F> {
        from_bytes::expr(&self.gas.cells[..N_BYTES_GAS])
    }

    pub fn is_success(&self) -> Cell<F> {
        self.is_success.clone()
    }

    pub fn gas_is_u64(&self) -> IsZeroGadget<F> {
        self.gas_is_u64.clone()
    }

    pub fn memory_expansion(&self) -> MemoryExpansionGadget<F, 2, N_BYTES_MEMORY_WORD_SIZE> {
        self.memory_expansion.clone()
    }

    // pub fn value_is_zero(&self, cb: &mut ConstraintBuilder<F>) -> IsZeroGadget<F>
    // {     IsZeroGadget::construct(cb, sum::expr(&self.value.cells))
    // }

    // pub fn has_value(
    //     &self,
    //     cb: &mut ConstraintBuilder<F>,
    //     is_delegatecall: Expression<F>,
    // ) -> Expression<F> {
    //     let value_is_zero = IsZeroGadget::construct(cb,
    // sum::expr(&self.value.cells));     select::expr(is_delegatecall,
    // 0.expr(), 1.expr() - value_is_zero.expr()) }

    pub fn gas_cost(
        &self,
        cb: &mut ConstraintBuilder<F>,
        is_warm_prev: Expression<F>,
        has_value: Expression<F>,
        is_call: Expression<F>,
        is_empty: Expression<F>,
    ) -> Expression<F> {
        select::expr(
            is_warm_prev,
            GasCost::WARM_ACCESS.expr(),
            GasCost::COLD_ACCOUNT_ACCESS.expr(),
        ) + has_value.clone()
            * (GasCost::CALL_WITH_VALUE.expr()
                // Only CALL opcode could invoke transfer to make empty account into non-empty.
                + is_call * is_empty * GasCost::NEW_ACCOUNT.expr())
            + self.memory_expansion.gas_cost()
    }

    // pub fn callee_gas_left(
    //     &self,
    //     cb: &mut ConstraintBuilder<F>,
    //     gas_cost: Expression<F>,
    // ) -> (Expression<F>, MinMaxGadget<F, N_BYTES_GAS>) {
    //     // Apply EIP 150
    //     let gas_available = cb.curr.state.gas_left.expr() - gas_cost.clone();
    //     let one_64th_gas = ConstantDivisionGadget::construct(cb,
    // gas_available.clone(), 64);     let all_but_one_64th_gas = gas_available
    // - one_64th_gas.quotient();     let capped_callee_gas_left =
    //   MinMaxGadget::construct(cb, self.gas, all_but_one_64th_gas.clone()); (
    //   select::expr( self.gas_is_u64.expr(), capped_callee_gas_left.min(),
    //   all_but_one_64th_gas, ), capped_callee_gas_left, )
    // }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        gas: U256,
        code_address: U256,
        value: U256,
        is_success: U256,
        cd_offset: U256,
        cd_length: U256,
        rd_offset: U256,
        rd_length: U256,
        memory_word_size: u64,
        randomness: F,
    ) -> Result<(u64), Error> {
        self.gas.assign(region, offset, Some(gas.to_le_bytes()))?;
        self.code_address
            .assign(region, offset, Some(code_address.to_le_bytes()))?;
        self.value
            .assign(region, offset, Some(value.to_le_bytes()))?;
        self.is_success
            .assign(region, offset, Value::known(F::from(is_success.low_u64())))?;
        self.gas_is_u64.assign(
            region,
            offset,
            sum::value(&gas.to_le_bytes()[N_BYTES_GAS..]),
        )?;
        let cd_address = self
            .cd_address
            .assign(region, offset, cd_offset, cd_length, randomness)?;
        let rd_address = self
            .rd_address
            .assign(region, offset, rd_offset, rd_length, randomness)?;
        let (_, memory_expansion_gas_cost) = self.memory_expansion.assign(
            region,
            offset,
            memory_word_size,
            [cd_address, rd_address],
        )?;

        Ok((memory_expansion_gas_cost))
    }

    pub(crate) fn gen_gas_available(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        memory_expansion_gas_cost: u64,
        gas_left: u64,
        is_warm_prev: bool,
        is_call: bool,
        has_value: bool,
        callee_exists: bool,
    ) -> Result<(u64), Error> {
        let gas_cost = if is_warm_prev {
            GasCost::WARM_ACCESS.as_u64()
        } else {
            GasCost::COLD_ACCOUNT_ACCESS.as_u64()
        } + if has_value {
            GasCost::CALL_WITH_VALUE.as_u64()
                // Only CALL opcode could invoke transfer to make empty account into non-empty.
                + if is_call && !callee_exists {
                    GasCost::NEW_ACCOUNT.as_u64()
                } else {
                    0
                }
        } else {
            0
        } + memory_expansion_gas_cost;
        let gas_available = gas_left - gas_cost;
        Ok((gas_available))
        // self.one_64th_gas
        //     .assign(region, offset, gas_available as u128)?;
        // self.capped_callee_gas_left.assign(
        //     region,
        //     offset,
        //     F::from(gas.low_u64()),
        //     F::from(gas_available - gas_available / 64),
        // )?;
    }
}
