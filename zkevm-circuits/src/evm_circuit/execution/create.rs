use crate::evm_circuit::util::RandomLinearCombination;
use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        param::{N_BYTES_ACCOUNT_ADDRESS, N_BYTES_GAS, N_BYTES_MEMORY_WORD_SIZE},
        step::ExecutionState,
        util::{
            common_gadget::TransferGadget,
            constraint_builder::{
                ConstraintBuilder, ReversionInfo, StepStateTransition,
                Transition::{Delta, To},
            },
            from_bytes,
            math_gadget::{
                BatchedIsZeroGadget, ConstantDivisionGadget, IsEqualGadget, IsZeroGadget,
                MinMaxGadget,
            },
            memory_gadget::{MemoryAddressGadget, MemoryExpansionGadget},
            select, sum, CachedRegion, Cell, Word,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    table::{AccountFieldTag, CallContextFieldTag},
    util::Expr,
};
use bus_mapping::evm::OpcodeId;
use eth_types::{
    evm_types::{GasCost, GAS_STIPEND_CALL_WITH_VALUE},
    Field, ToAddress, ToLittleEndian, ToScalar, U256,
};
use halo2_proofs::{circuit::Value, plonk::Error};
use keccak256::EMPTY_HASH_LE;

/// Gadget for CREATE and CREATE2 opcodes
#[derive(Clone, Debug)]
pub(crate) struct CreateGadget<F> {
    opcode: Cell<F>,
    is_create2: Cell<F>,

    // initialization_code_start: Word<F>,
    // initialization_code_length: Word<F>,
    value: Word<F>,
    salt: Word<F>,
    new_address: RandomLinearCombination<F, N_BYTES_ACCOUNT_ADDRESS>,

    // tx access list for new address
    tx_id: Cell<F>,
    reversion_info: ReversionInfo<F>,
    was_warm: Cell<F>,

    caller_address: Cell<F>,
    nonce: Cell<F>,

    callee_reversion_info: ReversionInfo<F>,

    transfer: TransferGadget<F>,

    initialization_code: MemoryAddressGadget<F>,
    memory_expansion: MemoryExpansionGadget<F, 1, N_BYTES_MEMORY_WORD_SIZE>,

    gas_left: ConstantDivisionGadget<F, N_BYTES_GAS>,
    //
    // // transfer value to new address
    // transfer: TransferGadget<F>,
    // callee_reversion_info: ReversionInfo<F>,
    //
    // // memory
    // caller_memory_address: MemoryAddressGadget<F>,
    // memory_expansion: MemoryExpansionGadget<F, 1, N_BYTES_MEMORY_WORD_SIZE>,
    // // new call context
    // current_address: Cell<F>,
    // depth: Cell<F>,
    // gas: Word<F>,
    // callee_address: Word<F>,
    // value: Word<F>,
    // is_success: Cell<F>,
    // gas_is_u64: IsZeroGadget<F>,
    //
    // // gas
    // one_64th_gas: ConstantDivisionGadget<F, N_BYTES_GAS>,
    // capped_callee_gas_left: MinMaxGadget<F, N_BYTES_GAS>,

    // errors:
    // is_empty_nonce_and_balance: BatchedIsZeroGadget<F, 2>,
    // is_empty_code_hash: IsEqualGadget<F>,
}

impl<F: Field> ExecutionGadget<F> for CreateGadget<F> {
    const NAME: &'static str = "CREATE";

    const EXECUTION_STATE: ExecutionState = ExecutionState::CREATE;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        // Use rw_counter of the step which triggers next call as its call_id.
        let callee_call_id = cb.curr.state.rw_counter.clone();

        let opcode = cb.query_cell();
        cb.opcode_lookup(opcode.expr(), 1.expr());

        let is_create2 = cb.query_bool();
        cb.require_equal(
            "Opcode is CREATE or CREATE2",
            opcode.expr(),
            select::expr(
                is_create2.expr(),
                OpcodeId::CREATE2.expr(),
                OpcodeId::CREATE.expr(),
            ),
        );

        let value = cb.query_word();
        cb.stack_pop(value.expr());

        let initialization_code = MemoryAddressGadget::construct_2(cb);
        cb.stack_pop(initialization_code.offset());
        cb.stack_pop(initialization_code.length());

        let salt = cb.condition(is_create2.expr(), |cb| {
            let salt = cb.query_word();
            cb.stack_pop(salt.expr());
            salt
        });
        let new_address = cb.query_rlc();
        cb.stack_push(new_address.expr());

        let tx_id = cb.call_context(None, CallContextFieldTag::TxId);
        let mut reversion_info = cb.reversion_info_read(None);
        let was_warm = cb.query_bool();
        cb.account_access_list_write(
            tx_id.expr(),
            from_bytes::expr(&new_address.cells),
            1.expr(),
            was_warm.expr(),
            Some(&mut reversion_info),
        );

        let caller_address = cb.call_context(None, CallContextFieldTag::CalleeAddress);
        let nonce = cb.query_cell();
        cb.account_write(
            caller_address.expr(),
            AccountFieldTag::Nonce,
            nonce.expr() + 1.expr(),
            nonce.expr(),
            Some(&mut reversion_info),
            // None,
        );

        // let caller_address = cb.call_context(None,
        // CallContextFieldTag::CalleeAddress);

        let mut callee_reversion_info = cb.reversion_info_write(Some(callee_call_id.expr()));
        cb.account_write(
            new_address.expr(),
            AccountFieldTag::Nonce,
            1.expr(),
            0.expr(),
            Some(&mut callee_reversion_info),
        );

        let transfer = TransferGadget::construct(
            cb,
            caller_address.expr(),
            new_address.expr(),
            value.clone(),
            &mut callee_reversion_info,
        );

        let memory_expansion =
            MemoryExpansionGadget::construct(cb, [initialization_code.address()]);

        let stack_pointer_delta = 2.expr() + is_create2.expr();

        // EIP-150: all but one 64th of the caller's gas is sent to the callee.
        // let caller_gas_left =
        // (geth_step.gas.0 - geth_step.gas_cost.0 - memory_expansion_gas_cost) / 64;

        let gas_cost = GasCost::CREATE.expr() + memory_expansion.gas_cost();
        let gas_left = ConstantDivisionGadget::construct(cb, cb.curr.state.gas_left.expr() - gas_cost, 64);
        for (field_tag, value) in [
            (
                CallContextFieldTag::ProgramCounter,
                cb.curr.state.program_counter.expr() + 1.expr(),
            ),
            (
                CallContextFieldTag::StackPointer,
                cb.curr.state.stack_pointer.expr() + stack_pointer_delta,
            ),
            (CallContextFieldTag::GasLeft, gas_left.quotient()),
            (
                CallContextFieldTag::MemorySize,
                memory_expansion.next_memory_word_size(),
            ),
            (
                CallContextFieldTag::ReversibleWriteCounter,
                cb.curr.state.reversible_write_counter.expr() + 2.expr(),
            ),
        ] {
            cb.call_context_lookup(true.expr(), None, field_tag, value);
        }

        // let caller_address = cb.call_context(None,
        // CallContextFieldTag::CalleeAddress); let [callee_address, value,
        // callee_address] = [(); 3].map(|| cb.query_word()); let is_failure =
        // IsZeroGadget::construct(cb, callee_address);
        // let mut callee_reversion_info =
        //     ReversionInfo::from_caller(cb, &reversion_info,
        // not::expr(is_failure.expr())); let transfer =
        // TransferGadget::construct(     cb,
        //     caller_address.expr(),
        //     address.expr(),
        //     value.expr(),
        //     &mut callee_reversion_info,
        // );

        // let [offset, size] = [(); 2].map(|| cb.query_word());
        // let memory_address = MemoryAddressGadget::construct(cb, offset, size);
        // let memory_expansion = MemoryExpansionGadget::construct(
        //     cb,
        //     cb.curr.state.memory_word_size.expr(),
        //     [memory_address.address()],
        // );
        //
        // let [value, offset, size, salt, address] = [(); 5].map(cb.query_cell());
        // [value, offset, size].map(|cell| cb.stack_pop(cell.expr()));
        // cb.condition(is_create2.expr(), |cb| cb.stack_pop(salt.expr()));
        // cb.stack_push(address);
        //
        // let [current_address, is_static, depth] = [
        //     CallContextFieldTag::CalleeAddress,
        //     CallContextFieldTag::IsStatic,
        //     CallContextFieldTag::Depth,
        // ]
        // .map(|field_tag| cb.call_context(None, field_tag));
        //
        // cb.range_lookup(depth.expr(), 1024);
        //
        // // Lookup values from stack
        // cb.stack_pop(gas_word.expr());
        // cb.stack_pop(callee_address_word.expr());

        // // `CALL` opcode has an additional stack pop `value`.
        // cb.condition(IS_CREATE2.expr(), |cb| cb.stack_pop(value.expr()));
        //
        // [
        //     cd_offset.expr(),
        //     cd_length.expr(),
        //     rd_offset.expr(),
        //     rd_length.expr(),
        // ]
        // .map(|expression| cb.stack_pop(expression));
        // cb.stack_push(is_success.expr());

        // let gas = Eip150Gadget::construct(cb, cb.curr.state.gas_left.expr() -
        // GasCost::CREATE);
        //
        // cb.require_step_state_transition(StepStateTransition {
        //     rw_counter: Delta(cb.rw_counter_offset.clone()),
        //     call_id: To(callee_call_id.expr()),
        //     is_root: To(false.expr()),
        //     is_create: To(true.expr()),
        //     code_hash: To(initialization_code_hash.expr()),
        //     gas_left: To(gas.callee_gas_left()),
        //     reversible_write_counter: To(2.expr()),
        //     ..StepStateTransition::new_context()
        // });

        Self {
            opcode,
            is_create2,
            reversion_info,
            tx_id,
            was_warm,
            value,
            salt,
            new_address,
            caller_address,
            nonce,
            callee_reversion_info,
            transfer,
            initialization_code,
            memory_expansion,
            gas_left,
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
        let opcode = step.opcode.unwrap();
        let is_create2 = opcode == OpcodeId::CREATE2;
        self.opcode
            .assign(region, offset, Value::known(F::from(opcode.as_u64())))?;
        self.is_create2.assign(
            region,
            offset,
            Value::known(is_create2.to_scalar().unwrap()),
        )?;

        let [value, initialization_code_start, initialization_code_length, new_address] =
            [0, 1, 2, 3 + usize::from(is_create2)]
                .map(|i| step.rw_indices[i])
                .map(|idx| block.rws[idx].stack_value());
        let salt = if is_create2 {
            block.rws[step.rw_indices[3]].stack_value()
        } else {
            U256::zero()
        };

        for (word, assignment) in [
            // (&self.initialization_code_start, initialization_code_start),
            // (&self.initialization_code_length, initialization_code_length),
            (&self.value, value),
            (&self.salt, salt),
        ] {
            word.assign(region, offset, Some(assignment.to_le_bytes()))?;
        }
        let initialization_code_address = self.initialization_code.assign(
            region,
            offset,
            initialization_code_start,
            initialization_code_length,
            block.randomness,
        )?;

        self.new_address.assign(
            region,
            offset,
            Some(new_address.to_le_bytes()[0..20].try_into().unwrap()),
        )?;

        self.tx_id
            .assign(region, offset, Value::known(tx.id.to_scalar().unwrap()))?;

        self.reversion_info.assign(
            region,
            offset,
            call.rw_counter_end_of_reversion,
            call.is_persistent,
        )?;

        self.was_warm.assign(
            region,
            offset,
            Value::known(
                block.rws[step.rw_indices[7 + usize::from(is_create2)]]
                    .tx_access_list_value_pair()
                    .1
                    .to_scalar()
                    .unwrap(),
            ),
        )?;

        dbg!(call.callee_address);
        self.caller_address.assign(
            region,
            offset,
            Value::known(call.callee_address.to_scalar().unwrap()),
        )?;

        self.nonce.assign(
            region,
            offset,
            Value::known(
                block.rws[step.rw_indices[9 + usize::from(is_create2)]]
                    .account_value_pair()
                    .1
                    .to_scalar()
                    .unwrap(),
            ),
        )?;

        //
        // let address_bytes =
        // block.rws[step.rw_indices[2]].stack_value().to_le_bytes()[0..20].try_into().
        // unwrap(); self.new_address.assign(
        //     region, offset,
        //     Some(address_bytes)
        // )?;

        let [callee_rw_counter_end_of_reversion, callee_is_persistent] = [10, 11]
            .map(|i| block.rws[step.rw_indices[i + usize::from(is_create2)]].call_context_value());

        dbg!(callee_rw_counter_end_of_reversion, callee_is_persistent);

        self.callee_reversion_info.assign(
            region,
            offset,
            callee_rw_counter_end_of_reversion
                .low_u64()
                .try_into()
                .unwrap(),
            callee_is_persistent.low_u64() != 0,
        )?;

        let [caller_balance_pair, callee_balance_pair] = [13, 14]
            .map(|i| block.rws[step.rw_indices[i + usize::from(is_create2)]].account_value_pair());
        dbg!(caller_balance_pair, callee_balance_pair, value);
        self.transfer.assign(
            region,
            offset,
            caller_balance_pair,
            callee_balance_pair,
            value,
        )?;

        self.memory_expansion.assign(
            region,
            offset,
            step.memory_word_size(),
            [initialization_code_address],
        )?;

        self.gas_left.assign(region, offset, (step.gas_left - GasCost::CREATE.as_u64()).into())?;

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::test_util::run_test_circuits;
    use eth_types::{
        address, bytecode, evm_types::OpcodeId, geth_types::Account, Address, Bytecode, ToWord,
        Word,
    };
    use itertools::Itertools;
    use mock::{eth, TestContext, MOCK_ACCOUNTS};

    const CALLEE_ADDRESS: Address = Address::repeat_byte(0xff);
    const CALLER_ADDRESS: Address = Address::repeat_byte(0x34);

    fn callee_bytecode(is_return: bool, offset: u64, length: u64) -> Bytecode {
        let memory_bytes = [0x60; 10];
        let memory_address = 0;
        let memory_value = Word::from_big_endian(&memory_bytes);
        let mut code = bytecode! {
            PUSH10(memory_value)
            PUSH1(memory_address)
            MSTORE
            PUSH2(length)
            PUSH2(32u64 - u64::try_from(memory_bytes.len()).unwrap() + offset)
        };
        code.write_op(if is_return {
            OpcodeId::RETURN
        } else {
            OpcodeId::REVERT
        });
        code
    }

    fn caller_bytecode(return_data_offset: u64, return_data_length: u64) -> Bytecode {
        bytecode! {
            PUSH32(return_data_length)
            PUSH32(return_data_offset)
            PUSH32(0) // call data length
            PUSH32(0) // call data offset
            PUSH32(0) // value
            PUSH32(CALLEE_ADDRESS.to_word())
            PUSH32(4000) // gas
            CALL
            STOP
        }
    }

    #[test]
    fn mason2() {
        let test_parameters = [(0, 0), (0, 10), (300, 20), (1000, 0)];
        for ((offset, length), is_return) in test_parameters.iter().cartesian_product(&[true])
        // FIX MEEEEEE there's an issue when the init call reverts.
        {
            let initializer = callee_bytecode(*is_return, *offset, *length).code();

            let root_code = bytecode! {
                PUSH32(Word::from_big_endian(&initializer))
                PUSH1(0)
                MSTORE

                PUSH1(initializer.len())        // size
                PUSH1(32 - initializer.len())   // offset
                PUSH1(0)                        // value

                CREATE
            };

            let caller = Account {
                address: CALLER_ADDRESS,
                code: root_code.into(),
                nonce: Word::one(),
                balance: eth(10),
                ..Default::default()
            };

            let test_context = TestContext::<2, 1>::new(
                None,
                |accs| {
                    accs[0]
                        .address(address!("0x000000000000000000000000000000000000cafe"))
                        .balance(eth(10));
                    accs[1].account(&caller);
                },
                |mut txs, accs| {
                    txs[0]
                        .from(accs[0].address)
                        .to(accs[1].address)
                        .gas(100000u64.into());
                },
                |block, _| block,
            )
            .unwrap();

            assert_eq!(
                run_test_circuits(test_context, None),
                Ok(()),
                "(offset, length, is_return) = {:?}",
                (*offset, *length, *is_return),
            );
        }
    }

    #[test]
    fn mason() {
        // Test the case where the initialization call is successful, but the CREATE
        // call is reverted.
        let initializer = callee_bytecode(true, 0, 10).code();

        let root_code = bytecode! {
            PUSH32(Word::from_big_endian(&initializer))
            PUSH1(0)
            MSTORE

            PUSH1(initializer.len())        // size
            PUSH1(32 - initializer.len())   // offset
            PUSH1(0)                        // value

            CREATE
            PUSH1(0)
            PUSH1(0)
            REVERT
        };

        let caller = Account {
            address: CALLER_ADDRESS,
            code: root_code.into(),
            nonce: Word::one(),
            balance: eth(10),
            ..Default::default()
        };

        let test_context = TestContext::<2, 1>::new(
            None,
            |accs| {
                accs[0]
                    .address(address!("0x000000000000000000000000000000000000cafe"))
                    .balance(eth(10));
                accs[1].account(&caller);
            },
            |mut txs, accs| {
                txs[0]
                    .from(accs[0].address)
                    .to(accs[1].address)
                    .gas(100000u64.into());
            },
            |block, _| block,
        )
        .unwrap();

        assert_eq!(run_test_circuits(test_context, None), Ok(()),);
    }
}
