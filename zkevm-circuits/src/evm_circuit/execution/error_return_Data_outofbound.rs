use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        param::N_BYTES_PROGRAM_COUNTER,
        step::ExecutionState,
        util::{
            common_gadget::RestoreContextGadget,
            constraint_builder::{
                ConstraintBuilder, StepStateTransition,
                Transition::{Delta, Same},
            },
            from_bytes,
            math_gadget::{IsEqualGadget, IsZeroGadget, LtGadget},
            CachedRegion, Cell, RandomLinearCombination, Word as RLCWord,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    table::CallContextFieldTag,
    util::Expr,
};
use eth_types::{evm_types::OpcodeId, Field, ToLittleEndian, Word};

use halo2_proofs::{circuit::Value, plonk::Error};

#[derive(Clone, Debug)]
pub(crate) struct ErrorReturnDataOutOfBoundGadget<F> {
    opcode: Cell<F>,
    /// Holds the length of the return data.
    return_data_length: Cell<F>,
    /// Holds the memory address for the offset in return data from where we
    /// read.
    data_offset:  Cell<F>,
    memory_offset: Cell<F>,
    end : Cell<F>,
    is_dataset_overflow: IsZeroGadget<F>,
    is_end_overflow: IsZeroGadget<F>,
    is_end_exceed_length: IsZeroGadget<F>,
    restore_context: RestoreContextGadget<F>,
}

impl<F: Field> ExecutionGadget<F> for ErrorReturnDataOutOfBoundGadget<F> {
    const NAME: &'static str = "ErrorReturnDataOutOfBoundGadget";

    const EXECUTION_STATE: ExecutionState = ExecutionState::ErrorReturnDataOutOfBound;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        let destination = cb.query_rlc();
        let opcode = cb.query_cell();
        let value = cb.query_cell();
        let is_code = cb.query_cell();
        let condition = cb.query_cell();

        cb.require_equal("opcode is RETURNDATACOPY", opcode.expr(), OpcodeId::RETURNDATACOPY.expr());
        // do stack oeprations

        // read last callee return data length

        // check overflows


        // initialize is_jump_dest
        let is_jump_dest = IsEqualGadget::construct(cb, value.expr(), OpcodeId::JUMPDEST.expr());

        // first default this condition, if use will re-construct with real condition
        // value
        let is_condition_zero = IsZeroGadget::construct(cb, condition.expr());

        // Pop the value from the stack
        cb.stack_pop(destination.expr());
        // look up bytecode length

        let within_range = LtGadget::construct(cb, dest_value.expr(), code_length.expr());
        //if not out of range, check `dest` is invalid
        cb.condition(within_range.expr(), |cb| {
            // if not out of range, Lookup real value
            cb.bytecode_lookup(
                cb.curr.state.code_hash.expr(),
                dest_value.clone(),
                is_code.expr(),
                value.expr(),
            );
            cb.require_zero(
                "is_code is false or not JUMPDEST",
                is_code.expr() * is_jump_dest.expr(),
            );
        });

        cb.call_context_lookup(false.expr(), None, CallContextFieldTag::IsSuccess, 0.expr());

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
                    2.expr() + is_jumpi.expr() + cb.curr.state.reversible_write_counter.expr(),
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
                0.expr(),
                0.expr(),
                0.expr(),
                0.expr(),
            )
        });

        Self {
            opcode,
            destination,
            code_length,
            value,
            is_code,
            within_range,
            is_jump_dest,
            is_jumpi,
            condition,
            is_condition_zero,
            restore_context,
        }
    }

    fn assign_exec_step(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        block: &Block<F>,
        _: &Transaction,
        call: &Call,
        step: &ExecStep,
    ) -> Result<(), Error> {
        let opcode = step.opcode.unwrap();
        let is_jumpi = opcode == OpcodeId::JUMPI;

        self.opcode
            .assign(region, offset, Value::known(F::from(opcode.as_u64())))?;
       
        let condition_rlc =
            RLCWord::random_linear_combine(condition.to_le_bytes(), block.randomness);

        self.within_range.assign(
            region,
            offset,
            F::from(destination.as_u64()),
            F::from(code_length),
        )?;

        self.is_jumpi.assign(
            region,
            offset,
            F::from(opcode.as_u64()),
            F::from(OpcodeId::JUMPI.as_u64()),
        )?;

        self.restore_context
            .assign(region, offset, block, call, step, 2 + is_jumpi as usize)?;
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::evm_circuit::test::run_test_circuit;
    use crate::evm_circuit::witness::block_convert;
    use crate::test_util::run_test_circuits;
    use eth_types::bytecode::Bytecode;
    use eth_types::evm_types::OpcodeId;
    use eth_types::geth_types::Account;
    use eth_types::{address, bytecode, Address, ToWord, Word};
    use mock::TestContext;

    fn test_return_data_out_of_bound(destination: usize, out_of_range: bool) {
        let mut bytecode = bytecode! {
            PUSH32(if out_of_range { destination + 10} else { destination })
            JUMP
        };

        // incorrect assigning for invalid jump
        for _ in 0..(destination - 33) {
            bytecode.write(0, false);
        }
        bytecode.append(&bytecode! {
            JUMPDEST
            STOP
        });

        assert_eq!(
            run_test_circuits(
                TestContext::<2, 1>::simple_ctx_with_bytecode(bytecode).unwrap(),
                None
            ),
            Ok(())
        );
    }

    #[test]
    fn invalid_jump_err() {
        test_invalid_jump(34, false);
    }


    #[test]
    fn invalid_jump_internal() {
        // test jump error in internal call
        test_internal_jump_error(false);
        // test jumpi error in internal call
        test_internal_jump_error(true);
    }

    // internal call test
    struct Stack {
        gas: u64,
        value: Word,
        cd_offset: u64,
        cd_length: u64,
        rd_offset: u64,
        rd_length: u64,
    }

    fn callee(code: Bytecode) -> Account {
        let code = code.to_vec();
        let is_empty = code.is_empty();
        Account {
            address: Address::repeat_byte(0xff),
            code: code.into(),
            nonce: if is_empty { 0 } else { 1 }.into(),
            balance: if is_empty { 0 } else { 0xdeadbeefu64 }.into(),
            ..Default::default()
        }
    }

    fn caller(opcode: OpcodeId, stack: Stack, caller_is_success: bool) -> Account {
        let is_call = opcode == OpcodeId::CALL;
        let terminator = if caller_is_success {
            OpcodeId::RETURN
        } else {
            OpcodeId::REVERT
        };

        // Call twice for testing both cold and warm access
        let mut bytecode = bytecode! {
            PUSH32(Word::from(stack.rd_length))
            PUSH32(Word::from(stack.rd_offset))
            PUSH32(Word::from(stack.cd_length))
            PUSH32(Word::from(stack.cd_offset))
        };
        if is_call {
            bytecode.push(32, stack.value);
        }
        bytecode.append(&bytecode! {
            PUSH32(Address::repeat_byte(0xff).to_word())
            PUSH32(Word::from(stack.gas))
            .write_op(opcode)
            PUSH32(Word::from(stack.rd_length))
            PUSH32(Word::from(stack.rd_offset))
            PUSH32(Word::from(stack.cd_length))
            PUSH32(Word::from(stack.cd_offset))
        });
        if is_call {
            bytecode.push(32, stack.value);
        }
        bytecode.append(&bytecode! {
            PUSH32(Address::repeat_byte(0xff).to_word())
            PUSH32(Word::from(stack.gas))
            .write_op(opcode)
            PUSH1(0)
            PUSH1(0)
            .write_op(terminator)
        });

        Account {
            address: Address::repeat_byte(0xfe),
            balance: Word::from(10).pow(20.into()),
            code: bytecode.to_vec().into(),
            ..Default::default()
        }
    }

    // jump or jumpi error happen in internal call
    fn test_internal_jump_error(is_jumpi: bool) {
        let mut caller_bytecode = bytecode! {
            PUSH1(0)
            PUSH1(0)
            PUSH1(0)
            PUSH1(0)
            PUSH1(0)
        };

        caller_bytecode.append(&bytecode! {
            PUSH32(Address::repeat_byte(0xff).to_word())
            PUSH2(10000)
            CALL
            STOP
        });

        let opcode = if is_jumpi {
            OpcodeId::JUMPI
        } else {
            OpcodeId::JUMP
        };

        let mut callee_bytecode = bytecode! {
            PUSH1(1) //  work as condition if is_jumpi
            PUSH1(42) // jump dest 45
            .write_op(opcode)

            PUSH1(0)
            PUSH1(0)
            PUSH1(0)
            PUSH1(0)
            PUSH1(0)
        };

        callee_bytecode.append(&bytecode! {
            PUSH20(Address::repeat_byte(0xff).to_word())
            PUSH1(132) // gas

            JUMPDEST
            GAS
            PUSH1(1)
            AND
            PUSH1(56)
            JUMPI

            PUSH1(0)
            PUSH1(0)
            REVERT

            JUMPDEST
            STOP
        });
        test_ok(
            Account {
                address: Address::repeat_byte(0xfe),
                balance: Word::from(10).pow(20.into()),
                code: caller_bytecode.into(),
                ..Default::default()
            },
            callee(callee_bytecode),
        );
    }

    fn test_ok(caller: Account, callee: Account) {
        let block = TestContext::<3, 1>::new(
            None,
            |accs| {
                accs[0]
                    .address(address!("0x000000000000000000000000000000000000cafe"))
                    .balance(Word::from(10u64.pow(19)));
                accs[1]
                    .address(caller.address)
                    .code(caller.code)
                    .nonce(caller.nonce)
                    .balance(caller.balance);
                accs[2]
                    .address(callee.address)
                    .code(callee.code)
                    .nonce(callee.nonce)
                    .balance(callee.balance);
            },
            |mut txs, accs| {
                txs[0]
                    .from(accs[0].address)
                    .to(accs[1].address)
                    .gas(100000.into());
            },
            |block, _tx| block.number(0xcafeu64),
        )
        .unwrap()
        .into();
        let block_data = bus_mapping::mock::BlockData::new_from_geth_data(block);
        let mut builder = block_data.new_circuit_input_builder();
        builder
            .handle_block(&block_data.eth_block, &block_data.geth_traces)
            .unwrap();
        let block = block_convert(&builder.block, &builder.code_db).unwrap();
        assert_eq!(run_test_circuit(block), Ok(()));
    }

    fn test_invalid_jumpi(destination: usize) {
        let mut bytecode = bytecode! {
            PUSH32(destination)
            PUSH32(100) // condition
            JUMPI
        };

        // incorrect assigning for invalid jump
        for _ in 0..(destination - 33) {
            bytecode.write(0, false);
        }
        bytecode.append(&bytecode! {
            JUMPDEST
            STOP
        });

        assert_eq!(
            run_test_circuits(
                TestContext::<2, 1>::simple_ctx_with_bytecode(bytecode).unwrap(),
                None
            ),
            Ok(())
        );
    }
}
