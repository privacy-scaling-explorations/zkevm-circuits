use crate::evm_circuit::util::memory_gadget::MemoryAddressGadget;
use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        step::ExecutionState,
        util::{
            common_gadget::RestoreContextGadget, constraint_builder::ConstraintBuilder, not,
            CachedRegion, Cell,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    table::CallContextFieldTag,
    util::Expr,
};
use bus_mapping::circuit_input_builder::CopyDataType;
use bus_mapping::evm::OpcodeId;
use eth_types::Field;
use halo2_proofs::plonk::Error;

use std::cmp::min;

#[derive(Clone, Debug)]
pub(crate) struct ReturnGadget<F> {
    opcode: Cell<F>,

    range: MemoryAddressGadget<F>,

    is_root: Cell<F>,
    is_create: Cell<F>,
    is_success: Cell<F>,
    restore_context: RestoreContextGadget<F>,

    copy_length: Cell<F>, // TODO: this needs more constraints.

    caller_id: Cell<F>, // can you get this out of restore_context?
    return_data_offset: Cell<F>,
    return_data_length: Cell<F>,
}

// This will handle reverts too?
impl<F: Field> ExecutionGadget<F> for ReturnGadget<F> {
    const NAME: &'static str = "RETURN";

    const EXECUTION_STATE: ExecutionState = ExecutionState::RETURN;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        let opcode = cb.query_cell();
        cb.opcode_lookup(opcode.expr(), 1.expr());

        let offset = cb.query_cell();
        let length = cb.query_rlc();
        cb.stack_pop(offset.expr()); // +1
        cb.stack_pop(length.expr()); // +2
        let range = MemoryAddressGadget::construct(cb, offset, length);

        let [is_root, is_create, is_success, caller_id, return_data_offset, return_data_length] = [
            CallContextFieldTag::IsRoot,
            CallContextFieldTag::IsCreate,
            CallContextFieldTag::IsSuccess,
            CallContextFieldTag::CallerId,
            CallContextFieldTag::ReturnDataOffset,
            CallContextFieldTag::ReturnDataLength,
        ]
        .map(|field_tag| cb.call_context(None, field_tag));

        cb.condition(is_success.expr(), |cb| {
            cb.require_equal(
                "Opcode should be RETURN",
                opcode.expr(),
                OpcodeId::RETURN.expr(),
            )
        });
        cb.condition(not::expr(is_success.expr()), |cb| {
            cb.require_equal(
                "Opcode should be REVERT",
                opcode.expr(),
                OpcodeId::REVERT.expr(),
            )
        });

        cb.condition(is_root.expr(), |cb| {
            cb.require_next_state(ExecutionState::EndTx);
            cb.call_context_lookup(
                0.expr(),
                None,
                CallContextFieldTag::IsSuccess,
                is_success.expr(),
            );
        });

        let copy_length = cb.query_cell();

        let restore_context = cb.condition(not::expr(is_root.expr()), |cb| {
            cb.require_next_state_not(ExecutionState::EndTx);
            RestoreContextGadget::construct(
                cb,
                is_success.expr(),
                copy_length.expr() + copy_length.expr(),
                range.offset(),
                range.length(),
            )
        });

        cb.condition(
            not::expr(is_create.expr()) * not::expr(is_root.expr()) * range.has_length(),
            |cb| {
                cb.copy_table_lookup(
                    cb.curr.state.call_id.expr(),        // source id
                    CopyDataType::Memory.expr(),         // source tag
                    caller_id.expr(),                    // destination id
                    CopyDataType::Memory.expr(),         // destination tag
                    range.offset(),                      // source address
                    range.offset() + copy_length.expr(), //
                    return_data_offset.expr(),           // destination address
                    copy_length.expr(),                  // length
                    0.expr(),
                    cb.curr.state.rw_counter.expr() + cb.rw_counter_offset().expr(),
                    copy_length.expr() + copy_length.expr(),
                );
            },
        );

        cb.condition(
            is_create.expr() * is_success.expr() * range.has_length(),
            |cb| {
                cb.copy_table_lookup(
                    cb.curr.state.call_id.expr(),  // source id
                    CopyDataType::Memory.expr(),   // source tag
                    caller_id.expr(),              // destination id
                    CopyDataType::Bytecode.expr(), // destination tag
                    range.offset(),                // source address
                    range.address(),               //
                    0.expr(),                      // destination address
                    range.length(),                // length
                    0.expr(),
                    cb.curr.state.rw_counter.expr() + cb.rw_counter_offset().expr(),
                    range.length(),
                );
            },
        );

        Self {
            opcode,
            range,
            is_root,
            is_create,
            is_success,
            caller_id,
            copy_length,
            return_data_offset,
            return_data_length,
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
        self.opcode.assign(
            region,
            offset,
            step.opcode.map(|opcode| F::from(opcode.as_u64())),
        )?;

        let [memory_offset, length] = [0, 1].map(|i| block.rws[step.rw_indices[i]].stack_value());
        self.range
            .assign(region, offset, memory_offset, length, block.randomness)?;

        self.is_root.assign(
            region,
            offset,
            Some(if call.is_root { F::one() } else { F::zero() }),
        )?;
        self.is_create.assign(
            region,
            offset,
            Some(if call.is_create { F::one() } else { F::zero() }),
        )?;
        self.is_success.assign(
            region,
            offset,
            Some(if call.is_success { F::one() } else { F::zero() }),
        )?;

        for (cell, value) in [
            (&self.caller_id, F::from(call.caller_id as u64)),
            (&self.return_data_length, call.return_data_length.into()),
            (&self.return_data_offset, call.return_data_offset.into()),
        ] {
            cell.assign(region, offset, Some(value))?;
        }

        if !call.is_root {
            self.restore_context
                .assign(region, offset, block, call, step, 8)?;
        }

        let copy_length = if call.is_root {
            0
        } else {
            min(call.return_data_length, length.as_u64())
        };
        self.copy_length
            .assign(region, offset, Some(F::from(copy_length)))?;

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::evm_circuit::test::run_test_circuit_incomplete_fixed_table;
    use crate::evm_circuit::witness::block_convert;
    use crate::test_util::run_test_circuits;
    use eth_types::geth_types::Account;
    use eth_types::{address, bytecode};
    use eth_types::{Address, ToWord, Word};
    use mock::TestContext;

    #[test]
    fn test_return() {
        let bytecode = bytecode! {
            PUSH32(40)
            PUSH32(30) // i think there's a memory expansion issue when there this value is too large?
            RETURN
        };

        assert_eq!(
            run_test_circuits(
                TestContext::<2, 1>::simple_ctx_with_bytecode(bytecode).unwrap(),
                None
            ),
            Ok(())
        );
    }
    // TODO: be sure to add tests that test offset = 0
    // root return with insufficient gas for memory expansion.

    #[test]
    fn test_return_nonroot() {
        let callee_bytecode = bytecode! {
            PUSH32(Word::MAX)
            PUSH1(Word::from(102u64))
            MSTORE
            PUSH1(Word::from(10)) // length!?!?
            PUSH2(Word::from(2)) // offset!?!?!
            RETURN
        };

        let callee = Account {
            address: Address::repeat_byte(0xff),
            code: callee_bytecode.to_vec().into(),
            nonce: Word::one(),
            balance: 0xdeadbeefu64.into(),
            ..Default::default()
        };

        let caller_bytecode = bytecode! {
            PUSH32(Word::from(10)) // call_return_data_length
            PUSH32(Word::from(10)) // call_return_data_offset
            PUSH32(Word::from(14u64))
            PUSH32(Word::from(10u64))
            PUSH32(Word::from(4u64)) // value
            PUSH32(Address::repeat_byte(0xff).to_word())
            PUSH32(Word::from(40000u64)) // gas
            CALL
            STOP
        };

        let caller = Account {
            address: Address::repeat_byte(0x34),
            code: caller_bytecode.to_vec().into(),
            nonce: Word::one(),
            balance: 0xdeadbeefu64.into(),
            ..Default::default()
        };

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
                    .gas(100000u64.into());
            },
            |block, _tx| block.number(0xcafeu64),
        )
        .unwrap();
        let block_data = bus_mapping::mock::BlockData::new_from_geth_data(block.into());
        let mut builder = block_data.new_circuit_input_builder();
        builder
            .handle_block(&block_data.eth_block, &block_data.geth_traces)
            .unwrap();

        assert_eq!(
            run_test_circuit_incomplete_fixed_table(block_convert(
                &builder.block,
                &builder.code_db
            )),
            Ok(())
        );
    }
}
