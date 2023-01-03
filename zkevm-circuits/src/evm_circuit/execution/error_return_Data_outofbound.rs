use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        param::{N_BYTES_MEMORY_ADDRESS, N_BYTES_MEMORY_WORD_SIZE},
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
    // return_data_length: Cell<F>,
    /// read.
    memory_offset: Cell<F>,
    data_offset:  RandomLinearCombination<F, 31>,
    length: RandomLinearCombination<F, 31>,
    //end : Cell<F>,

    //return_data_offset: Cell<F>,
    /// Holds the size of the last callee return data.
    return_data_size: Cell<F>,

    // is_dataset_overflow: IsZeroGadget<F>,
    // is_end_overflow: IsZeroGadget<F>,
    is_end_exceed_length: LtGadget<F, N_BYTES_MEMORY_WORD_SIZE>,
    restore_context: RestoreContextGadget<F>,
}

impl<F: Field> ExecutionGadget<F> for ErrorReturnDataOutOfBoundGadget<F> {
    const NAME: &'static str = "ErrorReturnDataOutOfBoundGadget";

    const EXECUTION_STATE: ExecutionState = ExecutionState::ErrorReturnDataOutOfBound;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        let opcode = cb.query_cell();
        let memory_offset = cb.query_cell();
        let data_offset = cb.query_rlc();
        let length = cb.query_rlc();

        let return_data_size = cb.query_cell();

        cb.require_equal("opcode is RETURNDATACOPY", opcode.expr(), OpcodeId::RETURNDATACOPY.expr());

        // 1. Pop dest_offset, offset, length from stack
        cb.stack_pop(memory_offset.expr());
        cb.stack_pop(data_offset.expr());
        cb.stack_pop(length.expr());

        // read last callee return data length
        cb.call_context_lookup(
            false.expr(),
            None,
            CallContextFieldTag::LastCalleeReturnDataLength,
            return_data_size.expr(),
        );

        // check overflows 
        // check data_offset or end is u64 overflow, or 
        // last_callee_return_data_length < end
        let is_end_exceed_length = LtGadget::construct(cb,  
            return_data_size.expr(), from_bytes::expr(&data_offset.cells) + from_bytes::expr(&length.cells));
        

        cb.require_equal("return_data_size < data offset + size", is_end_exceed_length.expr(), 1.expr());
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
                    0.expr() + cb.curr.state.reversible_write_counter.expr(),
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
            memory_offset,
            data_offset,
            length,
            is_end_exceed_length,
            return_data_size,
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

        self.opcode
            .assign(region, offset, Value::known(F::from(opcode.as_u64())))?;
       
        // let condition_rlc =
        //     RLCWord::random_linear_combine(condition.to_le_bytes(), block.randomness);
        self.restore_context
            .assign(region, offset, block, call, step, 2 as usize)?;
        Ok(())
    }
}


#[cfg(test)]
mod test {
    use crate::evm_circuit::test::rand_bytes;
    use crate::test_util::run_test_circuits_with_params;
    use bus_mapping::circuit_input_builder::CircuitsParams;
    use eth_types::{bytecode, ToWord, Word};
    use mock::test_ctx::TestContext;

    fn test_ok_internal(
        return_data_offset: usize,
        return_data_size: usize,
        dest_offset: usize,
        offset: usize,
        size: usize,
    ) {
        let (addr_a, addr_b) = (mock::MOCK_ACCOUNTS[0], mock::MOCK_ACCOUNTS[1]);

        let pushdata = rand_bytes(32);
        let return_offset =
            std::cmp::max((return_data_offset + return_data_size) as i64 - 32, 0) as usize;
        let code_b = bytecode! {
            PUSH32(Word::from_big_endian(&pushdata))
            PUSH32(return_offset)
            MSTORE

            PUSH32(return_data_size)
            PUSH32(return_data_offset)
            RETURN
            STOP
        };

        // code A calls code B.
        let code_a = bytecode! {
            // call ADDR_B.
            PUSH32(return_data_size) // retLength
            PUSH32(return_data_offset) // retOffset
            PUSH1(0x00) // argsLength
            PUSH1(0x00) // argsOffset
            PUSH1(0x00) // value
            PUSH32(addr_b.to_word()) // addr
            PUSH32(0x1_0000) // gas
            CALL
            PUSH32(size) // size
            PUSH32(offset) // offset
            PUSH32(dest_offset) // dest_offset
            RETURNDATACOPY
            STOP
        };

        let ctx = TestContext::<3, 1>::new(
            None,
            |accs| {
                accs[0].address(addr_a).code(code_a);
                accs[1].address(addr_b).code(code_b);
                accs[2]
                    .address(mock::MOCK_ACCOUNTS[2])
                    .balance(Word::from(1u64 << 30));
            },
            |mut txs, accs| {
                txs[0].to(accs[0].address).from(accs[2].address);
            },
            |block, _tx| block,
        )
        .unwrap();

        assert_eq!(
            run_test_circuits_with_params(
                ctx,
                None,
                CircuitsParams {
                    max_rws: 2048,
                    ..Default::default()
                }
            ),
            Ok(())
        );
    }

    // TODO: Add negative cases for out-of-bound and out-of-gas
    #[test]
    fn returndatacopy_out_of_bound_error() {
        test_ok_internal(0x00, 0x10, 0x20, 0x10, 0x10);
    }

    // #[test]
    // #[should_panic]
    // fn returndatacopy_gadget_out_of_gas() {
    //     test_ok_internal(0x00, 0x10, 0x2000000, 0x00, 0x10);
    // }
}
