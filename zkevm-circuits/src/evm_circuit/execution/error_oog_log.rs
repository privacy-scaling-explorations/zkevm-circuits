use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        param::N_BYTES_MEMORY_WORD_SIZE,
        step::ExecutionState,
        util::{
            common_gadget::RestoreContextGadget,
            constraint_builder::{
                ConstraintBuilder, StepStateTransition,
                Transition::{Delta, Same},
            },
            memory_gadget::{MemoryAddressGadget, MemoryExpansionGadget},
            not, sum, CachedRegion, Cell,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    table::{CallContextFieldTag, RwTableTag, TxLogFieldTag},
    util::{build_tx_log_expression, Expr},
};
use array_init::array_init;
use bus_mapping::circuit_input_builder::CopyDataType;
use eth_types::{evm_types::GasCost, evm_types::OpcodeId, ToScalar};
use eth_types::{Field, U256};
use halo2_proofs::{circuit::Value, plonk::Error};

#[derive(Clone, Debug)]
pub(crate) struct ErrorOOGLogGadget<F> {
    // memory address
    memory_address: MemoryAddressGadget<F>,
    // phase2_topics: [Cell<F>; 4],
    // topic_selectors: [Cell<F>; 4],

    memory_expansion: MemoryExpansionGadget<F, 1, N_BYTES_MEMORY_WORD_SIZE>,
    rw_counter_end_of_reversion: Cell<F>,
    restore_context: RestoreContextGadget<F>,
}

impl<F: Field> ExecutionGadget<F> for ErrorOOGLogGadget<F> {
    const NAME: &'static str = "LOG";

    const EXECUTION_STATE: ExecutionState = ExecutionState::ErrorOutOfGasLOG;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        let mstart = cb.query_cell_phase2();
        let msize = cb.query_word_rlc();
        let rw_counter_end_of_reversion = cb.query_cell();

        // Pop mstart_address, msize from stack
        cb.stack_pop(mstart.expr());
        cb.stack_pop(msize.expr());

        // no need to check not in static call, since write protection error will handle it.

        // constrain topics in logs
        // let phase2_topics = array_init(|_| cb.query_cell_phase2());
        // let topic_selectors: [Cell<F>; 4] = array_init(|_| cb.query_cell());
        // for (idx, topic) in phase2_topics.iter().enumerate() {
        //     cb.condition(topic_selectors[idx].expr(), |cb| {
        //         cb.stack_pop(topic.expr());
        //     });
        //     cb.condition(topic_selectors[idx].expr() * is_persistent.expr(), |cb| {
        //         cb.tx_log_lookup(
        //             tx_id.expr(),
        //             cb.curr.state.log_id.expr() + 1.expr(),
        //             TxLogFieldTag::Topic,
        //             idx.expr(),
        //             topic.expr(),
        //         );
        //     });
        // }

        let opcode = cb.query_cell();
        let topic_count = opcode.expr() - OpcodeId::LOG0.as_u8().expr();

        // check memory copy
        let memory_address = MemoryAddressGadget::construct(cb, mstart, msize);

        // Calculate the next memory size and the gas cost for this memory
        // access
        let memory_expansion = MemoryExpansionGadget::construct(cb, [memory_address.address()]);

        let gas_cost = GasCost::LOG.as_u64().expr()
            + GasCost::LOG.as_u64().expr() * topic_count.clone()
            + 8.expr() * memory_address.length()
            + memory_expansion.gas_cost();

        // current call must be failed.
        cb.call_context_lookup(false.expr(), None, CallContextFieldTag::IsSuccess, 0.expr());

        cb.call_context_lookup(
            false.expr(),
            None,
            CallContextFieldTag::RwCounterEndOfReversion,
            rw_counter_end_of_reversion.expr(),
        );

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
                rw_counter: Delta(4.expr() + cb.curr.state.reversible_write_counter.expr()),
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
            memory_address,
            //phase2_topics,
            //topic_selectors,
            memory_expansion,
            rw_counter_end_of_reversion,
            restore_context,
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

        let [memory_start, msize] =
            [step.rw_indices[0], step.rw_indices[1]].map(|idx| block.rws[idx].stack_value());

        let memory_address = self
            .memory_address
            .assign(region, offset, memory_start, msize)?;

        // Memory expansion
        self.memory_expansion
            .assign(region, offset, step.memory_word_size(), [memory_address])?;

        let opcode = step.opcode.unwrap();
        let topic_count = opcode.postfix().expect("opcode with postfix") as usize;
        assert!(topic_count <= 4);

        self.rw_counter_end_of_reversion.assign(
            region,
            offset,
            Value::known(F::from(call.rw_counter_end_of_reversion as u64)),
        )?;
        self.restore_context
        .assign(region, offset, block, call, step, 3)?;

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use eth_types::{evm_types::OpcodeId, Bytecode, Word};
    use mock::TestContext;
    use rand::Rng;

    use crate::test_util::run_test_circuits;

    #[test]
    fn log_gadget_simple() {
        // zero topic: log0
        test_log_ok(&[], false);
        // one topic: log1
        // test_log_ok(&[Word::from(0xA0)], true);
        // // two topics: log2
        // test_log_ok(&[Word::from(0xA0), Word::from(0xef)], true);
        // // three topics: log3
        // test_log_ok(
        //     &[Word::from(0xA0), Word::from(0xef), Word::from(0xb0)],
        //     true,
        // );
        // // four topics: log4
        // test_log_ok(
        //     &[
        //         Word::from(0xA0),
        //         Word::from(0xef),
        //         Word::from(0xb0),
        //         Word::from(0x37),
        //     ],
        //     true,
        // );
    }

    // test single log code and single copy log step
    fn test_log_ok(topics: &[Word], is_persistent: bool) {
        let mut pushdata = [0u8; 320];
        rand::thread_rng().try_fill(&mut pushdata[..]).unwrap();
        let mut code_prepare = prepare_code(&pushdata, 1);

        let log_codes = [
            OpcodeId::LOG0,
            OpcodeId::LOG1,
            OpcodeId::LOG2,
            OpcodeId::LOG3,
            OpcodeId::LOG4,
        ];

        let topic_count = topics.len();
        let cur_op_code = log_codes[topic_count];

        // use more than 256 for testing offset rlc
        let mstart = 0x102usize;
        let msize = 0x20usize;
        let mut code = Bytecode::default();
        // make dynamic topics push operations
        for topic in topics {
            code.push(32, *topic);
        }
        code.push(32, Word::from(msize));
        code.push(32, Word::from(mstart));
        code.write_op(cur_op_code);
        if is_persistent {
            code.write_op(OpcodeId::STOP);
        } else {
            // make current call failed with false persistent
            code.write_op(OpcodeId::INVALID(0xfe));
        }

        code_prepare.append(&code);

        assert_eq!(
            run_test_circuits(
                TestContext::<2, 1>::simple_ctx_with_bytecode(code_prepare).unwrap(),
                None
            ),
            Ok(()),
        );
    }

    /// prepare memory reading data
    fn prepare_code(data: &[u8], offset: usize) -> Bytecode {
        assert_eq!(data.len() % 32, 0);
        // prepare memory data
        let mut code = Bytecode::default();
        for (i, d) in data.chunks(32).enumerate() {
            code.push(32, Word::from_big_endian(d));
            code.push(32, Word::from(offset + i * 32));
            code.write_op(OpcodeId::MSTORE);
        }
        code
    }

///////////////////////

}
