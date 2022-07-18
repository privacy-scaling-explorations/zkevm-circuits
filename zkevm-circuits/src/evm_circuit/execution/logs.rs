use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        param::N_BYTES_MEMORY_WORD_SIZE,
        step::ExecutionState,
        table::{CallContextFieldTag, RwTableTag, TxLogFieldTag},
        util::{
            common_gadget::SameContextGadget,
            constraint_builder::{
                ConstraintBuilder, StepStateTransition,
                Transition::{Delta, To},
            },
            from_bytes,
            memory_gadget::{MemoryAddressGadget, MemoryExpansionGadget},
            sum, CachedRegion, Cell, Word,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    util::Expr,
};
use array_init::array_init;
use eth_types::Field;
use eth_types::{evm_types::GasCost, evm_types::OpcodeId, ToLittleEndian, ToScalar};
use halo2_proofs::plonk::Error;

#[derive(Clone, Debug)]
pub(crate) struct LogGadget<F> {
    same_context: SameContextGadget<F>,
    // memory address
    memory_address: MemoryAddressGadget<F>,
    topics: [Cell<F>; 4],
    topic_selectors: [Cell<F>; 4],

    contract_address: Cell<F>,
    is_static_call: Cell<F>,
    is_persistent: Cell<F>,
    tx_id: Cell<F>,
    memory_expansion: MemoryExpansionGadget<F, 1, N_BYTES_MEMORY_WORD_SIZE>,
}

impl<F: Field> ExecutionGadget<F> for LogGadget<F> {
    const NAME: &'static str = "LOG";

    const EXECUTION_STATE: ExecutionState = ExecutionState::LOG;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        let mstart = cb.query_cell();
        let msize = cb.query_rlc();

        // Pop mstart_address, msize from stack
        cb.stack_pop(mstart.expr());
        cb.stack_pop(msize.expr());
        // read tx id
        let tx_id = cb.call_context(None, CallContextFieldTag::TxId);
        // constrain not in static call
        let is_static_call = cb.call_context(None, CallContextFieldTag::IsStatic);
        cb.require_zero("is_static_call is false", is_static_call.expr());

        // check contract_address in CallContext & TxLog
        // use call context's  callee address as contract address
        let contract_address = cb.call_context(None, CallContextFieldTag::CalleeAddress);
        let is_persistent = cb.call_context(None, CallContextFieldTag::IsPersistent);
        cb.require_boolean("is_persistent is bool", is_persistent.expr());

        cb.condition(is_persistent.expr(), |cb| {
            cb.tx_log_lookup(
                tx_id.expr(),
                cb.curr.state.log_id.expr() + 1.expr(),
                TxLogFieldTag::Address,
                0.expr(),
                contract_address.expr(),
            );
        });

        // constrain topics in logs
        let topics = array_init(|_| cb.query_cell());
        let topic_selectors: [Cell<F>; 4] = array_init(|_| cb.query_cell());
        for (idx, topic) in topics.iter().enumerate() {
            cb.condition(topic_selectors[idx].expr(), |cb| {
                cb.stack_pop(topic.expr());
            });
            cb.condition(topic_selectors[idx].expr() * is_persistent.expr(), |cb| {
                cb.tx_log_lookup(
                    tx_id.expr(),
                    cb.curr.state.log_id.expr() + 1.expr(),
                    TxLogFieldTag::Topic,
                    idx.expr(),
                    topic.expr(),
                );
            });
        }

        let opcode = cb.query_cell();
        let topic_count = opcode.expr() - OpcodeId::LOG0.as_u8().expr();

        // TOPIC_COUNT == Non zero topic selector count
        cb.require_equal(
            " sum of topic selectors = topic_count ",
            topic_count.clone(),
            sum::expr(topic_selectors.clone()),
        );

        // `topic_selectors` order must be from 1 --> 0
        for idx in 0..4 {
            cb.require_boolean("topic selector is bool ", topic_selectors[idx].expr());
            if idx > 0 {
                let selector_prev = topic_selectors[idx - 1].expr();
                // selector can transit from 1 to 0 only once as [1, 1 ..., 0]
                cb.require_boolean(
                    "Constrain topic selectors can only transit from 1 to 0",
                    selector_prev - topic_selectors[idx].expr(),
                );
            }
        }

        // check memory copy
        let memory_address = MemoryAddressGadget::construct(cb, mstart, msize.clone());

        // Calculate the next memory size and the gas cost for this memory
        // access
        let memory_expansion = MemoryExpansionGadget::construct(
            cb,
            cb.curr.state.memory_word_size.expr(),
            [memory_address.address()],
        );

        // If the iterative process has not yet finished, we constrain the next step to
        // be another `CopyToLog` while adding some additional
        // constraints to the auxiliary data.
        // Constrain the next step CopyToLog if length != 0
        cb.constrain_next_step(
            ExecutionState::CopyToLog,
            Some(memory_address.has_length()),
            |cb| {
                let next_src_addr = cb.query_cell();
                let next_bytes_left = cb.query_cell();
                let next_src_addr_end = cb.query_cell();
                let next_is_persistent = cb.query_bool();
                let next_tx_id = cb.query_cell();
                let next_data_start_index = cb.query_cell();

                cb.require_equal(
                    "next_src_addr = memory_offset",
                    next_src_addr.expr(),
                    memory_address.offset(),
                );
                cb.require_equal(
                    "next_bytes_left = length",
                    next_bytes_left.expr(),
                    memory_address.length(),
                );
                cb.require_equal(
                    "next_src_addr_end = memory_offset + length",
                    next_src_addr_end.expr(),
                    memory_address.offset() + memory_address.length(),
                );
                cb.require_equal(
                    "next_is_persistent = is_persistent",
                    next_is_persistent.expr(),
                    is_persistent.expr(),
                );
                cb.require_equal("next_tx_id = tx_id", next_tx_id.expr(), tx_id.expr());
                cb.require_zero(
                    "next_data_start_index starts with 0",
                    next_data_start_index.expr(),
                );
            },
        );

        let gas_cost = GasCost::LOG.as_u64().expr()
            + GasCost::LOG.as_u64().expr() * topic_count.clone()
            + 8.expr() * from_bytes::expr(&msize.cells)
            + memory_expansion.gas_cost();
        // State transition

        let step_state_transition = StepStateTransition {
            rw_counter: Delta(cb.rw_counter_offset()),
            program_counter: Delta(1.expr()),
            stack_pointer: Delta(2.expr() + topic_count),
            memory_word_size: To(memory_expansion.next_memory_word_size()),
            log_id: Delta(is_persistent.expr()),
            gas_left: Delta(-gas_cost),
            ..Default::default()
        };

        let same_context = SameContextGadget::construct(cb, opcode, step_state_transition);

        Self {
            same_context,
            memory_address,
            topics,
            topic_selectors,
            contract_address,
            is_static_call,
            is_persistent,
            tx_id,
            memory_expansion,
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
        self.same_context.assign_exec_step(region, offset, step)?;

        let [memory_start, msize] =
            [step.rw_indices[0], step.rw_indices[1]].map(|idx| block.rws[idx].stack_value());

        let memory_address =
            self.memory_address
                .assign(region, offset, memory_start, msize, block.randomness)?;

        // Memory expansion
        self.memory_expansion
            .assign(region, offset, step.memory_word_size(), [memory_address])?;

        let opcode = step.opcode.unwrap();
        let topic_count = (opcode.as_u8() - OpcodeId::LOG0.as_u8()) as usize;
        assert!(topic_count <= 4);

        let is_persistent = call.is_persistent as u64;
        let mut topic_stack_entry = if topic_count > 0 {
            step.rw_indices[6 + call.is_persistent as usize]
        } else {
            // if topic_count == 0, this value will be no used anymore
            (RwTableTag::Stack, 0usize)
        };

        for i in 0..4 {
            let mut topic = Word::random_linear_combine([0; 32], block.randomness);
            if i < topic_count {
                topic = Word::random_linear_combine(
                    block.rws[topic_stack_entry].stack_value().to_le_bytes(),
                    block.randomness,
                );
                self.topic_selectors[i].assign(region, offset, Some(F::one()))?;
                topic_stack_entry.1 += 1;
            } else {
                self.topic_selectors[i].assign(region, offset, Some(F::zero()))?;
            }
            self.topics[i].assign(region, offset, Some(topic))?;
        }

        self.contract_address
            .assign(region, offset, call.callee_address.to_scalar())?;

        self.is_static_call
            .assign(region, offset, Some(F::from(call.is_static as u64)))?;
        self.is_persistent
            .assign(region, offset, Some(F::from(is_persistent)))?;
        self.tx_id
            .assign(region, offset, Some(F::from(tx.id as u64)))?;

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use eth_types::{bytecode, evm_types::OpcodeId, Bytecode, Word};
    use mock::TestContext;

    use crate::test_util::run_test_circuits;

    //TODO：add is_persistent = false cases
    #[test]
    fn log_tests() {
        // zero topic: log0
        test_log_ok(&[]);
        // one topic: log1
        test_log_ok(&[Word::from(0xA0)]);
        // two topics: log2
        test_log_ok(&[Word::from(0xA0), Word::from(0xef)]);
        // three topics: log3
        test_log_ok(&[Word::from(0xA0), Word::from(0xef), Word::from(0xb0)]);
        // four topics: log4
        test_log_ok(&[
            Word::from(0xA0),
            Word::from(0xef),
            Word::from(0xb0),
            Word::from(0x37),
        ]);
    }

    #[test]
    fn multi_log_tests() {
        // zero topic: log0
        test_multi_log_ok(&[]);
        // one topic: log1
        test_multi_log_ok(&[Word::from(0xA0)]);
        // two topics: log2
        test_multi_log_ok(&[Word::from(0xA0), Word::from(0xef)]);
        // three topics: log3
        test_multi_log_ok(&[Word::from(0xA0), Word::from(0xef), Word::from(0xb0)]);
        // four topics: log4
        test_multi_log_ok(&[
            Word::from(0xA0),
            Word::from(0xef),
            Word::from(0xb0),
            Word::from(0x37),
        ]);
    }

    // test single log code and single copy log step
    fn test_log_ok(topics: &[Word]) {
        let pushdata = "1234567890abcdef1234567890abcdef";
        // prepare first 32 bytes for memory reading
        let mut code_prepare = prepare_code(pushdata, 0);

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
        code.write_op(OpcodeId::STOP);
        code_prepare.append(&code);

        assert_eq!(
            run_test_circuits(
                TestContext::<2, 1>::simple_ctx_with_bytecode(code_prepare).unwrap(),
                None,
            ),
            Ok(()),
        );
    }

    // test multi log op codes and multi copy log steps
    fn test_multi_log_ok(topics: &[Word]) {
        // prepare memory data
        let pushdata = "1234567890abcdef1234567890abcdef";
        // prepare first 32 bytes for memory reading
        let mut code_prepare = prepare_code(pushdata, 0);

        let log_codes = [
            OpcodeId::LOG0,
            OpcodeId::LOG1,
            OpcodeId::LOG2,
            OpcodeId::LOG3,
            OpcodeId::LOG4,
        ];

        let topic_count = topics.len();
        let cur_op_code = log_codes[topic_count];

        let mut mstart = 0x00usize;
        let mut msize = 0x10usize;
        // first log op code
        let mut code = Bytecode::default();
        // make dynamic topics push operations
        for topic in topics {
            code.push(32, *topic);
        }
        code.push(32, Word::from(msize));
        code.push(32, Word::from(mstart));
        code.write_op(cur_op_code);

        // second log op code
        // prepare additinal bytes for memory reading
        code.append(&prepare_code(pushdata, 0x20));
        mstart = 0x00usize;
        // when mszie > 0x20 (32) needs multi copy steps
        msize = 0x30usize;
        for topic in topics {
            code.push(32, *topic);
        }
        code.push(32, Word::from(msize));
        code.push(32, Word::from(mstart));
        code.write_op(cur_op_code);

        code.write_op(OpcodeId::STOP);
        code_prepare.append(&code);

        assert_eq!(
            run_test_circuits(
                TestContext::<2, 1>::simple_ctx_with_bytecode(code_prepare).unwrap(),
                None,
            ),
            Ok(()),
        );
    }

    /// prepare memory reading data
    fn prepare_code(data: &str, offset: u32) -> Bytecode {
        // data is in hex format
        assert_eq!(data.bytes().len(), 32);
        // prepare memory data
        let pushdata = hex::decode(data).unwrap();
        return bytecode! {
            // populate memory.
            PUSH16(Word::from_big_endian(&pushdata))
            PUSH1(offset) // offset
            MSTORE
        };
    }
}
