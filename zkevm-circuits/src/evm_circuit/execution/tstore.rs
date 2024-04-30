use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        step::ExecutionState,
        util::{
            common_gadget::SameContextGadget,
            constraint_builder::{
                ConstrainBuilderCommon, EVMConstraintBuilder, ReversionInfo, StepStateTransition,
                Transition::Delta,
            },
            CachedRegion, Cell, StepRws,
        },
        witness::{Block, Call, Chunk, ExecStep, Transaction},
    },
    table::CallContextFieldTag,
    util::{
        word::{Word32Cell, WordExpr, WordLoHiCell},
        Expr,
    },
};
use bus_mapping::evm::OpcodeId;
use eth_types::Field;
use halo2_proofs::{circuit::Value, plonk::Error};

#[derive(Clone, Debug)]
pub(crate) struct TstoreGadget<F> {
    same_context: SameContextGadget<F>,
    tx_id: Cell<F>,
    is_static: Cell<F>,
    reversion_info: ReversionInfo<F>,
    callee_address: WordLoHiCell<F>,
    key: Word32Cell<F>,
    value: Word32Cell<F>,
    value_prev: Word32Cell<F>,
}

impl<F: Field> ExecutionGadget<F> for TstoreGadget<F> {
    const NAME: &'static str = "TSTORE";

    const EXECUTION_STATE: ExecutionState = ExecutionState::TSTORE;

    fn configure(cb: &mut EVMConstraintBuilder<F>) -> Self {
        let opcode = cb.query_cell();

        let tx_id = cb.call_context(None, CallContextFieldTag::TxId);

        // constraint not in static call
        let is_static = cb.call_context(None, CallContextFieldTag::IsStatic);
        cb.require_zero("is_static is false", is_static.expr());

        let mut reversion_info = cb.reversion_info_read(None);
        let callee_address = cb.call_context_read_as_word(None, CallContextFieldTag::CalleeAddress);

        let key = cb.query_word32();
        // Pop the key from the stack
        cb.stack_pop(key.to_word());

        let value = cb.query_word32();
        // Pop the value from the stack
        cb.stack_pop(value.to_word());

        let value_prev = cb.query_word32();
        cb.account_transient_storage_write(
            callee_address.to_word(),
            key.to_word(),
            value.to_word(),
            value_prev.to_word(),
            tx_id.expr(),
            Some(&mut reversion_info),
        );

        let step_state_transition = StepStateTransition {
            rw_counter: Delta(8.expr()),
            program_counter: Delta(1.expr()),
            stack_pointer: Delta(2.expr()),
            reversible_write_counter: Delta(1.expr()),
            gas_left: Delta(-OpcodeId::TSTORE.constant_gas_cost().expr()),
            ..Default::default()
        };
        let same_context = SameContextGadget::construct(cb, opcode, step_state_transition);

        Self {
            same_context,
            tx_id,
            is_static,
            reversion_info,
            callee_address,
            key,
            value,
            value_prev,
        }
    }

    fn assign_exec_step(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        block: &Block<F>,
        _chunk: &Chunk<F>,
        tx: &Transaction,
        call: &Call,
        step: &ExecStep,
    ) -> Result<(), Error> {
        self.same_context.assign_exec_step(region, offset, step)?;

        self.tx_id
            .assign(region, offset, Value::known(F::from(tx.id)))?;
        self.is_static
            .assign(region, offset, Value::known(F::from(call.is_static as u64)))?;
        self.reversion_info.assign(
            region,
            offset,
            call.rw_counter_end_of_reversion,
            call.is_persistent,
        )?;
        self.callee_address
            .assign_h160(region, offset, call.address)?;

        let mut rws = StepRws::new(block, step);

        rws.offset_add(5);

        let key = rws.next().stack_value();
        let value = rws.next().stack_value();
        self.key.assign_u256(region, offset, key)?;
        self.value.assign_u256(region, offset, value)?;

        let (_, value_prev, _, _) = rws.next().storage_value_aux();
        self.value_prev.assign_u256(region, offset, value_prev)?;

        Ok(())
    }
}

#[cfg(test)]
mod test {

    use crate::test_util::CircuitTestBuilder;
    use eth_types::{bytecode, Word};
    use mock::{test_ctx::helpers::tx_from_1_to_0, TestContext, MOCK_ACCOUNTS};

    #[test]
    fn tstore_gadget_no_refund() {
        test_ok(
            0x030201.into(),
            0x060504.into(),
            0x060504.into(),
            0x060504.into(),
        );
    }

    fn test_ok(key: Word, value: Word, value_prev: Word, original_value: Word) {
        let bytecode = bytecode! {
            PUSH32(value_prev)
            PUSH32(key)
            TSTORE
            PUSH32(value)
            PUSH32(key)
            TSTORE
            STOP
        };
        let ctx = TestContext::<2, 1>::new(
            None,
            |accs| {
                accs[0]
                    .address(MOCK_ACCOUNTS[0])
                    .balance(Word::from(10u64.pow(19)))
                    .code(bytecode)
                    .storage(vec![(key, original_value)].into_iter());
                accs[1]
                    .address(MOCK_ACCOUNTS[1])
                    .balance(Word::from(10u64.pow(19)));
            },
            tx_from_1_to_0,
            |block, _txs| block,
        )
        .unwrap();

        CircuitTestBuilder::new_from_test_ctx(ctx).run();
    }

    #[test]
    fn test_revert() {
        let key = Word::from(34);
        let value = Word::from(100);

        let bytecode = bytecode! {
            PUSH32(value)
            PUSH32(key)
            TSTORE
            PUSH32(0)
            PUSH32(0)
            REVERT
        };
        let ctx = TestContext::<2, 1>::new(
            None,
            |accs| {
                accs[0]
                    .address(MOCK_ACCOUNTS[0])
                    .balance(Word::from(10u64.pow(19)))
                    .code(bytecode);
                accs[1]
                    .address(MOCK_ACCOUNTS[1])
                    .balance(Word::from(10u64.pow(19)));
            },
            tx_from_1_to_0,
            |block, _txs| block,
        )
        .unwrap();

        CircuitTestBuilder::new_from_test_ctx(ctx).run();
    }
}
