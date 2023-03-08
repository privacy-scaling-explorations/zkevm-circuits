use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        param::{N_BYTES_GAS, N_BYTES_U64},
        step::ExecutionState,
        util::{
            from_bytes,
            common_gadget::RestoreContextGadget, constraint_builder::ConstraintBuilder,
            math_gadget::IsEqualGadget, memory_gadget::MemoryAddressGadget, CachedRegion, Cell,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    table::CallContextFieldTag,
    util::Expr,
};

use eth_types::{evm_types::GasCost, Field};
use halo2_proofs::{circuit::Value, plonk::Error};


/// Gadget for code store oog and max code size exceed
#[derive(Clone, Debug)]
pub(crate) struct ErrorInvalidCreationCodeGadget<F> {
    opcode: Cell<F>,
    memory_address: MemoryAddressGadget<F>,
    first_byte: Cell<F>,
    is_first_byte_invalid: IsEqualGadget<F>,
    rw_counter_end_of_reversion: Cell<F>,
    restore_context: RestoreContextGadget<F>,
}

impl<F: Field> ExecutionGadget<F> for ErrorInvalidCreationCodeGadget<F> {
    const NAME: &'static str = "ErrorCodeStore";

    const EXECUTION_STATE: ExecutionState = ExecutionState::ErrorInvalidCreationCode;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        let opcode = cb.query_cell();
        let first_byte = cb.query_cell();

        cb.opcode_lookup(opcode.expr(), 1.expr());

        let offset = cb.query_cell_phase2();
        let length = cb.query_word_rlc();
        let rw_counter_end_of_reversion = cb.query_cell();

        cb.stack_pop(offset.expr());
        cb.stack_pop(length.expr());
        cb.require_true("is_create is true", cb.curr.state.is_create.expr());

        let memory_address = MemoryAddressGadget::construct(cb, offset, length);
        //TODO: lookup memory for first byte
        cb.memory_lookup(0.expr(), memory_address.offset(), first_byte.expr(), None);

        // constrain first byte is 0xef
        let is_first_byte_invalid = IsEqualGadget::construct(cb, first_byte.expr(), 
        0xef.expr());

        cb.require_true("is_first_byte_invalid is true", is_first_byte_invalid.expr());

        cb.call_context_lookup(false.expr(), None, CallContextFieldTag::IsSuccess, 0.expr());
        cb.call_context_lookup(
            false.expr(),
            None,
            CallContextFieldTag::RwCounterEndOfReversion,
            rw_counter_end_of_reversion.expr(),
        );

        // Case C in the return specs.
        let restore_context = RestoreContextGadget::construct(
            cb,
            0.expr(),
            0.expr(),
            memory_address.offset(),
            memory_address.length(),
            0.expr(),
            0.expr(),
        );

        // constrain RwCounterEndOfReversion
        let rw_counter_end_of_step =
            cb.curr.state.rw_counter.expr() + cb.rw_counter_offset() - 1.expr();
        cb.require_equal(
            "rw_counter_end_of_reversion = rw_counter_end_of_step + reversible_counter",
            rw_counter_end_of_reversion.expr(),
            rw_counter_end_of_step + cb.curr.state.reversible_write_counter.expr(),
        );

        Self {
            opcode,
            first_byte,
            is_first_byte_invalid,
            memory_address,
            rw_counter_end_of_reversion,
            restore_context,
        }
    }

    fn assign_exec_step(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        block: &Block<F>,
        _tx: &Transaction,
        call: &Call,
        step: &ExecStep,
    ) -> Result<(), Error> {
        let opcode = step.opcode.unwrap();
        self.opcode
            .assign(region, offset, Value::known(F::from(opcode.as_u64())))?;

        let [memory_offset, length] = [0, 1].map(|i| block.rws[step.rw_indices[i]].stack_value());
        self.memory_address
            .assign(region, offset, memory_offset, length)?;

        let byte = block.rws[step.rw_indices[2]].memory_value();

        self.first_byte
            .assign(region, offset, Value::known(F::from(byte as u64)))?;
        self.is_first_byte_invalid.assign(region, offset, F::from(byte as u64), F::from(0xef as u64))?;

        self.rw_counter_end_of_reversion.assign(
            region,
            offset,
            Value::known(F::from(call.rw_counter_end_of_reversion as u64)),
        )?;
        self.restore_context
            .assign(region, offset, block, call, step, 5)?;
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use bus_mapping::circuit_input_builder::CircuitsParams;
    use eth_types::{
        address, bytecode, evm_types::OpcodeId, geth_types::Account, Address, Bytecode, Word,
    };

    use lazy_static::lazy_static;
    use mock::{eth, TestContext, MOCK_ACCOUNTS};

    use crate::test_util::CircuitTestBuilder;

    const CALLEE_ADDRESS: Address = Address::repeat_byte(0xff);
    lazy_static! {
        static ref CALLER_ADDRESS: Address = address!("0x00bbccddee000000000000000000000000002400");
    }

    const MAXCODESIZE: u64 = 0x6000u64;

    fn run_test_circuits(ctx: TestContext<2, 1>) {
        CircuitTestBuilder::new_from_test_ctx(ctx)
            .params(CircuitsParams {
                max_rws: 4500,
                ..Default::default()
            })
            .run();
    }

    fn initialization_bytecode() -> Bytecode {
        let memory_bytes = [0xef; 10];
        let memory_value = Word::from_big_endian(&memory_bytes);

        let mut code = bytecode! {
            PUSH10(memory_value)
            PUSH32(0)
            MSTORE
            PUSH2( 5 ) // length to copy
            PUSH2(32u64 - u64::try_from(memory_bytes.len()).unwrap()) // offset
            //PUSH2(0x00) // offset

        };
        code.write_op(OpcodeId::RETURN);

        code
    }

    fn creator_bytecode(initialization_bytecode: Bytecode, is_create2: bool) -> Bytecode {
        let initialization_bytes = initialization_bytecode.code();
        let mut code = Bytecode::default();

        //construct maxcodesize + 1 memory bytes
        let code_creator: Vec<u8> = initialization_bytes
            .to_vec()
            .iter()
            .cloned()
            .chain(0u8..((32 - initialization_bytes.len() % 32) as u8))
            .collect();
        for (index, word) in code_creator.chunks(32).enumerate() {
            code.push(32, Word::from_big_endian(word));
            code.push(32, Word::from(index * 32));
            code.write_op(OpcodeId::MSTORE);
        }

        if is_create2 {
            code.append(&bytecode! {PUSH1(45)}); // salt;
        }
        code.append(&bytecode! {
            PUSH32(initialization_bytes.len()) // size
            PUSH2(0x00) // offset
            PUSH2(23414) // value
        });
        code.write_op(if is_create2 {
            OpcodeId::CREATE2
        } else {
            OpcodeId::CREATE
        });
        code.append(&bytecode! {
            PUSH1(0)
            PUSH1(0)
            RETURN
        });

        code
    }

    fn test_context(caller: Account) -> TestContext<2, 1> {
        TestContext::new(
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
                    .gas(103800u64.into());
            },
            |block, _| block,
        )
        .unwrap()
    }

    #[test]
    fn test_invalid_creation_code() {
        //for is_create2 in [false, true] {
        for is_create2 in [false] {
            let initialization_code = initialization_bytecode();
            let root_code = creator_bytecode(initialization_code, is_create2);
            let caller = Account {
                address: *CALLER_ADDRESS,
                code: root_code.into(),
                nonce: Word::one(),
                balance: eth(10),
                ..Default::default()
            };
            run_test_circuits(test_context(caller));
        }
    }

    // TODO: add tx deploy case for invalid creation code.
    #[test]
    fn test_tx_deploy_invalid_creation_code() {
        let code = initialization_bytecode();

        let ctx = TestContext::<1, 1>::new(
            None,
            |accs| {
                accs[0].address(MOCK_ACCOUNTS[0]).balance(eth(20));
            },
            |mut txs, _accs| {
                txs[0]
                    .from(MOCK_ACCOUNTS[0])
                    .gas(53446u64.into())
                    .value(eth(2))
                    .input(code.into());
            },
            |block, _tx| block.number(0xcafeu64),
        )
        .unwrap();

        CircuitTestBuilder::new_from_test_ctx(ctx).run();
    }

}
