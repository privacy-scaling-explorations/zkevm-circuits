use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        step::ExecutionState,
        util::{
            common_gadget::CommonErrorGadget,
            constraint_builder::{ConstrainBuilderCommon, EVMConstraintBuilder},
            math_gadget::IsEqualGadget,
            memory_gadget::{CommonMemoryAddressGadget, MemoryAddressGadget},
            CachedRegion, Cell,
        },
        witness::{Block, Call, Chunk, ExecStep, Transaction},
    },
    util::{word::WordExpr, Expr},
};
use eth_types::{evm_types::INVALID_INIT_CODE_FIRST_BYTE, Field};
use halo2_proofs::{circuit::Value, plonk::Error};

/// Gadget for the invalid creation code error
#[derive(Clone, Debug)]
pub(crate) struct ErrorInvalidCreationCodeGadget<F> {
    opcode: Cell<F>,
    first_byte: Cell<F>,
    is_first_byte_invalid: IsEqualGadget<F>,
    memory_address: MemoryAddressGadget<F>,
    common_error_gadget: CommonErrorGadget<F>,
}

impl<F: Field> ExecutionGadget<F> for ErrorInvalidCreationCodeGadget<F> {
    const NAME: &'static str = "ErrorInvalidCreationCode";

    const EXECUTION_STATE: ExecutionState = ExecutionState::ErrorInvalidCreationCode;

    fn configure(cb: &mut EVMConstraintBuilder<F>) -> Self {
        let opcode = cb.query_cell();
        let first_byte = cb.query_cell();

        let offset = cb.query_word_unchecked();
        let length = cb.query_memory_address();

        cb.stack_pop(offset.to_word());
        cb.stack_pop(length.to_word());
        cb.require_true("is_create is true", cb.curr.state.is_create.expr());

        let memory_address = MemoryAddressGadget::construct(cb, offset, length);
        cb.memory_lookup(0.expr(), memory_address.offset(), first_byte.expr(), None);

        let is_first_byte_invalid =
            IsEqualGadget::construct(cb, first_byte.expr(), INVALID_INIT_CODE_FIRST_BYTE.expr());
        cb.require_true(
            "is_first_byte_invalid is true",
            is_first_byte_invalid.expr(),
        );

        let common_error_gadget =
            CommonErrorGadget::construct(cb, opcode.expr(), cb.rw_counter_offset());

        Self {
            opcode,
            first_byte,
            is_first_byte_invalid,
            memory_address,
            common_error_gadget,
        }
    }

    fn assign_exec_step(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        block: &Block<F>,
        _chunk: &Chunk<F>,
        _tx: &Transaction,
        call: &Call,
        step: &ExecStep,
    ) -> Result<(), Error> {
        let opcode = step.opcode().unwrap();
        self.opcode
            .assign(region, offset, Value::known(F::from(opcode.as_u64())))?;

        let [memory_offset, length] = [0, 1].map(|i| block.rws[step.rw_index(i)].stack_value());
        self.memory_address
            .assign(region, offset, memory_offset, length)?;

        let first_byte = block.rws[step.rw_index(2)].memory_value().into();
        self.first_byte
            .assign(region, offset, Value::known(F::from(first_byte)))?;
        self.is_first_byte_invalid.assign(
            region,
            offset,
            F::from(first_byte),
            F::from(INVALID_INIT_CODE_FIRST_BYTE.into()),
        )?;

        self.common_error_gadget
            .assign(region, offset, block, call, step, 5)?;

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::test_util::CircuitTestBuilder;
    use eth_types::{
        address, bytecode, evm_types::OpcodeId, geth_types::Account, Address, Bytecode, U256,
    };
    use mock::{eth, TestContext, MOCK_ACCOUNTS};

    const CALLER_ADDRESS: Address = Address::repeat_byte(0xaa);

    #[test]
    fn test_invalid_creation_code_for_create_opcodes() {
        [false, true].into_iter().for_each(|is_create2| {
            let code = caller_code(is_create2, init_code(10)).into();

            let caller = Account {
                address: CALLER_ADDRESS,
                code,
                nonce: 1.into(),
                balance: eth(10),
                ..Default::default()
            };

            CircuitTestBuilder::new_from_test_ctx(test_ctx(caller)).run();
        });
    }

    // Test ErrInvalidCode in transaction deployment (`tx.to == null`).
    #[test]
    fn test_invalid_creation_code_for_tx_deployment() {
        let deploy_code = init_code(20);
        let test_ctx = TestContext::<1, 1>::new(
            None,
            |accs| {
                accs[0].address(MOCK_ACCOUNTS[0]).balance(eth(20));
            },
            |mut txs, _accs| {
                txs[0]
                    .from(MOCK_ACCOUNTS[0])
                    .gas(53630_u64.into())
                    .value(eth(1))
                    .input(deploy_code.into());
            },
            |block, _tx| block.number(0xcafe_u64),
        )
        .unwrap();
        CircuitTestBuilder::new_from_test_ctx(test_ctx).run();
    }

    fn caller_code(is_create2: bool, init_code: Bytecode) -> Bytecode {
        let init_bytes = init_code.code();
        let init_len = init_bytes.len();

        let memory_bytes: Vec<_> = init_bytes
            .into_iter()
            .chain(0_u8..32 - init_len as u8 % 32)
            .collect();

        let mut code = Bytecode::default();
        memory_bytes.chunks(32).enumerate().for_each(|(idx, word)| {
            code.push(32, U256::from_big_endian(word));
            code.push(32, U256::from(idx * 32));
            code.write_op(OpcodeId::MSTORE);
        });

        if is_create2 {
            code.append(&bytecode! {PUSH1(45)}); // salt
        }
        code.append(&bytecode! {
            PUSH1(init_len) // size
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

    fn init_code(size: usize) -> Bytecode {
        let memory_bytes = vec![0xef; size];
        let memory_value = U256::from_big_endian(&memory_bytes);

        bytecode! {
            PUSH32(memory_value)
            PUSH32(0)
            MSTORE
            PUSH1(5) // length to copy
            PUSH1(32 - memory_bytes.len()) // offset
            RETURN
        }
    }

    fn test_ctx(caller: Account) -> TestContext<2, 1> {
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
                    .gas(103800_u64.into());
            },
            |block, _| block,
        )
        .unwrap()
    }
}
