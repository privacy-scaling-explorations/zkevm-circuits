use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        step::ExecutionState,
        util::{
            common_gadget::CommonErrorGadget,
            constraint_builder::{ConstrainBuilderCommon, EVMConstraintBuilder},
            math_gadget::{IsZeroGadget, IsZeroWordGadget},
            AccountAddress, CachedRegion, Cell,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    table::CallContextFieldTag,
    util::{
        word::{Word, WordCell, WordExpr},
        Expr,
    },
};
use eth_types::{evm_types::OpcodeId, Field, ToAddress, U256};
use halo2_proofs::{circuit::Value, plonk::Error};

#[derive(Clone, Debug)]
pub(crate) struct ErrorWriteProtectionGadget<F> {
    opcode: Cell<F>,
    is_call: IsZeroGadget<F>,
    gas: WordCell<F>,
    code_address: AccountAddress<F>,
    value: WordCell<F>,
    is_value_zero: IsZeroWordGadget<F, WordCell<F>>,
    common_error_gadget: CommonErrorGadget<F>,
}

impl<F: Field> ExecutionGadget<F> for ErrorWriteProtectionGadget<F> {
    const NAME: &'static str = "ErrorWriteProtection";

    const EXECUTION_STATE: ExecutionState = ExecutionState::ErrorWriteProtection;

    fn configure(cb: &mut EVMConstraintBuilder<F>) -> Self {
        let opcode = cb.query_cell();
        let is_call = IsZeroGadget::construct(cb, opcode.expr() - OpcodeId::CALL.expr());
        let gas_word = cb.query_word_unchecked();
        let code_address = cb.query_account_address();
        let value = cb.query_word_unchecked();
        let is_value_zero = IsZeroWordGadget::construct(cb, &value);

        // require_in_set method will spilit into more low degree expressions if exceed
        // max_degree. otherwise need to do fixed lookup for these opcodes
        // checking.
        cb.require_in_set(
            "ErrorWriteProtection only happens in [CALL, SSTORE, CREATE, CREATE2, SELFDESTRUCT, LOG0..4 ]",
            opcode.expr(),
            vec![
                OpcodeId::CALL.expr(),
                OpcodeId::SSTORE.expr(),
                OpcodeId::CREATE.expr(),
                OpcodeId::CREATE2.expr(),
                OpcodeId::SELFDESTRUCT.expr(),
                OpcodeId::LOG0.expr(),
                OpcodeId::LOG1.expr(),
                OpcodeId::LOG2.expr(),
                OpcodeId::LOG3.expr(),
                OpcodeId::LOG4.expr(),
            ],
        );

        // Lookup values from stack if opcode is call
        // Precondition: If there's a StackUnderflow CALL, is handled before this error
        cb.condition(is_call.expr(), |cb| {
            cb.stack_pop(gas_word.to_word());
            cb.stack_pop(code_address.to_word());
            cb.stack_pop(value.to_word());
            cb.require_zero("value of call is not zero", is_value_zero.expr());
        });

        // current call context is readonly
        cb.call_context_lookup_read(None, CallContextFieldTag::IsStatic, Word::one());

        // constrain not root call as at least one previous staticcall preset.
        cb.require_zero(
            "ErrorWriteProtection only happen in internal call",
            cb.curr.state.is_root.expr(),
        );

        let common_error_gadget = CommonErrorGadget::construct(cb, opcode.expr(), 0.expr());

        Self {
            opcode,
            is_call,
            gas: gas_word,
            code_address,
            value,
            is_value_zero,
            common_error_gadget,
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
        let opcode = step.opcode().unwrap();
        let is_call = opcode == OpcodeId::CALL;
        self.opcode
            .assign(region, offset, Value::known(F::from(opcode.as_u64())))?;
        let [mut gas, mut code_address, mut value] = [U256::zero(), U256::zero(), U256::zero()];

        if is_call {
            [gas, code_address, value] =
                [0, 1, 2].map(|index| block.get_rws(step, index).stack_value());
        }

        self.gas.assign_u256(region, offset, gas)?;
        self.code_address
            .assign_h160(region, offset, code_address.to_address())?;
        self.value.assign_u256(region, offset, value)?;

        self.is_call.assign(
            region,
            offset,
            F::from(opcode.as_u64()) - F::from(OpcodeId::CALL.as_u64()),
        )?;
        self.is_value_zero
            .assign(region, offset, Word::from(value))?;

        self.common_error_gadget.assign(
            region,
            offset,
            block,
            call,
            step,
            3 + (is_call as usize * 3),
        )?;

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::test_util::CircuitTestBuilder;
    use eth_types::{
        address, bytecode, bytecode::Bytecode, geth_types::Account, Address, ToWord, Word, U64,
    };
    use mock::TestContext;

    fn callee(code: Bytecode) -> Account {
        let code = code.code_vec();
        let is_empty = code.is_empty();

        Account {
            address: Address::repeat_byte(0xff),
            code: code.into(),
            nonce: U64::from(!is_empty as u64),
            balance: if is_empty { 0 } else { 0xdeadbeefu64 }.into(),
            ..Default::default()
        }
    }

    #[test]
    fn test_write_protection() {
        // test sstore with write protection error
        test_internal_write_protection(false);
        // test call with write protection error
        test_internal_write_protection(true);
    }

    // ErrorWriteProtection error happen in internal call
    fn test_internal_write_protection(is_call: bool) {
        let mut caller_bytecode = bytecode! {
            PUSH1(0)
            PUSH1(0)
            PUSH1(0)
            PUSH1(0)
            //PUSH1(100) //skip value for static call
        };

        caller_bytecode.append(&bytecode! {
            PUSH32(Address::repeat_byte(0xff).to_word())
            PUSH2(40000) // gas
            STATICCALL //CALL
            STOP
        });

        let mut callee_bytecode = bytecode! {
            PUSH1(42)
            PUSH1(0x02)
        };

        if is_call {
            callee_bytecode.append(&bytecode! {
                PUSH1(0)
                PUSH1(0)
                PUSH1(10)
                PUSH1(200)  // non zero value
                PUSH20(Address::repeat_byte(0xff).to_word())
                PUSH2(10000)  // gas
                //this call got error: ErrorWriteProtection
                CALL
                RETURN
                STOP
            });
        } else {
            callee_bytecode.append(&bytecode! {
                // this SSTORE got error: ErrorWriteProtection
                SSTORE
                STOP
            });
        }

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
        let ctx = TestContext::<3, 1>::new(
            None,
            |accs| {
                accs[0]
                    .address(address!("0x000000000000000000000000000000000000cafe"))
                    .balance(Word::from(10u64.pow(19)));
                accs[1].account(&caller);
                accs[2].account(&callee);
            },
            |mut txs, accs| {
                txs[0]
                    .from(accs[0].address)
                    .to(accs[1].address)
                    .gas(150000.into());
            },
            |block, _tx| block.number(0xcafeu64),
        )
        .unwrap();

        CircuitTestBuilder::new_from_test_ctx(ctx).run();
    }
}
