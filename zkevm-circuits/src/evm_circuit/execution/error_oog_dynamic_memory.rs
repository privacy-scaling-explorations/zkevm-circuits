use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        param::{N_BYTES_GAS, N_BYTES_MEMORY_ADDRESS},
        step::ExecutionState,
        util::{
            common_gadget::CommonErrorGadget,
            constraint_builder::{ConstrainBuilderCommon, EVMConstraintBuilder},
            math_gadget::LtGadget,
            memory_gadget::{
                CommonMemoryAddressGadget, MemoryAddressGadget, MemoryExpansionGadget,
            },
            CachedRegion, Cell,
        },
    },
    util::word::WordExpr,
    witness::{Block, Call, ExecStep, Transaction},
};
use eth_types::{evm_types::OpcodeId, Field};
use gadgets::util::Expr;
use halo2_proofs::{circuit::Value, plonk::Error};

#[derive(Clone, Debug)]
pub(crate) struct ErrorOOGDynamicMemoryGadget<F> {
    opcode: Cell<F>,

    memory_addr: MemoryAddressGadget<F>,
    memory_expansion: MemoryExpansionGadget<F, 1, N_BYTES_MEMORY_ADDRESS>,
    insufficient_gas: LtGadget<F, N_BYTES_GAS>,
    common_error_gadget: CommonErrorGadget<F>,
}

impl<F: Field> ExecutionGadget<F> for ErrorOOGDynamicMemoryGadget<F> {
    const NAME: &'static str = "ErrorOutOfGasDynamicMemoryExpansion";
    const EXECUTION_STATE: ExecutionState = ExecutionState::ErrorOutOfGasDynamicMemoryExpansion;

    // Support other OOG due to pure memory including RETURN and REVERT
    fn configure(cb: &mut EVMConstraintBuilder<F>) -> Self {
        let opcode = cb.query_cell();

        cb.require_in_set(
            "ErrorOutOfGasDynamicMemoryExpansion opcode must be RETURN or REVERT",
            opcode.expr(),
            vec![OpcodeId::RETURN.expr(), OpcodeId::REVERT.expr()],
        );

        let offset = cb.query_word_unchecked();
        let length = cb.query_memory_address();
        cb.stack_pop(offset.to_word());
        cb.stack_pop(length.to_word());

        let memory_addr = MemoryAddressGadget::construct(cb, offset, length);
        let memory_expansion = MemoryExpansionGadget::construct(cb, [memory_addr.address()]);

        // constant gas of RETURN and REVERT is zero.
        let insufficient_gas = LtGadget::construct(
            cb,
            cb.curr.state.gas_left.expr(),
            memory_expansion.gas_cost(),
        );
        cb.require_equal(
            "gas_left must less than gas_cost",
            insufficient_gas.expr(),
            true.expr(),
        );

        let common_error_gadget =
            CommonErrorGadget::construct(cb, opcode.expr(), cb.rw_counter_offset() + 2.expr());

        Self {
            opcode,
            memory_addr,
            memory_expansion,
            insufficient_gas,
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
        self.opcode
            .assign(region, offset, Value::known(F::from(opcode.as_u64())))?;

        let memory_offset = block.get_rws(step, 0).stack_value();
        let length = block.get_rws(step, 1).stack_value();
        let expanded_address = self
            .memory_addr
            .assign(region, offset, memory_offset, length)?;
        self.memory_expansion.assign(
            region,
            offset,
            step.memory_word_size(),
            [expanded_address],
        )?;

        self.insufficient_gas.assign(
            region,
            offset,
            F::from(step.gas_left),
            F::from(step.gas_cost),
        )?;

        self.common_error_gadget.assign(
            region,
            offset,
            block,
            call,
            step,
            if opcode == OpcodeId::CREATE { 5 } else { 4 },
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::test_util::CircuitTestBuilder;
    use eth_types::{bytecode, word, Bytecode, ToWord};
    use mock::{
        eth, test_ctx::helpers::account_0_code_account_1_no_code, TestContext, MOCK_ACCOUNTS,
    };

    #[test]
    fn test() {
        let codes = [
            bytecode! {
                PUSH8(0xFF)
                PUSH32(word!("0xFFFFF")) // offset
                RETURN
            },
            bytecode! {
                PUSH8(0xFF)
                PUSH32(word!("0xFFFFF")) // offset
                REVERT
            },
        ];

        for code in codes.iter() {
            test_root(code.clone());
            test_internal(code.clone());
        }
    }

    fn test_root(code: Bytecode) {
        let ctx = TestContext::<2, 1>::new(
            None,
            account_0_code_account_1_no_code(code),
            |mut txs, accs| {
                txs[0]
                    .from(accs[1].address)
                    .to(accs[0].address)
                    .gas(word!("0xFFFFF"));
            },
            |block, _tx| block,
        )
        .unwrap();

        CircuitTestBuilder::new_from_test_ctx(ctx).run();
    }

    fn test_internal(code: Bytecode) {
        let code_a = bytecode! {
            PUSH1(0x00) // retLength
            PUSH1(0x00) // retOffset
            PUSH32(0x00) // argsLength
            PUSH32(0x00) // argsOffset
            PUSH1(0x00) // value
            PUSH32(MOCK_ACCOUNTS[1].to_word()) // addr
            PUSH32(word!("0xFFFFF")) // gas
            CALL
            STOP
        };

        let ctx = TestContext::<3, 1>::new(
            None,
            |accs| {
                accs[0].address(MOCK_ACCOUNTS[0]).code(code_a);
                accs[1].address(MOCK_ACCOUNTS[1]).code(code);
                accs[2].address(MOCK_ACCOUNTS[2]).balance(eth(1));
            },
            |mut txs, accs| {
                txs[0]
                    .from(accs[2].address)
                    .to(accs[0].address)
                    .gas(word!("0xFFFFFF"));
            },
            |block, _tx| block,
        )
        .unwrap();

        CircuitTestBuilder::new_from_test_ctx(ctx).run();
    }
}
