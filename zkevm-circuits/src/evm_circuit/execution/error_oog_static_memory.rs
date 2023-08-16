use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        param::{N_BYTES_GAS, N_BYTES_MEMORY_ADDRESS},
        step::ExecutionState,
        util::{
            common_gadget::CommonErrorGadget,
            constraint_builder::{ConstrainBuilderCommon, EVMConstraintBuilder},
            math_gadget::{IsEqualGadget, LtGadget},
            memory_gadget::{
                CommonMemoryAddressGadget, MemoryAddressGadget, MemoryExpansionGadget,
            },
            select, CachedRegion, Cell,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    util::{word::WordExpr, Expr},
};
use eth_types::{evm_types::OpcodeId, Field, ToWord};
use halo2_proofs::{circuit::Value, plonk::Error};

#[derive(Clone, Debug)]
pub(crate) struct ErrorOOGStaticMemoryGadget<F> {
    opcode: Cell<F>,
    // Allow memory size to expand to 5 bytes, because memory address could be
    // at most 2^40 - 1, after constant division by 32, the memory word size
    // then could be at most 2^35 - 1.
    // So generic N_BYTES_MEMORY_WORD_SIZE for MemoryExpansionGadget needs to
    // be larger by 1 than normal usage (to be 5), to be able to contain
    // number up to 2^35 - 1.
    memory_expansion: MemoryExpansionGadget<F, 1, N_BYTES_MEMORY_ADDRESS>,
    memory_addr: MemoryAddressGadget<F>,
    insufficient_gas: LtGadget<F, N_BYTES_GAS>,
    is_mstore8: IsEqualGadget<F>,
    common_error_gadget: CommonErrorGadget<F>,
}

impl<F: Field> ExecutionGadget<F> for ErrorOOGStaticMemoryGadget<F> {
    const NAME: &'static str = "ErrorOutOfGasStaticMemoryExpansion";

    const EXECUTION_STATE: ExecutionState = ExecutionState::ErrorOutOfGasStaticMemoryExpansion;

    // Support other OOG due to pure memory including MSTORE, MSTORE8 and MLOAD
    fn configure(cb: &mut EVMConstraintBuilder<F>) -> Self {
        let opcode = cb.query_cell();
        cb.require_in_set(
            "ErrorOutOfGasStaticMemoryExpansion opcode must be MLOAD or MSTORE or MSTORE8",
            opcode.expr(),
            vec![
                OpcodeId::MLOAD.expr(),
                OpcodeId::MSTORE8.expr(),
                OpcodeId::MSTORE.expr(),
            ],
        );

        // pop memory_offset from stack
        let memory_offset = cb.query_word_unchecked();
        cb.stack_pop(memory_offset.to_word());

        // Check if this is an MSTORE8
        let is_mstore8 = IsEqualGadget::construct(cb, opcode.expr(), OpcodeId::MSTORE8.expr());

        // Get the next memory size, 1 byte if opcode is MSTORE8, otherwise 32 bytes
        let length = cb.query_memory_address();
        cb.require_equal(
            "Memory length must be 32 for MLOAD and MSTORE, and 1 for MSTORE8",
            length.expr(),
            select::expr(is_mstore8.expr(), 1.expr(), 32.expr()),
        );

        let memory_addr = MemoryAddressGadget::construct(cb, memory_offset, length);
        let memory_expansion = MemoryExpansionGadget::construct(cb, [memory_addr.address()]);

        // Check if the amount of gas available is less than the amount of gas required
        // constant gas of MSTORE, MSTORE8 and MLOAD are the same
        let insufficient_gas = LtGadget::construct(
            cb,
            cb.curr.state.gas_left.expr(),
            OpcodeId::MLOAD.constant_gas_cost().expr() + memory_expansion.gas_cost(),
        );

        cb.require_equal(
            "gas_left must be less than gas_cost",
            insufficient_gas.expr(),
            true.expr(),
        );

        // TODO: `+2` bcs CommonErrorGadget looks up IsSuccess and RwCounterEndOfReversion,
        // ,but `+2` should be moved inside CommonErrorGadget
        let common_error_gadget =
            CommonErrorGadget::construct(cb, opcode.expr(), cb.rw_counter_offset() + 2.expr());

        Self {
            opcode,
            memory_addr,
            memory_expansion,
            insufficient_gas,
            is_mstore8,
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

        // Inputs/Outputs
        let memory_offset = block.get_rws(step, 0).stack_value();
        self.opcode
            .assign(region, offset, Value::known(F::from(opcode.as_u64())))?;
        self.is_mstore8.assign(
            region,
            offset,
            F::from(opcode.as_u64()),
            F::from(OpcodeId::MSTORE8.as_u64()),
        )?;

        let length = if opcode == OpcodeId::MSTORE8 {
            1.to_word()
        } else {
            32.to_word()
        };
        let expanded_address = self
            .memory_addr
            .assign(region, offset, memory_offset, length)?;
        self.memory_expansion.assign(
            region,
            offset,
            step.memory_word_size(),
            [expanded_address],
        )?;

        // Gas insufficient check
        // Get `gas_available` variable here once it's available
        self.insufficient_gas.assign(
            region,
            offset,
            F::from(step.gas_left),
            F::from(step.gas_cost),
        )?;

        self.common_error_gadget
            .assign(region, offset, block, call, step, 3)?;

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
                MSTORE
                STOP
            },
            bytecode! {
                PUSH8(0xFF)
                PUSH32(word!("0xFFFFF")) // offset
                MSTORE8
                STOP
            },
            bytecode! {
                PUSH32(word!("0xFFFFF")) // offset
                MLOAD
                STOP
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
                    .gas(word!("0xFFFF"));
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
            PUSH32(0xFF) // gas
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
                    .gas(word!("0xFFFF"));
            },
            |block, _tx| block,
        )
        .unwrap();

        CircuitTestBuilder::new_from_test_ctx(ctx).run();
    }
}
