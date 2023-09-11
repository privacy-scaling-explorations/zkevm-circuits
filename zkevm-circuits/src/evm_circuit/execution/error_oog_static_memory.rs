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
                CommonMemoryAddressGadget, MemoryExpandedAddressGadget, MemoryExpansionGadget,
            },
            select, CachedRegion, Cell,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    util::{word::Word, Expr},
};
use eth_types::{evm_types::OpcodeId, Field, ToWord};
use gadgets::util::or;
use halo2_proofs::{circuit::Value, plonk::Error};

#[derive(Clone, Debug)]
pub(crate) struct ErrorOOGStaticMemoryGadget<F> {
    opcode: Cell<F>,
    is_mstore8: IsEqualGadget<F>,
    // Allow memory size to expand to 5 bytes, because memory address could be
    // at most 2^40 - 1, after constant division by 32, the memory word size
    // then could be at most 2^35 - 1.
    // So generic N_BYTES_MEMORY_WORD_SIZE for MemoryExpansionGadget needs to
    // be larger by 1 than normal usage (to be 5), to be able to contain
    // number up to 2^35 - 1.
    memory_expansion: MemoryExpansionGadget<F, 1, N_BYTES_MEMORY_ADDRESS>,
    memory_address: MemoryExpandedAddressGadget<F>,
    insufficient_gas: LtGadget<F, N_BYTES_GAS>,
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

        // Check if this is an MSTORE8
        let is_mstore8 = IsEqualGadget::construct(cb, opcode.expr(), OpcodeId::MSTORE8.expr());

        // pop memory_offset from stack
        let memory_address = MemoryExpandedAddressGadget::construct_self(cb);
        cb.stack_pop(memory_address.offset_word());

        // Get the next memory size, 1 byte if opcode is MSTORE8, otherwise 32 bytes
        cb.require_equal_word(
            "Memory length must be 32 for MLOAD and MSTORE, and 1 for MSTORE8",
            memory_address.length_word(),
            Word::from_lo_unchecked(select::expr(is_mstore8.expr(), 1.expr(), 32.expr())),
        );

        let memory_expansion = MemoryExpansionGadget::construct(cb, [memory_address.address()]);

        // Check if the amount of gas available is less than the amount of gas required
        // constant gas of MSTORE, MSTORE8 and MLOAD are the same
        let insufficient_gas = LtGadget::construct(
            cb,
            cb.curr.state.gas_left.expr(),
            OpcodeId::MLOAD.constant_gas_cost().expr() + memory_expansion.gas_cost(),
        );

        cb.require_equal(
            "Memory address is overflow or gas left is less than required",
            or::expr([memory_address.overflow(), insufficient_gas.expr()]),
            1.expr(),
        );

        let common_error_gadget =
            CommonErrorGadget::construct(cb, opcode.expr(), cb.rw_counter_offset());

        Self {
            opcode,
            memory_address,
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
            .memory_address
            .assign(region, offset, memory_offset, length)?;
        let (_, memory_expansion_gas) = self.memory_expansion.assign(
            region,
            offset,
            step.memory_word_size(),
            [expanded_address],
        )?;

        // Gas insufficient check
        let const_gas = opcode.constant_gas_cost();
        self.insufficient_gas.assign(
            region,
            offset,
            F::from(step.gas_left),
            F::from(memory_expansion_gas + const_gas),
        )?;

        self.common_error_gadget
            .assign(region, offset, block, call, step, 3)?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::test_util::CircuitTestBuilder;
    use eth_types::{bytecode, word, Bytecode, ToWord, U256};
    use mock::{
        eth, test_ctx::helpers::account_0_code_account_1_no_code, TestContext, MOCK_ACCOUNTS,
    };

    #[test]
    fn test_oog_static_memory_simple() {
        for code in testing_bytecodes(0x40_u64.into()).iter() {
            test_root(code);
            test_internal(code);
        }
    }

    #[test]
    fn test_oog_static_memory_max_expanded_address() {
        // > MAX_EXPANDED_MEMORY_ADDRESS (0x1fffffffe0)
        for code in testing_bytecodes(0x1fffffffe1_u64.into()).iter() {
            test_root(code);
            test_internal(code);
        }
    }

    #[test]
    fn test_oog_static_memory_max_u64_address() {
        for code in testing_bytecodes(u64::MAX.into()).iter() {
            test_root(code);
            test_internal(code);
        }
    }

    #[test]
    fn test_oog_static_memory_max_word_address() {
        for code in testing_bytecodes(U256::MAX).iter() {
            test_root(code);
            test_internal(code);
        }
    }

    fn testing_bytecodes(offset: U256) -> Vec<Bytecode> {
        vec![
            bytecode! {
                PUSH8(0x14)
                PUSH32(offset)
                MSTORE
                STOP
            },
            bytecode! {
                PUSH8(0x14)
                PUSH32(offset)
                MSTORE8
                STOP
            },
            bytecode! {
                PUSH32(offset)
                MLOAD
                STOP
            },
        ]
    }
    fn test_root(code: &Bytecode) {
        let ctx = TestContext::<2, 1>::new(
            None,
            account_0_code_account_1_no_code(code.clone()),
            |mut txs, accs| {
                txs[0]
                    .from(accs[1].address)
                    .to(accs[0].address)
                    .gas(21010.into());
            },
            |block, _tx| block,
        )
        .unwrap();

        CircuitTestBuilder::new_from_test_ctx(ctx).run();
    }

    fn test_internal(code: &Bytecode) {
        let code_a = bytecode! {
            PUSH1(0x00) // retLength
            PUSH1(0x00) // retOffset
            PUSH32(0x00) // argsLength
            PUSH32(0x00) // argsOffset
            PUSH1(0x00) // value
            PUSH32(MOCK_ACCOUNTS[1].to_word()) // addr
            PUSH32(0xA) // gas
            CALL
            STOP
        };

        let ctx = TestContext::<3, 1>::new(
            None,
            |accs| {
                accs[0].address(MOCK_ACCOUNTS[0]).code(code_a);
                accs[1].address(MOCK_ACCOUNTS[1]).code(code.clone());
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
