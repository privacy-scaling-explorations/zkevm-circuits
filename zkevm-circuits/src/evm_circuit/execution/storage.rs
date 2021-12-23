use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        step::ExecutionState,
        util::{
            common_gadget::SameContextGadget,
            constraint_builder::{
                ConstraintBuilder, StepStateTransition, Transition::Delta,
            },
            from_bytes,
            math_gadget::IsEqualGadget,
            storage_gadget::StorageExpansionGadget,
            Word,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    util::Expr,
};
use bus_mapping::{eth_types::ToLittleEndian, evm::OpcodeId};
use halo2::{arithmetic::FieldExt, circuit::Region, plonk::Error};

#[derive(Clone, Debug)]
pub(crate) struct StorageGadget<F> {
    same_context: SameContextGadget<F>,
    address: Word<F>,
    value: Word<F>,
    storage_expansion: StorageExpansionGadget<F>,
    is_sload: IsEqualGadget<F>,
}

impl<F: FieldExt> ExecutionGadget<F> for StorageGadget<F> {
    const NAME: &'static str = "STORAGE";

    const EXECUTION_STATE: ExecutionState = ExecutionState::STORAGE;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        let opcode = cb.query_cell();
        let address = cb.query_word();
        let value = cb.query_word();

        // Check if this is an SLOAD
        let is_sload =
            IsEqualGadget::construct(cb, opcode.expr(), OpcodeId::SLOAD.expr());
        // This is an SSTORE
        let is_sstore = 1.expr() - is_sload.expr();

        // Calculate the gas cost for this storage access
        let storage_expansion = StorageExpansionGadget::construct();
        let storage_gas_cost = storage_expansion.expr();

        /* Stack operations */
        // Pop the address from the stack
        cb.stack_lookup(
            false.expr(),
            cb.stack_pointer_offset().expr(),
            address.expr(),
        );
        // For SLOAD push the value to the stack
        // FOR SSTORE pop the value from the stack
        cb.stack_lookup(
            is_sload.expr(),
            cb.stack_pointer_offset().expr() + 1.expr() - is_sload.expr(),
            value.expr(),
        );

        /* Storage operations */
        // Read/Write the value from storage at the specified address
        for idx in 0..32 {
            // We read/write all the bytes of value at an increasing address
            // value.
            let byte = if idx == 31 {
                value.cells[0].expr()
            } else {
                value.cells[31 - idx].expr()
            };

            // We increase the offset for SLOAD and SSTORE.
            let offset = if idx == 0 { 0.expr() } else { idx.expr() };

            cb.storage_lookup_with_counter(
                cb.curr.state.rw_counter.expr()
                    + cb.rw_counter_offset().expr()
                    + offset.clone(),
                is_sstore.clone(),
                from_bytes::expr(&address.cells[0..16]),
                from_bytes::expr(&address.cells[16..32]),
                offset,
                byte,
            );
        }

        // State transition
        // - `rw_counter` needs to be increased by 34
        // - `program_counter` needs to be increased by 1
        // - `stack_pointer` needs to be increased by 2 when is_sstore,
        //   otherwise to be same
        let step_state_transition = StepStateTransition {
            rw_counter: Delta(34.expr()),
            program_counter: Delta(1.expr()),
            stack_pointer: Delta(is_sstore * 2.expr()),
            ..Default::default()
        };
        let same_context = SameContextGadget::construct(
            cb,
            opcode,
            step_state_transition,
            Some(storage_gas_cost),
        );

        Self {
            same_context,
            address,
            value,
            storage_expansion,
            is_sload,
        }
    }

    fn assign_exec_step(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        block: &Block<F>,
        _: &Transaction<F>,
        _: &Call<F>,
        step: &ExecStep,
    ) -> Result<(), Error> {
        self.same_context.assign_exec_step(region, offset, step)?;

        let opcode = step.opcode.unwrap();

        // panic!("{:?}", block);

        // Inputs/Outputs
        let [address, value] = [step.rw_indices[0], step.rw_indices[1]]
            .map(|idx| block.rws[idx].stack_value());
        self.address
            .assign(region, offset, Some(address.to_le_bytes()))?;
        self.value
            .assign(region, offset, Some(value.to_le_bytes()))?;

        // Check if this is an SLOAD
        self.is_sload.assign(
            region,
            offset,
            F::from(opcode.as_u64()),
            F::from(OpcodeId::SLOAD.as_u64()),
        )?;

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::evm_circuit::{
        test::{rand_word, run_test_circuit_incomplete_fixed_table},
        witness,
    };
    use bus_mapping::{
        bytecode,
        eth_types::Word,
        evm::{Gas, GasCost, OpcodeId},
    };
    use std::iter;

    fn test_ok(
        opcode: OpcodeId,
        address: Word,
        value: Word,
        _memory_size: u64,
        gas_cost: u64,
    ) {
        let bytecode = bytecode! {
            PUSH32(value)
            PUSH32(address)
            #[start]
            .write_op(opcode)
            STOP
        };

        let gas = Gas(gas_cost + 100_000); // add extra gas for the pushes
        let mut block_trace =
            bus_mapping::mock::BlockData::new_single_tx_trace_code_gas(
                &bytecode, gas,
            )
            .unwrap();
        block_trace.geth_trace.struct_logs = block_trace.geth_trace.struct_logs
            [bytecode.get_pos("start")..]
            .to_vec();
        let mut builder = block_trace.new_circuit_input_builder();
        builder
            .handle_tx(&block_trace.eth_tx, &block_trace.geth_trace)
            .unwrap();
        let block = witness::block_convert(&bytecode, &builder.block);
        assert_eq!(run_test_circuit_incomplete_fixed_table(block), Ok(()));
    }

    #[test]
    fn storage_gadget_simple() {
        // test_ok(
        //     OpcodeId::MSTORE,
        //     Word::from(0x12FFFF),
        //     Word::from_big_endian(&(1..33).collect::<Vec<_>>()),
        //     38913,
        //     3074206,
        // );

        test_ok(
            OpcodeId::SLOAD,
            Word::from(0x12),
            Word::from_big_endian(&(1..33).collect::<Vec<_>>()),
            38913,
            3074206,
        );
        // test_ok(
        //     OpcodeId::MLOAD,
        //     Word::from(0x12FFFF) + 16,
        //     Word::from_big_endian(
        //         &(17..33).chain(iter::repeat(0).take(16)).collect::<Vec<_>>(),
        //     ),
        //     38914,
        //     3074361,
        // );
        // test_ok(
        //     OpcodeId::MSTORE8,
        //     Word::from(0x12FFFF),
        //     Word::from_big_endian(&(1..33).collect::<Vec<_>>()),
        //     38912,
        //     3074051,
        // );
    }

    #[test]
    fn storage_gadget_rand() {
        let calc_memory_size_and_gas_cost = |opcode, address: Word| {
            let memory_size = (address.as_u64()
                + match opcode {
                    OpcodeId::MSTORE | OpcodeId::MLOAD => 32,
                    OpcodeId::MSTORE8 => 1,
                    _ => 0,
                }
                + 31)
                / 32;
            let gas_cost = memory_size * memory_size / 512
                + 3 * memory_size
                + GasCost::FASTEST.as_u64();
            (memory_size, gas_cost)
        };

        for opcode in [OpcodeId::MSTORE, OpcodeId::MLOAD, OpcodeId::MSTORE8] {
            // we use 15-bit here to reduce testing resource consumption.
            // In real cases the address is 5 bytes (40 bits)
            let max_memory_size_pow_of_two = 15;
            let address = rand_word() % (1u64 << max_memory_size_pow_of_two);
            let value = rand_word();
            let (memory_size, gas_cost) =
                calc_memory_size_and_gas_cost(opcode, address);
            test_ok(opcode, address, value, memory_size, gas_cost);
        }
    }
}
