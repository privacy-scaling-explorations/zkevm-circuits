use super::Opcode;
use crate::{
    circuit_input_builder::{CircuitInputStateRef, ExecStep},
    Error,
};
use eth_types::{evm_types::MemoryAddress, GethExecStep, ToBigEndian, Word};

/// Placeholder structure used to implement [`Opcode`] trait over it
/// corresponding to the [`OpcodeId::MLOAD`](crate::evm::OpcodeId::MLOAD)
/// `OpcodeId`. This is responsible of generating all of the associated
/// [`crate::operation::StackOp`]s and [`crate::operation::MemoryOp`]s and place
/// them inside the trace's [`crate::operation::OperationContainer`].
#[derive(Debug, Copy, Clone)]
pub(crate) struct Mload;

impl Opcode for Mload {
    fn gen_associated_ops(
        state: &mut CircuitInputStateRef,
        geth_steps: &[GethExecStep],
    ) -> Result<Vec<ExecStep>, Error> {
        let geth_step = &geth_steps[0];
        let mut exec_step = state.new_step(geth_step)?;
        // First stack read
        //
        let stack_value_read = geth_step.stack.last()?;
        let stack_position = geth_step.stack.last_filled();

        // Manage first stack read at latest stack position
        state.stack_read(&mut exec_step, stack_position, stack_value_read)?;

        // Read the memory
        let mut mem_read_addr: MemoryAddress = stack_value_read.try_into()?;
        // Accesses to memory that hasn't been initialized are valid, and return
        // 0.
        let mem_read_value = geth_steps[1].stack.last()?;

        // TODO: get two memory words (slot, slot + 32) at address if offset != 0, otherwise get one word at slot. 
        let mut memory = state.call_ctx_mut()?.memory.clone();
        println!("before mload memory length is {}", memory.0.len());

        let offset = stack_value_read.as_u64();
        // expand to offset + 64 to enusre addr_right_Word without out of boundary
        let minimal_length = offset + 64;

        
        memory.extend_at_least(minimal_length as usize);

        let shift= offset % 32;
        let slot = offset - shift;
        println!("minimal_length {} , slot {},  shift {}, memory_length {}", minimal_length, slot, shift, memory.0.len());


        let mut slot_bytes: [u8; 32] = [0; 32];
        slot_bytes.clone_from_slice(&memory.0[(slot as usize)..(slot as usize + 32)]);

        let addr_left_Word = Word::from_big_endian(&slot_bytes);
        // TODO: edge case: if shift = 0, skip to read right word ?
        let mut word_right_bytes: [u8; 32] = [0; 32];
        slot_bytes.clone_from_slice(&memory.0[(slot + 32) as usize..(slot + 64) as usize]);

        
        let addr_right_Word = Word::from_little_endian(&word_right_bytes);

        // First stack write
        //
        state.stack_write(&mut exec_step, stack_position, mem_read_value)?;

        // First mem read -> 32 MemoryOp generated.
        state.memory_read_word(&mut exec_step, slot.into(), addr_left_Word)?;
        state.memory_read_word(&mut exec_step, (slot + 32).into(), addr_right_Word)?;

        // reconstruction
        // "minimal_length - 32" subtract 32 as actual expansion size
         state.call_ctx_mut()?.memory.extend_at_least((minimal_length - 32) as usize);

        Ok(vec![exec_step])
    }
}

#[cfg(test)]
mod mload_tests {
    use super::*;
    use crate::{
        circuit_input_builder::ExecState,
        mock::BlockData,
        operation::{MemoryOp, MemoryWordOp, StackOp, RW},
    };
    use eth_types::{
        bytecode,
        evm_types::{OpcodeId, StackAddress},
        geth_types::GethData,
        Word,
    };
    use itertools::Itertools;
    use mock::test_ctx::{helpers::*, TestContext};
    use pretty_assertions::assert_eq;

    #[test]
    fn mload_opcode_impl() {
        let code = bytecode! {
            .setup_state()

            PUSH1(0x40u64)
            MLOAD
            STOP
        };

        // Get the execution steps from the external tracer
        let block: GethData = TestContext::<2, 1>::new(
            None,
            account_0_code_account_1_no_code(code),
            tx_from_1_to_0,
            |block, _tx| block.number(0xcafeu64),
        )
        .unwrap()
        .into();

        let mut builder = BlockData::new_from_geth_data(block.clone()).new_circuit_input_builder();
        builder
            .handle_block(&block.eth_block, &block.geth_traces)
            .unwrap();

        let step = builder.block.txs()[0]
            .steps()
            .iter()
            .find(|step| step.exec_state == ExecState::Op(OpcodeId::MLOAD))
            .unwrap();

        assert_eq!(
            [0, 1]
                .map(|idx| &builder.block.container.stack[step.bus_mapping_instance[idx].as_usize()])
                .map(|operation| (operation.rw(), operation.op())),
            [
                (
                    RW::READ,
                    &StackOp::new(1, StackAddress::from(1023), Word::from(0x40))
                ),
                (
                    RW::WRITE,
                    &StackOp::new(1, StackAddress::from(1023), Word::from(0x80))
                )
            ]
        );

        let shift =  0x40 % 32;
        let slot = 0x40 - shift;
        let memory_words = &builder.block.container.memory_word;
        assert_eq!(
            (2..4)
                .map(|idx| &builder.block.container.memory_word
                    [step.bus_mapping_instance[idx].as_usize()])
                .map(|operation| (operation.rw(), operation.op().clone()))
                .collect_vec(),
                vec![(
                    RW::READ,
                    MemoryWordOp::new(1, MemoryAddress(slot), Word::from(0x80u64))
                ), 
                (
                    RW::READ,
                    MemoryWordOp::new(1, MemoryAddress(slot + 32), Word::from(0x00))
                ),
                ]
        )
    
    }
}
