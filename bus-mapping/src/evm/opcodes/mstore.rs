use std::mem;

use super::Opcode;
use crate::{
    circuit_input_builder::{CircuitInputStateRef, ExecStep},
    Error,
};
use eth_types::{evm_types::MemoryAddress, GethExecStep, ToBigEndian, ToLittleEndian, Word};

/// Placeholder structure used to implement [`Opcode`] trait over it
/// corresponding to the [`OpcodeId::MSTORE`](crate::evm::OpcodeId::MSTORE)
/// `OpcodeId`.
#[derive(Debug, Copy, Clone)]
pub(crate) struct Mstore<const IS_MSTORE8: bool>;

impl<const IS_MSTORE8: bool> Opcode for Mstore<IS_MSTORE8> {
    fn gen_associated_ops(
        state: &mut CircuitInputStateRef,
        geth_steps: &[GethExecStep],
    ) -> Result<Vec<ExecStep>, Error> {
        let geth_step = &geth_steps[0];
        let mut exec_step = state.new_step(geth_step)?;
        // First stack read (offset)
        let offset = geth_step.stack.nth_last(0)?;
        let offset_pos = geth_step.stack.nth_last_filled(0);
        state.stack_read(&mut exec_step, offset_pos, offset)?;

        // Second stack read (value)
        let value = geth_step.stack.nth_last(1)?;
        let value_pos = geth_step.stack.nth_last_filled(1);
        state.stack_read(&mut exec_step, value_pos, value)?;

        // First mem write -> 32 MemoryOp generated.
        let offset_addr: MemoryAddress = offset.try_into()?;
        // TODO: get two memory words (slot, slot + 32) at address if offset != 0, otherwise get one word at slot. 
        
        let mut memory = state.call_ctx_mut()?.memory.clone();
        // expand memory size + 64 as slot 
        let minimal_length = offset_addr.0 + if IS_MSTORE8 { 1  } else { 64 /* 32 */ };
        println!("minimal_length {} , IS_MSTORE8 {}, memory_length {}", minimal_length, IS_MSTORE8, memory.0.len());
        
        memory.extend_at_least(minimal_length);

        let offset_u64 = offset.as_u64();
        let shift= offset_u64 % 32;
        let slot = offset_u64 - shift;
        println!("shift {}, slot {}", shift, slot);
        // reconstruct memory with value  
        match IS_MSTORE8 {
            true => {
                //let bytes=  *value.to_le_bytes().to_vec();
                let val = *value.to_le_bytes().first().unwrap();
                let word_v8= Word::from(val as u64);
                memory.0[offset_u64 as usize] = val;
            }
            false => {
                let bytes = value.to_be_bytes();
                memory[offset_u64 as usize..offset_u64 as usize + 32].copy_from_slice(&bytes);
            }
        }

        // after memory construction, we can get slot_Word(left_Word), right_word to fill buss mapping. 
        let mut slot_bytes: [u8; 32] = [0; 32];
        let mut addr_left_Word = Word::zero();

        if IS_MSTORE8 {
            let byte = *value.to_le_bytes().first().unwrap();
            addr_left_Word = Word::from(byte as u64);
        }else {
            slot_bytes.clone_from_slice(&memory.0[(slot as usize)..(slot as usize + 32)]);
            addr_left_Word = Word::from_big_endian(&slot_bytes);
        }

        // TODO: edge case: if shift = 0, no need to right word
        let mut word_right_bytes: [u8; 32] = [0; 32];
        let cur_memory_size = memory.0.len();
        // when is_msotre8, skip word_right as mstore8 only affect one word.
        if !IS_MSTORE8 { 
            slot_bytes.clone_from_slice(&memory.0[(slot as usize + 32)..cur_memory_size]);
        }
      
        // construct right word
        let addr_right_Word = Word::from_big_endian(&word_right_bytes);

        // address = 100, slot = 96 shift = 4
        // value = address + 32 = 132
        // left word = slot ( 96...96+32 bytes) slot = 128...128+32 word(fill 0)
        match IS_MSTORE8 {
            true => {
                // memory write operation for mstore8
                state.memory_write_word(
                    &mut exec_step,
                    slot.into(),
                    addr_left_Word,
                )?;
            }
            false => {
                // lookup left word
                state.memory_write_word(
                    &mut exec_step,
                    slot.into(),
                    addr_left_Word,
                )?;
                // look up right word
                state.memory_write_word(
                    &mut exec_step,
                    (slot + 32).into(),
                    addr_right_Word,
                )?;
            }
        }

        // reconstruction
        let offset = geth_step.stack.nth_last(0)?;
        let value = geth_step.stack.nth_last(1)?;
        let offset_addr: MemoryAddress = offset.try_into()?;

        let minimal_length = offset_addr.0 + if IS_MSTORE8 { 1 } else { 32 };
        state.call_ctx_mut()?.memory.extend_at_least(minimal_length);

        let mem_starts = offset_addr.0;

        match IS_MSTORE8 {
            true => {
                let val = *value.to_le_bytes().first().unwrap();
                state.call_ctx_mut()?.memory.0[mem_starts] = val;
            }
            false => {
                let bytes = value.to_be_bytes();
                state.call_ctx_mut()?.memory[mem_starts..mem_starts + 32].copy_from_slice(&bytes);
            }
        }

        println!("after mstore memory length {}", state.call_ctx_mut()?.memory.0.len());
        Ok(vec![exec_step])
    }
}

#[cfg(test)]
mod mstore_tests {
    use super::*;
    use crate::{
        circuit_input_builder::ExecState,
        mock::BlockData,
        operation::{MemoryOp, StackOp, RW, MemoryWordOp},
    };
    use eth_types::{
        bytecode,
        evm_types::{MemoryAddress, OpcodeId, StackAddress},
        geth_types::GethData,
        Word, U256,
    };
    use itertools::Itertools;
    use mock::test_ctx::{helpers::*, TestContext};
    use pretty_assertions::assert_eq;

    #[test]
    fn mstore_opcode_impl() {
        let code = bytecode! {
            .setup_state()
            PUSH2(0x1234)
            PUSH2(0x100)
            MSTORE
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
            .filter(|step| step.exec_state == ExecState::Op(OpcodeId::MSTORE))
            .nth(1)
            .unwrap();

        assert_eq!(
            [0, 1]
                .map(|idx| &builder.block.container.stack[step.bus_mapping_instance[idx].as_usize()])
                .map(|operation| (operation.rw(), operation.op())),
            [
                (
                    RW::READ,
                    &StackOp::new(1, StackAddress::from(1022u32), Word::from(0x100u64))
                ),
                (
                    RW::READ,
                    &StackOp::new(1, StackAddress::from(1023u32), Word::from(0x1234u64))
                )
            ]
        );

        let shift =  0x100 % 32;
        let slot = 0x100 - shift;
        assert_eq!(
            (2..4)
                .map(|idx| &builder.block.container.memory_word
                    [step.bus_mapping_instance[idx].as_usize()])
                .map(|operation| (operation.rw(), operation.op().clone()))
                .collect_vec(),
                vec![(
                    RW::WRITE,
                    MemoryWordOp::new(1, MemoryAddress(slot), Word::from(0x1234u64))
                ), 
                (
                    RW::WRITE,
                    MemoryWordOp::new(1, MemoryAddress(slot + 32), Word::from(0x00))
                ),
                ]
        )
    }

    #[test]
    fn mstore8_opcode_impl() {
        let code = bytecode! {
            .setup_state()
            PUSH2(0x1234)
            PUSH2(0x100)
            MSTORE8
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
            .find(|step| step.exec_state == ExecState::Op(OpcodeId::MSTORE8))
            .unwrap();

        assert_eq!(
            [0, 1]
                .map(|idx| &builder.block.container.stack[step.bus_mapping_instance[idx].as_usize()])
                .map(|operation| (operation.rw(), operation.op())),
            [
                (
                    RW::READ,
                    &StackOp::new(1, StackAddress::from(1022u32), Word::from(0x100u64))
                ),
                (
                    RW::READ,
                    &StackOp::new(1, StackAddress::from(1023u32), Word::from(0x1234))
                )
            ]
        );

        let shift =  0x100 % 32;
        let slot = 0x100 - shift;
        let memory_word_op = &builder.block.container.memory_word[step.bus_mapping_instance[2].as_usize()];
        assert_eq!(
            (memory_word_op.rw(), memory_word_op.op()),
            (RW::WRITE, &MemoryWordOp::new(1, MemoryAddress(slot), Word::from(0x34)))
        )
    }
}
