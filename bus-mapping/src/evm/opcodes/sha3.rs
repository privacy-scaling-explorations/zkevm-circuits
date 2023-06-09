use super::Opcode;
use crate::{
    circuit_input_builder::{
        CircuitInputStateRef, CircuitsParams, CopyDataType, CopyEvent, ExecStep, NumberOrHash,
    },
    Error,
};
use eth_types::{GethExecStep, U256};
use ethers_core::utils::keccak256;

#[derive(Clone, Copy, Debug)]
pub(crate) struct Sha3;

impl Opcode for Sha3 {
    fn gen_associated_ops<C: CircuitsParams>(
        state: &mut CircuitInputStateRef<C>,
        geth_steps: &[GethExecStep],
    ) -> Result<Vec<ExecStep>, Error> {
        let geth_step = &geth_steps[0];
        let mut exec_step = state.new_step(geth_step)?;

        let expected_sha3 = geth_steps[1].stack.last()?;

        // byte offset in the memory.
        let offset = geth_step.stack.nth_last(0)?;
        state.stack_read(&mut exec_step, geth_step.stack.nth_last_filled(0), offset)?;

        // byte size to read in the memory.
        let size = geth_step.stack.nth_last(1)?;
        state.stack_read(&mut exec_step, geth_step.stack.nth_last_filled(1), size)?;

        if size.gt(&U256::zero()) {
            state
                .call_ctx_mut()?
                .memory
                .extend_at_least(offset.as_usize() + size.as_usize());
        }

        let memory = state
            .call_ctx()?
            .memory
            // Get low Uint64 of offset to generate copy steps. Since offset
            // could be Uint64 overflow if length is zero.
            .read_chunk(offset.low_u64().into(), size.as_usize().into());

        // keccak-256 hash of the given data in memory.
        let sha3 = keccak256(&memory);
        debug_assert_eq!(U256::from_big_endian(&sha3), expected_sha3);
        state.stack_write(
            &mut exec_step,
            geth_steps[1].stack.last_filled(),
            sha3.into(),
        )?;

        // Memory read operations
        let rw_counter_start = state.block_ctx.rwc;
        let mut steps = Vec::with_capacity(size.as_usize());
        for (i, byte) in memory.iter().enumerate() {
            // Read step
            state.memory_read(&mut exec_step, (offset.as_usize() + i).into(), *byte)?;
            steps.push((*byte, false));
        }
        state.block.sha3_inputs.push(memory);

        let call_id = state.call()?.call_id;
        state.push_copy(
            &mut exec_step,
            CopyEvent {
                src_addr: offset.low_u64(),
                src_addr_end: offset
                    .low_u64()
                    .checked_add(size.as_u64())
                    .unwrap_or(u64::MAX),
                src_type: CopyDataType::Memory,
                src_id: NumberOrHash::Number(call_id),
                dst_addr: 0,
                dst_type: CopyDataType::RlcAcc,
                dst_id: NumberOrHash::Number(call_id),
                log_id: None,
                rw_counter_start,
                bytes: steps,
            },
        );

        Ok(vec![exec_step])
    }
}

#[cfg(test)]
pub(crate) mod sha3_tests {
    use eth_types::{evm_types::OpcodeId, geth_types::GethData, U256};
    use ethers_core::utils::keccak256;
    use mock::{
        test_ctx::helpers::{account_0_code_account_1_no_code, tx_from_1_to_0},
        Sha3CodeGen, TestContext,
    };

    use crate::{
        circuit_input_builder::ExecState,
        mock::BlockData,
        operation::{MemoryOp, StackOp, RW},
    };

    fn test_ok(mut gen: Sha3CodeGen) {
        let (code, memory) = gen.gen_sha3_code();
        let (size, offset) = (gen.size, gen.offset);
        let memory_len = memory.len();

        // The memory that is hashed.
        let mut memory_view = memory
            .into_iter()
            .skip(offset)
            .take(size)
            .collect::<Vec<u8>>();
        memory_view.resize(size, 0);
        let expected_sha3_value = keccak256(&memory_view);

        let block: GethData = TestContext::<2, 1>::new(
            None,
            account_0_code_account_1_no_code(code),
            tx_from_1_to_0,
            |block, _txs| block,
        )
        .unwrap()
        .into();

        let builder = BlockData::new_from_geth_data(block.clone()).new_circuit_input_builder();
        let builder = builder
            .handle_block(&block.eth_block, &block.geth_traces)
            .unwrap();

        let step = builder.block.txs()[0]
            .steps()
            .iter()
            .find(|step| step.exec_state == ExecState::Op(OpcodeId::SHA3))
            .unwrap();

        let call_id = builder.block.txs()[0].calls()[0].call_id;

        // stack read and write.
        assert_eq!(
            [0, 1, 2]
                .map(|idx| &builder.block.container.stack[step.bus_mapping_instance[idx].as_usize()])
                .map(|op| (op.rw(), op.op())),
            [
                (
                    RW::READ,
                    &StackOp::new(call_id, 1022.into(), U256::from(offset)),
                ),
                (
                    RW::READ,
                    &StackOp::new(call_id, 1023.into(), U256::from(size)),
                ),
                (
                    RW::WRITE,
                    &StackOp::new(call_id, 1023.into(), expected_sha3_value.into()),
                ),
            ]
        );

        // Memory reads.
        // Initial memory_len bytes are the memory writes from MSTORE instruction, so we
        // skip them.
        assert_eq!(
            (memory_len..(memory_len + size))
                .map(|idx| &builder.block.container.memory[idx])
                .map(|op| (op.rw(), op.op().clone()))
                .collect::<Vec<(RW, MemoryOp)>>(),
            {
                let mut memory_ops = Vec::with_capacity(size);
                (0..size).for_each(|idx| {
                    let value = memory_view[idx];
                    memory_ops.push((
                        RW::READ,
                        MemoryOp::new(call_id, (offset + idx).into(), value),
                    ));
                });
                memory_ops
            },
        );

        let copy_events = builder.block.copy_events.clone();

        // single copy event with `size` reads and `size` writes.
        assert_eq!(copy_events.len(), 1);
        assert_eq!(copy_events[0].bytes.len(), size);

        for (idx, (value, is_code)) in copy_events[0].bytes.iter().enumerate() {
            assert_eq!(Some(value), memory_view.get(idx));
            assert!(!is_code);
        }
    }

    #[test]
    fn sha3_opcode_ok() {
        test_ok(Sha3CodeGen::mem_empty(0x10, 0x32));
        test_ok(Sha3CodeGen::mem_lt_size(0x34, 0x44));
        test_ok(Sha3CodeGen::mem_eq_size(0x222, 0x111));
        test_ok(Sha3CodeGen::mem_gt_size(0x20, 0x30));
    }
}
