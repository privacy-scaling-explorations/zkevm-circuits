use super::Opcode;
use crate::{
    circuit_input_builder::{
        CircuitInputStateRef, CopyDataType, CopyEvent, ExecStep, NumberOrHash,
    },
    Error,
};
use eth_types::{bytecode, Bytecode, GethExecStep, Word, U256};
use ethers_core::utils::keccak256;
use rand::{rngs::ThreadRng, Rng};

#[derive(Clone, Copy, Debug)]
pub(crate) struct Sha3;

impl Opcode for Sha3 {
    fn gen_associated_ops(
        state: &mut CircuitInputStateRef,
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
        debug_assert_eq!(Word::from_big_endian(&sha3), expected_sha3);
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

/// Generate Sha3 opcode
pub struct Sha3CodeGen {
    /// The offset
    pub offset: usize,
    /// The size
    pub size: usize,
    data_len: usize,
    rng: ThreadRng,
}
impl Sha3CodeGen {
    /// Construct with memory less than size
    pub fn mem_lt_size(offset: usize, size: usize) -> Self {
        let mut rng = rand::thread_rng();
        let data_len = offset
            + if size.gt(&0) {
                rng.gen_range(0..size)
            } else {
                0
            };
        Self {
            offset,
            size,
            data_len,
            rng,
        }
    }
    /// Construct with memory equal to size
    pub fn mem_eq_size(offset: usize, size: usize) -> Self {
        let data_len = offset + size;
        Self {
            offset,
            size,
            data_len,
            rng: rand::thread_rng(),
        }
    }
    /// Construct with memory greater than size
    pub fn mem_gt_size(offset: usize, size: usize) -> Self {
        let mut rng = rand::thread_rng();
        let data_len = offset
            + size
            + if size.gt(&0) {
                rng.gen_range(0..size)
            } else {
                0
            };
        Self {
            offset,
            size,
            data_len,
            rng,
        }
    }
    /// Construct with empty memory
    pub fn mem_empty(offset: usize, size: usize) -> Self {
        Self {
            offset,
            size,
            data_len: 0,
            rng: rand::thread_rng(),
        }
    }
    fn rand_bytes(&mut self) -> Vec<u8> {
        (0..self.data_len)
            .map(|_| self.rng.gen())
            .collect::<Vec<u8>>()
    }
    /// Generate bytecode for SHA3 opcode after having populated sufficient
    /// memory given the offset and size arguments for SHA3.
    pub fn gen_sha3_code(&mut self) -> (Bytecode, Vec<u8>) {
        let data = self.rand_bytes();
        let mut memory = Vec::with_capacity(self.data_len);

        // add opcodes to populate memory in the current context.
        let mut code = Bytecode::default();
        for (i, mem_chunk) in data.chunks(32).enumerate() {
            let mem_value = if mem_chunk.len() < 32 {
                std::iter::repeat(0u8)
                    .take(32 - mem_chunk.len())
                    .chain(mem_chunk.to_vec())
                    .collect::<Vec<u8>>()
            } else {
                mem_chunk.to_vec()
            };
            memory.extend_from_slice(&mem_value);
            code.op_mstore(32 * i, Word::from_big_endian(&mem_value));
        }
        // append SHA3 related opcodes at the tail end.
        let code_tail = bytecode! {
            PUSH32(self.size)
            PUSH32(self.offset)
            SHA3
            STOP
        };
        code.append(&code_tail);
        (code, memory)
    }
}

#[cfg(test)]
pub(crate) mod sha3_tests {
    use super::Sha3CodeGen;
    use eth_types::{evm_types::OpcodeId, geth_types::GethData, Word};
    use ethers_core::utils::keccak256;
    use mock::{
        test_ctx::helpers::{account_0_code_account_1_no_code, tx_from_1_to_0},
        TestContext,
    };

    use crate::{
        circuit_input_builder::{CircuitsParams, ExecState},
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

        let mut builder = BlockData::new_from_geth_data_with_params(
            block.clone(),
            CircuitsParams {
                max_rws: 2048,
                ..Default::default()
            },
        )
        .new_circuit_input_builder();
        builder
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
                    &StackOp::new(call_id, 1022.into(), Word::from(offset)),
                ),
                (
                    RW::READ,
                    &StackOp::new(call_id, 1023.into(), Word::from(size)),
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
