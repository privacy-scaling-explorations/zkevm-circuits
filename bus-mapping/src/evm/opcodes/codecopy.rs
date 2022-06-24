use crate::{
    circuit_input_builder::{
        CircuitInputStateRef, CopyDataType, CopyEvent, CopyStep, ExecStep, NumberOrHash,
    },
    constants::MAX_COPY_BYTES,
    operation::RW,
    Error,
};
use eth_types::{Bytecode, GethExecStep};

use super::Opcode;

#[derive(Clone, Copy, Debug)]
pub(crate) struct Codecopy;

impl Opcode for Codecopy {
    fn gen_associated_ops(
        state: &mut CircuitInputStateRef,
        geth_steps: &[GethExecStep],
    ) -> Result<Vec<ExecStep>, Error> {
        let geth_step = &geth_steps[0];
        let exec_steps = vec![gen_codecopy_step(state, geth_step)?];
        let copy_event = gen_copy_event(state, geth_step)?;
        state.push_copy(copy_event);
        Ok(exec_steps)
    }
}

fn gen_codecopy_step(
    state: &mut CircuitInputStateRef,
    geth_step: &GethExecStep,
) -> Result<ExecStep, Error> {
    let mut exec_step = state.new_step(geth_step)?;

    let dest_offset = geth_step.stack.nth_last(0)?;
    let code_offset = geth_step.stack.nth_last(1)?;
    let length = geth_step.stack.nth_last(2)?;

    // stack reads
    state.stack_read(
        &mut exec_step,
        geth_step.stack.nth_last_filled(0),
        dest_offset,
    )?;
    state.stack_read(
        &mut exec_step,
        geth_step.stack.nth_last_filled(1),
        code_offset,
    )?;
    state.stack_read(&mut exec_step, geth_step.stack.nth_last_filled(2), length)?;

    Ok(exec_step)
}

fn gen_copy_steps(
    state: &mut CircuitInputStateRef,
    exec_step: &mut ExecStep,
    src_addr: u64,
    dst_addr: u64,
    bytes_left: u64,
    src_addr_end: u64,
    bytecode: &Bytecode,
) -> Result<Vec<CopyStep>, Error> {
    let cap = std::cmp::min(bytes_left as usize, MAX_COPY_BYTES);
    let mut steps = Vec::with_capacity(2 * cap);
    for idx in 0..cap {
        let addr = (src_addr as usize) + idx;
        let (value, is_code, is_pad) = if addr < (src_addr_end as usize) {
            bytecode
                .get(addr)
                .map_or((0, None, true), |e| (e.value, Some(e.is_code), false))
        } else {
            (0, None, true)
        };
        // Read
        steps.push(CopyStep {
            addr: addr as u64,
            addr_end: Some(src_addr_end),
            tag: CopyDataType::Bytecode,
            rw: RW::READ,
            value,
            is_code,
            is_pad,
            rwc: None,
        });
        // Write
        state.memory_write(exec_step, (dst_addr as usize + idx).into(), value)?;
        steps.push(CopyStep {
            addr: dst_addr + (idx as u64),
            addr_end: None,
            tag: CopyDataType::Memory,
            rw: RW::WRITE,
            value,
            is_code: None,
            is_pad: false,
            rwc: Some(state.block_ctx.rwc),
        })
    }
    Ok(steps)
}

fn gen_copy_event(
    state: &mut CircuitInputStateRef,
    geth_step: &GethExecStep,
) -> Result<CopyEvent, Error> {
    let dst_offset = geth_step.stack.nth_last(0)?.as_u64();
    let code_offset = geth_step.stack.nth_last(1)?.as_u64();
    let length = geth_step.stack.nth_last(2)?.as_u64();

    let code_hash = state.call()?.code_hash;
    let bytecode: Bytecode = state
        .code(code_hash)?
        .try_into()
        .map_err(eth_types::Error::BytecodeError)?;
    let src_addr_end = bytecode.code().len() as u64;

    let mut copied = 0;
    let mut copy_steps = vec![];
    while copied < length {
        let mut exec_step = state.new_step(geth_step)?;
        let int_copy_steps = gen_copy_steps(
            state,
            &mut exec_step,
            code_offset + copied,
            dst_offset + copied,
            length - copied,
            src_addr_end,
            &bytecode,
        )?;
        copy_steps.extend(int_copy_steps);
        copied += MAX_COPY_BYTES as u64;
    }

    Ok(CopyEvent {
        src_type: CopyDataType::Bytecode,
        src_id: NumberOrHash::Hash(code_hash),
        src_addr: code_offset,
        src_addr_end,
        dst_type: CopyDataType::Memory,
        dst_id: NumberOrHash::Number(state.call()?.call_id),
        dst_addr: dst_offset,
        log_id: None,
        length,
        steps: copy_steps,
    })
}

#[cfg(test)]
mod codecopy_tests {
    use eth_types::{
        bytecode,
        evm_types::{MemoryAddress, OpcodeId, StackAddress},
        geth_types::GethData,
        Word, H256,
    };
    use ethers_core::utils::keccak256;
    use mock::{
        test_ctx::helpers::{account_0_code_account_1_no_code, tx_from_1_to_0},
        TestContext,
    };

    use crate::{
        circuit_input_builder::{CopyDataType, CopyStep, ExecState, NumberOrHash},
        mock::BlockData,
        operation::{MemoryOp, RWCounter, StackOp, RW},
    };

    #[test]
    fn codecopy_opcode_impl() {
        test_ok(0x00, 0x00, 0x40);
        test_ok(0x20, 0x40, 0xA0);
    }

    fn test_ok(dst_offset: usize, code_offset: usize, size: usize) {
        let code = bytecode! {
            PUSH32(size)
            PUSH32(code_offset)
            PUSH32(dst_offset)
            CODECOPY
            STOP
        };

        let block: GethData = TestContext::<2, 1>::new(
            None,
            account_0_code_account_1_no_code(code.clone()),
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
            .find(|step| step.exec_state == ExecState::Op(OpcodeId::CODECOPY))
            .unwrap();

        let expected_call_id = builder.block.txs()[0].calls()[step.call_index].call_id;

        assert_eq!(
            [0, 1, 2]
                .map(|idx| &builder.block.container.stack[step.bus_mapping_instance[idx].as_usize()])
                .map(|op| (op.rw(), op.op())),
            [
                (
                    RW::READ,
                    &StackOp::new(1, StackAddress::from(1021), Word::from(dst_offset)),
                ),
                (
                    RW::READ,
                    &StackOp::new(1, StackAddress::from(1022), Word::from(code_offset)),
                ),
                (
                    RW::READ,
                    &StackOp::new(1, StackAddress::from(1023), Word::from(size)),
                ),
            ]
        );

        // RW table memory writes.
        assert_eq!(
            (0..size)
                .map(|idx| &builder.block.container.memory[idx])
                .map(|op| (op.rw(), op.op().clone()))
                .collect::<Vec<(RW, MemoryOp)>>(),
            (0..size)
                .map(|idx| {
                    (
                        RW::WRITE,
                        MemoryOp::new(
                            1,
                            MemoryAddress::from(dst_offset + idx),
                            if code_offset + idx < code.code().len() {
                                code.code()[code_offset + idx]
                            } else {
                                0
                            },
                        ),
                    )
                })
                .collect::<Vec<(RW, MemoryOp)>>(),
        );

        let copy_events = builder.block.copy_events.clone();
        assert_eq!(copy_events.len(), 1);
        assert_eq!(copy_events[0].steps.len(), 2 * size);
        assert_eq!(
            copy_events[0].src_id,
            NumberOrHash::Hash(H256(keccak256(&code.code())))
        );
        assert_eq!(copy_events[0].src_addr as usize, code_offset);
        assert_eq!(copy_events[0].src_addr_end as usize, code.code().len());
        assert_eq!(copy_events[0].src_type, CopyDataType::Bytecode);
        assert_eq!(
            copy_events[0].dst_id,
            NumberOrHash::Number(expected_call_id)
        );
        assert_eq!(copy_events[0].dst_addr as usize, dst_offset);
        assert_eq!(copy_events[0].dst_type, CopyDataType::Memory);
        assert!(copy_events[0].log_id.is_none());
        assert_eq!(copy_events[0].length as usize, size);

        let mut rwc_start = step.rwc.0 + 3;
        for (idx, copy_rw_pair) in copy_events[0].steps.chunks(2).enumerate() {
            assert_eq!(copy_rw_pair.len(), 2);
            let (value, is_code, is_pad) = code
                .get(code_offset + idx)
                .map_or((0, None, true), |e| (e.value, Some(e.is_code), false));
            // Read
            let read_step = copy_rw_pair[0].clone();
            assert_eq!(
                read_step,
                CopyStep {
                    addr: (code_offset + idx) as u64,
                    addr_end: Some(code.code().len() as u64),
                    tag: CopyDataType::Bytecode,
                    rw: RW::READ,
                    value,
                    is_code,
                    is_pad,
                    rwc: None,
                }
            );
            // Write
            let write_step = copy_rw_pair[1].clone();
            assert_eq!(
                write_step,
                CopyStep {
                    addr: (dst_offset + idx) as u64,
                    addr_end: None,
                    tag: CopyDataType::Memory,
                    rw: RW::WRITE,
                    value,
                    is_code: None,
                    is_pad: false,
                    rwc: {
                        rwc_start += 1;
                        Some(RWCounter(rwc_start))
                    },
                }
            );
        }
    }
}
