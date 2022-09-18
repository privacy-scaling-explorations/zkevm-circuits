use super::Opcode;
use crate::circuit_input_builder::{CircuitInputStateRef, ExecStep, CopyEvent, CopyDataType, NumberOrHash};
use crate::operation::{TxAccessListAccountOp, RW, MemoryOp};
use crate::Error;
use eth_types::{GethExecStep, ToAddress};

#[derive(Clone, Copy, Debug)]
pub(crate) struct Extcodecopy;

// TODO: Update to treat code_hash == 0 as account not_exists once the circuit
// is implemented https://github.com/privacy-scaling-explorations/zkevm-circuits/pull/720

impl Opcode for Extcodecopy {
    fn gen_associated_ops(
        state: &mut CircuitInputStateRef,
        geth_steps: &[GethExecStep],
    ) -> Result<Vec<ExecStep>, Error> {
        let geth_step = &geth_steps[0];
        let exec_steps = vec![gen_extcodecopy_step(state, geth_step)?];

        // reconstruction
        let address = geth_steps[0].stack.nth_last(0)?.to_address();
        let dest_offset = geth_steps[0].stack.nth_last(1)?.as_u64();
        let code_offset = geth_steps[0].stack.nth_last(2)?.as_u64();
        let length = geth_steps[0].stack.nth_last(3)?.as_u64();

        let (exist, account) = state.sdb.get_account(&address);
        assert!(exist, "target account does not exist");
        let code = state.code(account.code_hash)?;

        let call_ctx = state.call_ctx_mut()?;
        let memory = &mut call_ctx.memory;
        if length != 0 {
            let minimal_length = (dest_offset + length) as usize;
            memory.extend_at_least(minimal_length);

            let mem_starts = dest_offset as usize;
            let mem_ends = mem_starts + length as usize;
            let code_starts = code_offset as usize;
            let code_ends = code_starts + length as usize;
            if code_ends <= code.len() {
                memory[mem_starts..mem_ends].copy_from_slice(&code[code_starts..code_ends]);
            } else if let Some(actual_length) = code.len().checked_sub(code_starts) {
                let mem_code_ends = mem_starts + actual_length;
                memory[mem_starts..mem_code_ends].copy_from_slice(&code[code_starts..]);
                // since we already resize the memory, no need to copy 0s for
                // out of bound bytes
            }
        }

        let copy_event = gen_copy_event(state, geth_step)?;
        state.push_copy(copy_event);
        Ok(exec_steps)
    }
}

fn gen_extcodecopy_step(
    state: &mut CircuitInputStateRef,
    geth_step: &GethExecStep,
) -> Result<ExecStep, Error> {
    let mut exec_step = state.new_step(geth_step)?;

    let address = geth_step.stack.nth_last(0)?;
    let dest_offset = geth_step.stack.nth_last(1)?;
    let offset = geth_step.stack.nth_last(2)?;
    let length = geth_step.stack.nth_last(3)?;

    let is_warm = state
        .sdb
        .check_account_in_access_list(&address.to_address());
    state.push_op_reversible(
        &mut exec_step,
        RW::WRITE,
        TxAccessListAccountOp {
            tx_id: state.tx_ctx.id(),
            address: address.to_address(),
            is_warm: true,
            is_warm_prev: is_warm,
        },
    )?;

    // stack reads
    state.stack_read(&mut exec_step, geth_step.stack.nth_last_filled(0), address)?;
    state.stack_read(
        &mut exec_step,
        geth_step.stack.nth_last_filled(1),
        dest_offset,
    )?;
    state.stack_read(&mut exec_step, geth_step.stack.nth_last_filled(2), offset)?;
    state.stack_read(&mut exec_step, geth_step.stack.nth_last_filled(3), length)?;
    Ok(exec_step)
}

fn gen_copy_steps(
    state: &mut CircuitInputStateRef,
    exec_step: &mut ExecStep,
    src_addr: u64,
    dst_addr: u64,
    src_addr_end: u64,
    bytes_left: u64,
    code: Vec<u8>,
) -> Result<Vec<(u8, bool)>, Error> {
    let mut copy_steps = Vec::with_capacity(bytes_left as usize);
    for idx in 0..bytes_left {
        let addr = src_addr + idx;
        let value = if addr < src_addr_end {
            let byte = code[addr as usize];
            state.push_op(exec_step,
                RW::READ,
                MemoryOp::new(state.call()?.caller_id, addr.into(), byte)
            );
            byte
        } else {
            0
        };
        copy_steps.push((value, false));
        state.memory_write(exec_step, (dst_addr + idx).into(), value)?;
    }

    Ok(copy_steps)
}

fn gen_copy_event(
    state: &mut CircuitInputStateRef,
    geth_step: &GethExecStep,
) -> Result<CopyEvent, Error> {
    let rw_counter_start = state.block_ctx.rwc;
    let external_address = geth_step.stack.nth_last(0)?.to_address();
    let memory_offset = geth_step.stack.nth_last(1)?.as_u64();
    let data_offset = geth_step.stack.nth_last(2)?.as_u64();
    let length = geth_step.stack.nth_last(3)?.as_u64();
    
    let mut exec_step = gen_extcodecopy_step(state, geth_step)?;
    let code_hash = state.sdb.get_account(&external_address).1.code_hash;
    let code = state.code(code_hash)?;
    let src_addr_end = code.len() as u64;
    let copy_steps = gen_copy_steps(
        state,
        &mut exec_step,
        data_offset,
        memory_offset,
        src_addr_end,
        length,
        code
    )?;
    Ok(CopyEvent { 
        src_addr: data_offset,
        src_addr_end,
        src_type: CopyDataType::Bytecode,
        src_id: NumberOrHash::Hash(code_hash),
        dst_addr: memory_offset,
        dst_type: CopyDataType::Memory,
        dst_id: NumberOrHash::Number(state.call()?.call_id),
        log_id: None,
        rw_counter_start,
        bytes: copy_steps
    })
}

#[cfg(test)]
mod extcodecopy_tests {
    use crate::mock::BlockData;
    use eth_types::geth_types::GethData;
    use eth_types::{bytecode, word};
    use mock::test_ctx::helpers::{account_0_code_account_1_no_code, tx_from_1_to_0};
    use mock::TestContext;

    #[test]
    fn test_ok() {
        // // deployed contract
        // PUSH1 0x20
        // PUSH1 0
        // PUSH1 0
        // CALLDATACOPY
        // PUSH1 0x20
        // PUSH1 0
        // RETURN
        //
        // bytecode: 0x6020600060003760206000F3
        //
        // // constructor
        // PUSH12 0x6020600060003760206000F3
        // PUSH1 0
        // MSTORE
        // PUSH1 0xC
        // PUSH1 0x14
        // RETURN
        //
        // bytecode: 0x6B6020600060003760206000F3600052600C6014F3
        let code = bytecode! {
            PUSH21(word!("6B6020600060003760206000F3600052600C6014F3"))
            PUSH1(0)
            MSTORE

            PUSH1 (0x15)
            PUSH1 (0xB)
            PUSH1 (0)
            CREATE

            PUSH1 (0x20)
            PUSH1 (0x0)
            PUSH1 (0x20)
            DUP4
            EXTCODECOPY

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
    }
}
