use eth_types::GethExecStep;

use crate::{
    circuit_input_builder::{
        Call, CircuitInputStateRef, CopyDataType, CopyEvent, ExecState, ExecStep, NumberOrHash,
    },
    evm::opcodes::precompiles::common_call_ctx_reads,
    operation::{MemoryOp, RW},
    precompile::PrecompileCalls,
    Error,
};

pub fn gen_associated_ops(
    state: &mut CircuitInputStateRef,
    geth_step: GethExecStep,
    call: Call,
    memory_bytes: &[u8],
) -> Result<ExecStep, Error> {
    assert_eq!(call.code_address(), Some(PrecompileCalls::Identity.into()));
    let mut exec_step = state.new_step(&geth_step)?;
    exec_step.exec_state = ExecState::Precompile(PrecompileCalls::Identity);

    common_call_ctx_reads(state, &mut exec_step, &call);

    let rw_counter_start = state.block_ctx.rwc;
    if call.is_success && call.call_data_length > 0 && call.return_data_length > 0 {
        let length = std::cmp::min(call.call_data_length, call.return_data_length);
        let bytes: Vec<(u8, bool)> = memory_bytes
            .iter()
            .skip(call.call_data_offset as usize)
            .take(length as usize)
            .map(|b| (*b, false))
            .collect();
        for (i, &(byte, _is_code)) in bytes.iter().enumerate() {
            // push callee memory read
            state.push_op(
                &mut exec_step,
                RW::READ,
                MemoryOp::new(call.call_id, i.into(), byte),
            );
            // push caller memory write
            state.push_op(
                &mut exec_step,
                RW::WRITE,
                MemoryOp::new(
                    call.caller_id,
                    (call.return_data_offset + i as u64).into(),
                    byte,
                ),
            );
        }
        state.push_copy(
            &mut exec_step,
            CopyEvent {
                src_addr: 0,
                src_addr_end: call.return_data_length,
                src_type: CopyDataType::Memory,
                src_id: NumberOrHash::Number(call.call_id),
                dst_addr: call.return_data_offset,
                dst_type: CopyDataType::Memory,
                dst_id: NumberOrHash::Number(call.caller_id),
                log_id: None,
                rw_counter_start,
                bytes,
            },
        );
    }

    Ok(exec_step)
}