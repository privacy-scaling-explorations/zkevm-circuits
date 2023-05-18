use eth_types::{Address, GethExecStep, ToWord, Word};

use crate::{
    circuit_input_builder::{
        Call, CircuitInputStateRef, CopyDataType, CopyEvent, ExecStep, NumberOrHash,
    },
    operation::{CallContextField, RWCounter},
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

    for (field, value) in [
        (
            CallContextField::IsSuccess,
            Word::from(call.is_success as u64),
        ),
        (CallContextField::CalleeAddress, {
            let addr: Address = PrecompileCalls::Identity.into();
            addr.to_word()
        }),
        (CallContextField::CallerId, call.caller_id.into()),
        (
            CallContextField::CallDataOffset,
            call.call_data_offset.into(),
        ),
        (
            CallContextField::CallDataLength,
            call.call_data_length.into(),
        ),
        (
            CallContextField::ReturnDataOffset,
            call.return_data_offset.into(),
        ),
        (
            CallContextField::ReturnDataLength,
            call.return_data_length.into(),
        ),
    ] {
        state.call_context_read(&mut exec_step, call.call_id, field, value);
    }

    let rw_counter_start = state.block_ctx.rwc;
    if call.is_success && call.call_data_length > 0 {
        state.push_copy(
            &mut exec_step,
            CopyEvent {
                src_addr: call.call_data_offset,
                src_addr_end: call.call_data_offset + call.call_data_length,
                src_type: CopyDataType::Memory,
                src_id: NumberOrHash::Number(call.caller_id),
                dst_addr: 0,
                dst_type: CopyDataType::Memory,
                dst_id: NumberOrHash::Number(call.call_id),
                log_id: None,
                rw_counter_start,
                bytes: memory_bytes
                    .iter()
                    .skip(call.call_data_offset as usize)
                    .take(call.call_data_length as usize)
                    .map(|b| (*b, false))
                    .collect(),
            },
        );
    }
    if call.is_success && call.call_data_length > 0 && call.return_data_length > 0 {
        let length = std::cmp::min(call.call_data_length, call.return_data_length);
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
                rw_counter_start: RWCounter(
                    rw_counter_start.0 + (2 * call.call_data_length as usize),
                ),
                bytes: memory_bytes
                    .iter()
                    .skip(call.call_data_offset as usize)
                    .take(length as usize)
                    .map(|b| (*b, false))
                    .collect(),
            },
        );
    }

    Ok(exec_step)
}
