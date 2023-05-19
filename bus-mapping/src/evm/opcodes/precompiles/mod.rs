use eth_types::{ToWord, Word};

use crate::{
    circuit_input_builder::{Call, CircuitInputStateRef, ExecStep},
    operation::CallContextField,
};

pub mod identity;

pub(crate) fn common_call_ctx_reads(
    state: &mut CircuitInputStateRef,
    exec_step: &mut ExecStep,
    call: &Call,
) {
    for (field, value) in [
        (
            CallContextField::IsSuccess,
            Word::from(call.is_success as u64),
        ),
        (
            CallContextField::CalleeAddress,
            call.code_address().unwrap().to_word(),
        ),
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
        state.call_context_read(exec_step, call.call_id, field, value);
    }
}
