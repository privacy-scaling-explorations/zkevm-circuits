use eth_types::{Address, GethExecStep, ToWord, Word};

use crate::{
    circuit_input_builder::{Call, CircuitInputStateRef, ExecStep},
    operation::CallContextField,
    precompile::PrecompileCalls,
    Error,
};

pub fn gen_associated_ops(
    state: &mut CircuitInputStateRef,
    geth_step: GethExecStep,
    call: Call,
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

    // TODO(rohit): copy event for memory bytes copied from caller to callee (call data).
    // TODO(rohit): copy event for memory bytes copied from callee to caller (return data).

    Ok(exec_step)
}
