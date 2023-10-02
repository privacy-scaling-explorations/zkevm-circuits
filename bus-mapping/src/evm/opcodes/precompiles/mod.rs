use eth_types::{GethExecStep, ToWord, Word};

use crate::{
    circuit_input_builder::{Call, CircuitInputStateRef, ExecState, ExecStep},
    operation::CallContextField,
    precompile::PrecompileCalls,
    Error,
};

type InOutRetData = (Option<Vec<u8>>, Option<Vec<u8>>, Option<Vec<u8>>);

pub fn gen_associated_ops(
    state: &mut CircuitInputStateRef,
    geth_step: GethExecStep,
    call: Call,
    precompile: PrecompileCalls,
    (input_bytes, output_bytes, _returned_bytes): InOutRetData,
) -> Result<ExecStep, Error> {
    assert_eq!(call.code_address(), Some(precompile.into()));
    let mut exec_step = state.new_step(&geth_step)?;
    exec_step.exec_state = ExecState::Precompile(precompile);

    common_call_ctx_reads(state, &mut exec_step, &call)?;

    // TODO: Other precompiles carry PrecompileEvent and PrecompileAuxData.
    // Since identity doesn't have this mechanism, this part is left out.
    // let (opt_event, aux_data) = match precompile {
    //     // match more precompiles to capture precompile events and aux data
    //     PrecompileCalls::Identity => (None, None),
    //     _ => {
    //         log::warn!("precompile {:?} unsupported in circuits", precompile);
    //         (None, None)
    //     }
    // };
    // if let Some(event) = opt_event {
    //     state.push_precompile_event(event);
    // }
    // exec_step.aux_data = aux_data;

    Ok(exec_step)
}

fn common_call_ctx_reads(state: &mut CircuitInputStateRef, exec_step: &mut ExecStep, call: &Call)  -> Result<(), Error> {
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

    Ok(())
}
