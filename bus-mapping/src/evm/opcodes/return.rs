use super::Opcode;
// use crate::circuit_input_builder::{CircuitInputStateRef, ExecStep};
use crate::circuit_input_builder::CopyEvent;
use crate::circuit_input_builder::CopyStep;
use crate::circuit_input_builder::{CopyDataType, NumberOrHash};
use crate::operation::MemoryOp;
use crate::{
    circuit_input_builder::CircuitInputStateRef,
    evm::opcodes::ExecStep,
    operation::{AccountField, CallContextField, TxAccessListAccountOp, RW},
    state_db::Account,
    Error,
};
use eth_types::{GethExecStep, ToWord};
use std::cmp::max;

#[derive(Debug, Copy, Clone)]
pub(crate) struct Return;

// rename to ReturnRevertStop?
impl Opcode for Return {
    fn gen_associated_ops(
        state: &mut CircuitInputStateRef,
        steps: &[GethExecStep],
    ) -> Result<Vec<ExecStep>, Error> {
        let step = &steps[0];
        let mut exec_step = state.new_step(step)?;

        let offset = step.stack.last()?;
        state.stack_read(&mut exec_step, step.stack.last_filled(), offset)?;

        let length = step.stack.nth_last(1)?;
        state.stack_read(&mut exec_step, step.stack.nth_last_filled(1), length)?;

        let call = *state.call()?;
        let is_root = call.is_root;
        for (field, value) in [
            (CallContextField::IsRoot, is_root.to_word()),
            (CallContextField::IsCreate, call.is_create().to_word()),
            (CallContextField::IsSuccess, call.is_success.to_word()), // done in handle stop
            (CallContextField::CallerId, call.caller_id.into()),
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

        state.call_context_read(
            &mut exec_step,
            call.call_id,
            CallContextField::IsSuccess,
            call.is_success.to_word(),
        );

        if !is_root {
            state.handle_restore_context(steps, &mut exec_step);
        }

        if call.is_create() {
        } else if !is_root {
            // if caller length > callee length, we need to fill the remaining memory with
            // 0's.
            for i in 0..10 {
                state.push_op(
                    &mut exec_step,
                    RW::WRITE,
                    MemoryOp::new(call.caller_id, copy_step.addr.into(), 0u8),
                );
            }
        }

        state.handle_return(step)?;
        Ok(vec![exec_step])
    }
}

struct CopyAddress {
    tag: CopyDataType,
    id: usize,
    offset: usize,
}

fn handle_copy(
    state: &mut CircuitInputStateRef,
    source: CopyAddress,
    destination: CopyAddress,
    values: &[u8],
) {
    let caller_offset = call.return_data_offset as usize;
    let caller_length = call.return_data_length as usize;

    let callee_offset = offset.low_u64() as usize;
    let callee_length = length.low_u64() as usize;
    let callee_address = callee_offset + callee_length;

    let mut return_buffer: Vec<u8> = vec![0; caller_length];
    for i in 0..std::cmp::min(caller_length, callee_length) {
        return_buffer[i] = step.memory.0[callee_offset + i];
    }

    let rw_counter = state.block_ctx.rwc;

    // number of copy steps is always = 2 * destination.length?
    // rw_counter increase is always source.length + destination.length?

    for (i, value) in values.iter().enumerate() {
        copy_steps.push(CopyStep {
            addr: source.offset as u64,
            tag: source.tag,
            rw: RW::READ,
            value: *value,
            is_code: None,
            is_pad: false,
            rwc: (rw_counter.0 + 2 * i).into(),
            rwc_inc_left: 2 * (length - i),
        });
        state.push_op(
            &mut exec_step,
            RW::READ,
            MemoryOp::new(source.id, source.offset.into(), *value),
        );

        copy_steps.push(CopyStep {
            addr: destination.offset as u64,
            tag: destination.tag,
            rw: RW::WRITE,
            value: *value,
            is_code: None,
            is_pad: false,
            rwc: (rw_counter.0 + 2 * i + 1).into(),
            rwc_inc_left: 2 * (length - i) - 1,
        });
        state.push_op(
            &mut exec_step,
            RW::WRITE,
            MemoryOp::new(destination.id, destination.offset.into(), *value),
        );
    }

    state.push_copy(CopyEvent {
        src_type: CopyDataType::Memory,
        src_id: NumberOrHash::Number(source.id),
        src_addr: source.offset as u64,
        src_addr_end: (source.offset + values.len()) as u64,
        dst_type: CopyDataType::Memory,
        dst_id: NumberOrHash::Number(destination.id),
        dst_addr: destination.offset as u64,
        length: values.len().try_into().unwrap(),
        log_id: None,
        steps: copy_steps,
        tx_id: state.tx_ctx.id(),
        call_id: 0, // my god why is this here????
        pc: 0.into(),
    });
}
