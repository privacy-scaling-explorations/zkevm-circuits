use super::Opcode;
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
        } else if !is_root && !length.is_zero() {
            // // reconstruction????
            //
            // let callee_memory = &state.call_ctx()?.memory;
            //
            // // let offset = offset.low_u64() as usize;
            // // let length = length.low_u64() as usize;
            // // let mut return_buffer = callee_memory[offset..offset + length].to_vec();
            // let mut return_data = state.call_ctx()?.return_data.clone();
            // return_buffer.resize(call.return_data_offset + call.return_data_length as usize, 0);
            //
            // let caller_memory = &mut state.caller_ctx_mut()?.memory;
            // let return_data_end = call.return_data_offset + call.return_data_length;
            // caller_memory.0[call.return_data_offset as usize ..return_data_end as usize].copy_from_slice(&return_buffer);
            //
            // handle_copy(
            //     state,
            //     &mut exec_step,
            //     Source {
            //         tag: CopyDataType::Memory,
            //         id: call.call_id,
            //         offset: offset.try_into().unwrap(),
            //         bytes: vec![],
            //     },
            //     Destination {
            //         tag: CopyDataType::Memory,
            //         id: call.caller_id,
            //         offset: call.return_data_offset,
            //         length: call.return_data_length.try_into().unwrap(),
            //     },
            // );
        }

        state.handle_return(step)?;
        Ok(vec![exec_step])
    }
}

struct Source {
    tag: CopyDataType,
    id: usize,
    offset: u64,
    bytes: Vec<u8>,
}

struct Destination {
    tag: CopyDataType,
    id: usize,
    offset: u64,
    length: usize,
}

fn handle_copy(
    state: &mut CircuitInputStateRef,
    step: &mut ExecStep,
    source: Source,
    destination: Destination,
) {
    let mut buffer: Vec<u8> = vec![0; destination.length];
    let mut rw_counters = vec![];
    for i in 0..destination.length {
        if i < source.bytes.len() {
            buffer[i] = source.bytes[i];
            state.push_op(
                step,
                RW::READ,
                MemoryOp::new(source.id, source.offset.into(), buffer[i]),
            );
        }
        let read_rw_counter = state.block_ctx.rwc;
        state.push_op(
            step,
            RW::WRITE,
            MemoryOp::new(destination.id, destination.offset.into(), buffer[i]),
        );
        let write_rw_counter = state.block_ctx.rwc;

        rw_counters.push((read_rw_counter, write_rw_counter));
    }

    dbg!(&rw_counters);
    let rw_counter_end = rw_counters.last().unwrap().1 .0;
    let mut copy_steps = vec![];
    for (byte, &(read_rw_counter, write_rw_counter)) in buffer.iter().zip(&rw_counters) {
        copy_steps.push(CopyStep {
            addr: source.offset,
            tag: source.tag,
            rw: RW::READ,
            value: *byte,
            is_code: None,
            is_pad: false,
            rwc: read_rw_counter,
            rwc_inc_left: (rw_counter_end - read_rw_counter.0).try_into().unwrap(),
        });
        copy_steps.push(CopyStep {
            addr: destination.offset,
            tag: destination.tag,
            rw: RW::WRITE,
            value: *byte,
            is_code: None,
            is_pad: false,
            rwc: write_rw_counter,
            rwc_inc_left: (rw_counter_end - write_rw_counter.0).try_into().unwrap(),
        });
    }

    state.push_copy(CopyEvent {
        src_type: CopyDataType::Memory,
        src_id: NumberOrHash::Number(source.id),
        src_addr: source.offset,
        src_addr_end: source.offset + u64::try_from(source.bytes.len()).unwrap(),
        dst_type: CopyDataType::Memory,
        dst_id: NumberOrHash::Number(destination.id),
        dst_addr: destination.offset,
        length: destination.length.try_into().unwrap(),
        log_id: None,
        steps: copy_steps,
    });
}
