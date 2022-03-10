use super::Opcode;
use crate::circuit_input_builder::{CircuitInputStateRef, ExecState, ExecStep, StepAuxiliaryData};
use crate::operation::{CallContextField, CallContextOp, RWCounter, RW};
use crate::Error;
use eth_types::evm_types::{Gas, GasCost, ProgramCounter};
use eth_types::GethExecStep;
use std::collections::HashMap;

// The max number of bytes that can be copied in a step limited by the number
// of cells in a step
const MAX_COPY_BYTES: usize = 71;

#[derive(Clone, Copy, Debug)]
pub(crate) struct Calldatacopy;

impl Opcode for Calldatacopy {
    fn gen_associated_ops(
        state: &mut CircuitInputStateRef,
        exec_step: &mut ExecStep,
        steps: &[GethExecStep],
    ) -> Result<(), Error> {
        let step = &steps[0];
        let memory_offset = step.stack.nth_last(0)?;
        let data_offset = step.stack.nth_last(1)?;
        let length = step.stack.nth_last(2)?;

        state.push_stack_op(
            exec_step,
            RW::READ,
            step.stack.nth_last_filled(0),
            memory_offset,
        );
        state.push_stack_op(
            exec_step,
            RW::READ,
            step.stack.nth_last_filled(1),
            data_offset,
        );
        state.push_stack_op(exec_step, RW::READ, step.stack.nth_last_filled(2), length);
        state.push_op(
            exec_step,
            RW::READ,
            CallContextOp {
                call_id: state.call().call_id,
                field: CallContextField::TxId,
                value: state.tx_ctx.id().into(),
            },
        );

        let (memory_word_size, gas_cost) = if state.call().is_root {
            let next_memory_word_size = if length.is_zero() {
                0
            } else {
                (memory_offset.as_u64() + length.as_u64() + 31) / 32
            };

            let gas_cost = GasCost::FASTEST.as_u64()
                + calc_memory_copier_gas_cost(0, next_memory_word_size, length.as_u64());

            (next_memory_word_size, gas_cost)
        } else {
            let call_data_length = state.call().call_data_length.into();
            let call_data_offset = state.call().call_data_offset.into();
            state.push_op(
                exec_step,
                RW::READ,
                CallContextOp {
                    call_id: state.call().call_id,
                    field: CallContextField::CallDataLength,
                    value: call_data_length,
                },
            );
            state.push_op(
                exec_step,
                RW::READ,
                CallContextOp {
                    call_id: state.call().call_id,
                    field: CallContextField::CallDataOffset,
                    value: call_data_offset,
                },
            );

            let curr_memory_word_size =
                (call_data_offset.as_u64() + call_data_length.as_u64() + 31) / 32;
            let next_memory_word_size = if length.is_zero() {
                curr_memory_word_size
            } else {
                std::cmp::max(
                    curr_memory_word_size,
                    (memory_offset.as_u64() + length.as_u64() + 31) / 32,
                )
            };

            let gas_cost = GasCost::FASTEST.as_u64()
                + calc_memory_copier_gas_cost(
                    curr_memory_word_size,
                    next_memory_word_size,
                    length.as_u64(),
                );

            (curr_memory_word_size, gas_cost)
        };

        // Should we set `gas_cost` and `memory_size` here?
        exec_step.gas_cost = GasCost(gas_cost);
        exec_step.memory_size = (memory_word_size * 32) as usize;

        println!("bus-mapping - 2 - {exec_step:?}");

        Ok(())
    }

    fn gen_associated_ops_multi(
        state: &mut CircuitInputStateRef,
        next_steps: &[GethExecStep],
    ) -> Result<(), Error> {
        // Generate an ExecStep of state CALLDATACOPY.
        let mut call_data_copy_step = state.new_step(&next_steps[0]);
        Self::gen_associated_ops(state, &mut call_data_copy_step, next_steps)?;

        // Generate ExecSteps of virtual state CopyToMemory.
        let copy_to_memory_steps = gen_memory_copy_steps(state, &call_data_copy_step, next_steps)?;

        state.push_step_to_tx(call_data_copy_step);
        for s in copy_to_memory_steps {
            state.push_step_to_tx(s);
        }

        Ok(())
    }
}

fn calc_memory_expension_gas_cost(curr_memory_word_size: u64, next_memory_word_size: u64) -> u64 {
    if next_memory_word_size <= curr_memory_word_size {
        0
    } else {
        let total_cost = |mem_word_size| {
            mem_word_size * GasCost::MEMORY.as_u64() + mem_word_size * mem_word_size / 512
        };
        total_cost(next_memory_word_size) - total_cost(curr_memory_word_size)
    }
}

fn calc_memory_copier_gas_cost(
    curr_memory_word_size: u64,
    next_memory_word_size: u64,
    num_copy_bytes: u64,
) -> u64 {
    let num_words = (num_copy_bytes + 31) / 32;
    num_words * GasCost::COPY.as_u64()
        + calc_memory_expension_gas_cost(curr_memory_word_size, next_memory_word_size)
}

fn gen_memory_copy_step(
    state: &mut CircuitInputStateRef,
    last_step: &ExecStep,
    src_addr: u64,
    dst_addr: u64,
    src_addr_end: u64,
    bytes_left: usize,
    memory_size: usize,
    from_tx: bool,
    bytes_map: &HashMap<u64, u8>,
) -> ExecStep {
    let mut step = last_step.clone();
    step.rwc = RWCounter(step.rwc.0 + step.bus_mapping_instance.len());
    step.bus_mapping_instance = Vec::new();
    step.exec_state = ExecState::CopyToMemory;
    step.gas_left = Gas(step.gas_left.0 - step.gas_cost.0);
    step.gas_cost = GasCost(0);
    step.pc = ProgramCounter(step.pc.0 + 1);
    step.stack_size = 0;
    step.memory_size = memory_size;

    let mut selectors = vec![0u8; MAX_COPY_BYTES];
    for (idx, selector) in selectors.iter_mut().enumerate() {
        if idx < bytes_left {
            *selector = 1;
            let addr = src_addr + idx as u64;
            let byte = if addr < src_addr_end {
                debug_assert!(bytes_map.contains_key(&addr));
                if !from_tx {
                    state.push_memory_op(
                        &mut step,
                        RW::READ,
                        (idx + src_addr as usize).into(),
                        bytes_map[&addr],
                    );
                }
                bytes_map[&addr]
            } else {
                0
            };
            state.push_memory_op(&mut step, RW::WRITE, (idx + dst_addr as usize).into(), byte);
        }
    }
    step.aux_data = Some(StepAuxiliaryData::CopyToMemory {
        src_addr,
        dst_addr,
        bytes_left: bytes_left as u64,
        src_addr_end,
        from_tx,
        selectors,
    });
    step
}

fn gen_memory_copy_steps(
    state: &mut CircuitInputStateRef,
    call_data_copy_step: &ExecStep,
    next_steps: &[GethExecStep],
) -> Result<Vec<ExecStep>, Error> {
    let memory_offset = next_steps[0].stack.nth_last(0)?.as_u64();
    let data_offset = next_steps[0].stack.nth_last(1)?.as_u64();
    let length = next_steps[0].stack.nth_last(2)?.as_usize();

    let is_root = state.call().is_root;
    let (src_addr, buffer_addr, buffer_addr_end) = if is_root {
        (data_offset, 0, 0 + state.tx.input.len() as u64)
    } else {
        let call_data_offset = state.call().call_data_offset;

        (
            call_data_offset + data_offset,
            call_data_offset,
            call_data_offset + state.tx.input.len() as u64,
        )
    };

    let buffer: Vec<u8> = vec![0; (buffer_addr_end - buffer_addr) as usize];

    let memory_size = if length == 0 {
        0
    } else {
        (memory_offset + length as u64 + 31) / 32 * 32
    };

    let bytes_map = (buffer_addr..buffer_addr_end)
        .zip(buffer.iter().copied())
        .collect();

    let mut copied = 0;
    let mut steps = vec![];
    let mut last_step = call_data_copy_step;

    while copied < length {
        steps.push(gen_memory_copy_step(
            state,
            last_step,
            src_addr + copied as u64,
            memory_offset + copied as u64,
            buffer_addr_end,
            length - copied,
            memory_size as usize,
            is_root,
            &bytes_map,
        ));
        last_step = steps.last().unwrap();
        copied += MAX_COPY_BYTES;
    }

    Ok(steps)
}
