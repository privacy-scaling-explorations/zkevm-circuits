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
        geth_steps: &[GethExecStep],
    ) -> Result<Vec<ExecStep>, Error> {
        let geth_step = &geth_steps[0];
        let mut exec_steps = Vec::new();
        exec_steps.push(gen_calldatacopy_step(state, geth_step)?);
        let memory_copy_steps = gen_memory_copy_steps(state, geth_steps)?;
        exec_steps.extend(memory_copy_steps);
        Ok(exec_steps)
    }
}

fn gen_calldatacopy_step(
    state: &mut CircuitInputStateRef,
    geth_step: &GethExecStep,
) -> Result<ExecStep, Error> {
    let mut exec_step = state.new_step(geth_step)?;
    let memory_offset = geth_step.stack.nth_last(0)?;
    let data_offset = geth_step.stack.nth_last(1)?;
    let length = geth_step.stack.nth_last(2)?;

    state.push_stack_op(
        &mut exec_step,
        RW::READ,
        geth_step.stack.nth_last_filled(0),
        memory_offset,
    )?;
    state.push_stack_op(
        &mut exec_step,
        RW::READ,
        geth_step.stack.nth_last_filled(1),
        data_offset,
    )?;
    state.push_stack_op(&mut exec_step, RW::READ, geth_step.stack.nth_last_filled(2), length)?;
    state.push_op(
        &mut exec_step,
        RW::READ,
        CallContextOp {
            call_id: state.call()?.call_id,
            field: CallContextField::TxId,
            value: state.tx_ctx.id().into(),
        },
    );

    if !state.call()?.is_root {
        state.push_op(
            &mut exec_step,
            RW::READ,
            CallContextOp {
                call_id: state.call()?.call_id,
                field: CallContextField::CallDataLength,
                value: state.call()?.call_data_length.into(),
            },
        );
        state.push_op(
            &mut exec_step,
            RW::READ,
            CallContextOp {
                call_id: state.call()?.call_id,
                field: CallContextField::CallDataOffset,
                value: state.call()?.call_data_offset.into(),
            },
        );
    };
    println!("exec_step = {exec_step:?}");
    Ok(exec_step)
}

fn gen_memory_copy_step(
    state: &mut CircuitInputStateRef,
    exec_step: &mut ExecStep,
    src_addr: u64,
    dst_addr: u64,
    src_addr_end: u64,
    bytes_left: usize,
    is_root: bool,
) {
    let mut selectors = vec![0u8; MAX_COPY_BYTES];
    for (idx, selector) in selectors.iter_mut().enumerate() {
        if idx < bytes_left {
            *selector = 1;
            let addr = src_addr + idx as u64;
            let byte = if addr < src_addr_end {
                if is_root {
                    state.tx.input[addr as usize]
                } else {
                    // TODO, read caller memory
                    // state.push_memory_op(
                    //     exec_step,
                    //     RW::READ,
                    //     (addr as usize).into(),
                    //     bytes_map[&addr],
                    // );
                    0u8
                }
            } else {
                0
            };
            println!("calldata[{}] = {}", addr, byte);
            state.push_memory_op(exec_step, RW::WRITE, (idx + dst_addr as usize).into(), byte);
        }
    }

    exec_step.aux_data = Some(StepAuxiliaryData::CopyToMemory {
        src_addr,
        dst_addr,
        bytes_left: bytes_left as u64,
        src_addr_end,
        from_tx: is_root,
        selectors,
    });
}

fn gen_memory_copy_steps(
    state: &mut CircuitInputStateRef,
    geth_steps: &[GethExecStep],
) -> Result<Vec<ExecStep>, Error> {
    let memory_offset = geth_steps[0].stack.nth_last(0)?.as_u64();
    let data_offset = geth_steps[0].stack.nth_last(1)?.as_u64();
    let length = geth_steps[0].stack.nth_last(2)?.as_usize();

    let call_data_offset = state.call()?.call_data_offset;
    let call_data_length = state.call()?.call_data_length;
    let (src_addr, buffer_addr_end) = (
        call_data_offset + data_offset,
        call_data_offset + call_data_length,
    );

    let mut copied = 0;
    let mut steps = vec![];
    while copied < length {
        let mut exec_step = state.new_step(&geth_steps[1])?;
        exec_step.exec_state = ExecState::CopyToMemory;
        gen_memory_copy_step(
            state,
            &mut exec_step,
            src_addr + copied as u64,
            memory_offset + copied as u64,
            buffer_addr_end,
            length - copied,
            state.call()?.is_root,
        );
        println!("exec_step = {:?}", exec_step);
        steps.push(exec_step);
        copied += MAX_COPY_BYTES;
    }

    Ok(steps)
}

/*
#[cfg(test)]
mod calldatacopy_tests {
    use crate::{
        circuit_input_builder::{ExecStep, TransactionContext},
        mock::BlockData,
        operation::{CallContextField, CallContextOp, RW},
        Error,
    };
    use eth_types::evm_types::StackAddress;
    use eth_types::{bytecode, Word};
    use mock::new_single_tx_trace_code_at_start;
    use pretty_assertions::assert_eq;

    #[test]
    fn calldatacopy_opcode_impl() -> Result<(), Error> {
        // Set length to zero for only testing CallDataCopy (without CopyToMemory
        // steps).
        let length = Word::from(0);
        let data_offset = Word::from(0);
        let memory_offset = Word::from(0x40);

        let code = bytecode! {
            PUSH32(length)
            PUSH32(data_offset)
            PUSH32(memory_offset)
            #[start]
            CALLDATACOPY
            STOP
        };

        // Get the execution steps from the external tracer
        let block =
            BlockData::new_from_geth_data(new_single_tx_trace_code_at_start(&code).unwrap());

        let mut builder = block.new_circuit_input_builder();
        builder
            .handle_tx(&block.eth_tx, &block.geth_trace)
            .unwrap();

        let mut test_builder = block.new_circuit_input_builder();
        let mut tx = test_builder
            .new_tx(&block.eth_tx, !block.geth_trace.failed)
            .unwrap();
        let mut tx_ctx = TransactionContext::new(&block.eth_tx, &block.geth_trace).unwrap();

        // Generate step corresponding to CALLDATACOPY
        let mut step = ExecStep::new(
            &block.geth_trace.struct_logs[0],
            0,
            test_builder.block_ctx.rwc,
            0,
        );
        let mut state = test_builder.state_ref(&mut tx, &mut tx_ctx);

        state.push_stack_op(&mut step, RW::READ, StackAddress::from(1021), memory_offset);
        state.push_stack_op(&mut step, RW::READ, StackAddress::from(1022), data_offset);
        state.push_stack_op(&mut step, RW::READ, StackAddress::from(1023), length);
        state.push_op(
            &mut step,
            RW::READ,
            CallContextOp {
                call_id: state.call().call_id,
                field: CallContextField::TxId,
                value: state.tx_ctx.id().into(),
            },
        );

        if !state.call().is_root {
            state.push_op(
                &mut step,
                RW::READ,
                CallContextOp {
                    call_id: state.call().call_id,
                    field: CallContextField::CallDataLength,
                    value: state.call().call_data_length.into(),
                },
            );
            state.push_op(
                &mut step,
                RW::READ,
                CallContextOp {
                    call_id: state.call().call_id,
                    field: CallContextField::CallDataOffset,
                    value: state.call().call_data_offset.into(),
                },
            );
        };

        tx.steps_mut().push(step);
        test_builder.block.txs_mut().push(tx);

        // Compare first step bus mapping instance
        assert_eq!(
            builder.block.txs()[0].steps()[0].bus_mapping_instance,
            test_builder.block.txs()[0].steps()[0].bus_mapping_instance,
        );

        // Compare containers
        assert_eq!(builder.block.container, test_builder.block.container);

        Ok(())
    }
}
*/
