use crate::{
    circuit_input_builder::{CircuitInputStateRef, ExecStep},
    operation::{CallContextField, CallContextOp, MemoryOp, RW},
    Error,
};
use eth_types::{GethExecStep, U256};

use super::Opcode;

#[derive(Clone, Copy, Debug)]
pub(crate) struct Calldataload;

impl Opcode for Calldataload {
    fn gen_associated_ops(
        state: &mut CircuitInputStateRef,
        geth_steps: &[GethExecStep],
    ) -> Result<Vec<ExecStep>, Error> {
        let geth_step = &geth_steps[0];
        let mut exec_step = state.new_step(geth_step)?;

        // fetch the top of the stack, i.e. offset in calldata to start reading 32-bytes
        // from.
        let offset = geth_step.stack.nth_last(0)?;

        state.push_stack_op(
            &mut exec_step,
            RW::READ,
            geth_step.stack.nth_last_filled(0),
            offset,
        )?;

        state.push_op(
            &mut exec_step,
            RW::READ,
            CallContextOp {
                call_id: state.call()?.call_id,
                field: CallContextField::TxId,
                value: state.tx_ctx.id().into(),
            },
        );

        let is_root = state.call()?.is_root;

        if !is_root {
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
            state.push_op(
                &mut exec_step,
                RW::READ,
                CallContextOp {
                    call_id: state.call()?.call_id,
                    field: CallContextField::CallerId,
                    value: state.call()?.caller_id.into(),
                },
            );
        }

        let (offset, src_addr, src_addr_end, caller_id, call_data) = {
            let call = state.call()?;
            (
                offset.as_usize(),
                call.call_data_offset as usize + offset.as_usize(),
                call.call_data_offset as usize + call.call_data_length as usize,
                call.caller_id,
                state.call_ctx()?.call_data.to_vec(),
            )
        };
        let calldata_word = (0..32)
            .map(|idx| {
                let addr = offset + idx;
                let byte = if addr < src_addr_end {
                    call_data[addr]
                } else {
                    0
                };
                if !is_root {
                    state.push_op(
                        &mut exec_step,
                        RW::READ,
                        MemoryOp::new(caller_id, src_addr.into(), byte),
                    );
                }
                byte
            })
            .collect::<Vec<u8>>();

        state.push_stack_op(
            &mut exec_step,
            RW::WRITE,
            geth_step.stack.last_filled(),
            U256::from_big_endian(&calldata_word),
        )?;

        Ok(vec![exec_step])
    }
}

#[cfg(test)]
mod calldataload_tests {
    use eth_types::{
        bytecode,
        evm_types::{OpcodeId, StackAddress},
        geth_types::GethData,
        Word,
    };
    use mock::{
        test_ctx::helpers::{account_0_code_account_1_no_code, tx_from_1_to_0},
        TestContext,
    };
    use rand::random;

    use crate::{circuit_input_builder::ExecState, mock::BlockData, operation::StackOp};

    use super::*;

    fn rand_bytes(size: usize) -> Vec<u8> {
        (0..size).map(|_| random()).collect::<Vec<u8>>()
    }

    #[test]
    fn calldataload_root_opcode_impl() {
        // 1. should be right padded
        test_root_ok(0u64, vec![1u8, 2u8], {
            let mut v = vec![0u8; 32];
            v[0] = 1u8;
            v[1] = 2u8;
            Word::from_big_endian(&v)
        });
        // 2. exactly 32 bytes
        let calldata = rand_bytes(32);
        test_root_ok(0u64, calldata.clone(), Word::from_big_endian(&calldata));
        // 3. take only 32 bytes
        let calldata = rand_bytes(64);
        test_root_ok(
            12u64,
            calldata.clone(),
            Word::from_big_endian(&calldata[12..44]),
        );
    }

    // This test must be enabled and should pass once `CREATE` is handled with a
    // dummy gen associated ops.
    #[test]
    #[ignore]
    fn calldataload_internal_opcode_impl() {
        test_internal_ok();
    }

    fn test_internal_ok() {
        // PUSH3 600035
        // PUSH1 00
        // MSTORE
        // PUSH1 03
        // PUSH1 1D
        // RETURN
        let contract_code: Vec<u8> = hex::decode("626000356000526003601DF3").unwrap();
        let create_and_call = bytecode! {
            // 1. Store the following bytes to memory
            PUSH12(Word::from_big_endian(&contract_code))
            PUSH1(0x00)
            MSTORE
            // 2. Create a contract with code: 60 00 35
            PUSH1(0x0c) // size
            PUSH1(0x14) // offset
            PUSH1(0x00) // value
            CREATE
            // 3. Call created contract, i.e. CALLDATALOAD is in internal call
            PUSH1(0x00)   // retSize
            PUSH1(0x00)   // retOffset
            PUSH1(0x20)   // argsSize
            PUSH1(0x00)   // argsOffset
            PUSH1(0x00)   // value
            DUP6          // address
            PUSH2(0xFFFF) // gas
            CALL
        };

        let block: GethData = TestContext::<2, 1>::new(
            None,
            account_0_code_account_1_no_code(create_and_call),
            tx_from_1_to_0,
            |block, _tx| block.number(0xcafeu64),
        )
        .unwrap()
        .into();

        let mut builder = BlockData::new_from_geth_data(block.clone()).new_circuit_input_builder();
        builder
            .handle_block(&block.eth_block, &block.geth_traces)
            .unwrap();

        let _step = builder.block.txs()[0]
            .steps()
            .iter()
            .find(|step| step.exec_state == ExecState::Op(OpcodeId::CALLDATALOAD))
            .unwrap();
    }

    fn test_root_ok(offset: u64, calldata: Vec<u8>, calldata_word: Word) {
        let code = bytecode! {
            PUSH32(offset)
            CALLDATALOAD
            STOP
        };

        let block: GethData = TestContext::<2, 1>::new(
            None,
            account_0_code_account_1_no_code(code),
            |mut txs, accs| {
                txs[0]
                    .to(accs[0].address)
                    .from(accs[1].address)
                    .input(calldata.into());
            },
            |block, _tx| block.number(0xcafeu64),
        )
        .unwrap()
        .into();

        let mut builder = BlockData::new_from_geth_data(block.clone()).new_circuit_input_builder();
        builder
            .handle_block(&block.eth_block, &block.geth_traces)
            .unwrap();

        let step = builder.block.txs()[0]
            .steps()
            .iter()
            .find(|step| step.exec_state == ExecState::Op(OpcodeId::CALLDATALOAD))
            .unwrap();

        assert_eq!(
            [0, 2]
                .map(|idx| &builder.block.container.stack[step.bus_mapping_instance[idx].as_usize()])
                .map(|op| (op.rw(), op.op())),
            [
                (
                    RW::READ,
                    &StackOp::new(1, StackAddress::from(1023), Word::from(offset)),
                ),
                (
                    RW::WRITE,
                    &StackOp::new(1, StackAddress::from(1023), calldata_word),
                ),
            ]
        );

        assert_eq!(
            {
                let op =
                    &builder.block.container.call_context[step.bus_mapping_instance[1].as_usize()];
                (op.rw(), op.op())
            },
            (
                RW::READ,
                &CallContextOp {
                    call_id: builder.block.txs()[0].calls()[0].call_id,
                    field: CallContextField::TxId,
                    value: Word::from(1),
                }
            ),
        );
    }
}
