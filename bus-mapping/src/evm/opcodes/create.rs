use crate::circuit_input_builder::{
    CircuitInputStateRef, CopyDataType, CopyEvent, ExecStep, NumberOrHash,
};
use crate::evm::Opcode;
use crate::operation::{
    AccountField, AccountOp, CallContextField, MemoryOp, TxAccessListAccountOp, RW,
};
use crate::Error;
use eth_types::{
    evm_types::gas_utils::memory_expansion_gas_cost, Bytecode, GethExecStep, ToBigEndian, ToWord,
    Word, H160, H256,
};
use ethers_core::utils::{get_create2_address, keccak256, rlp};

#[derive(Debug, Copy, Clone)]
pub struct Create<const IS_CREATE2: bool>;

impl<const IS_CREATE2: bool> Opcode for Create<IS_CREATE2> {
    fn gen_associated_ops(
        state: &mut CircuitInputStateRef,
        geth_steps: &[GethExecStep],
    ) -> Result<Vec<ExecStep>, Error> {
        let geth_step = &geth_steps[0];

        let offset = geth_step.stack.nth_last(1)?.as_usize();
        let length = geth_step.stack.nth_last(2)?.as_usize();

        let curr_memory_word_size = state.call_ctx()?.memory_word_size();
        if length != 0 {
            state
                .call_ctx_mut()?
                .memory
                .extend_at_least(offset + length);
        }
        let next_memory_word_size = state.call_ctx()?.memory_word_size();

        let mut exec_step = state.new_step(geth_step)?;

        // TODO: rename this to initialization call?
        let call = state.parse_call(geth_step)?;

        let n_pop = if IS_CREATE2 { 4 } else { 3 };
        for i in 0..n_pop {
            state.stack_read(
                &mut exec_step,
                geth_step.stack.nth_last_filled(i),
                geth_step.stack.nth_last(i)?,
            )?;
        }

        let address = if IS_CREATE2 {
            state.create2_address(&geth_steps[0])?
        } else {
            state.create_address()?
        };
        state.stack_write(
            &mut exec_step,
            geth_step.stack.nth_last_filled(n_pop - 1),
            if call.is_success {
                address.to_word()
            } else {
                Word::zero()
            },
        )?;

        let mut initialization_code = vec![];
        if length > 0 {
            initialization_code =
                handle_copy(state, &mut exec_step, state.call()?.call_id, offset, length)?;
        }

        // Quote from [EIP-2929](https://eips.ethereum.org/EIPS/eip-2929)
        // > When a CREATE or CREATE2 opcode is called,
        // > immediately (i.e. before checks are done to determine
        // > whether or not the address is unclaimed)
        // > add the address being created to accessed_addresses,
        // > but gas costs of CREATE and CREATE2 are unchanged

        let tx_id = state.tx_ctx.id();
        let current_call = state.call()?.clone();

        for (field, value) in [
            (CallContextField::TxId, tx_id.to_word()),
            (
                CallContextField::RwCounterEndOfReversion,
                current_call.rw_counter_end_of_reversion.to_word(),
            ),
            (
                CallContextField::IsPersistent,
                current_call.is_persistent.to_word(),
            ),
        ] {
            state.call_context_read(&mut exec_step, current_call.call_id, field, value);
        }

        let is_warm = state.sdb.check_account_in_access_list(&address);
        state.push_op_reversible(
            &mut exec_step,
            RW::WRITE,
            TxAccessListAccountOp {
                tx_id,
                address,
                is_warm: true,
                is_warm_prev: is_warm,
            },
        )?;

        state.call_context_read(
            &mut exec_step,
            current_call.call_id,
            CallContextField::CalleeAddress,
            current_call.address.to_word(),
        );

        // Increase caller's nonce
        let caller_nonce = state.sdb.get_nonce(&call.caller_address);
        state.push_op_reversible(
            &mut exec_step,
            RW::WRITE,
            AccountOp {
                address: call.caller_address,
                field: AccountField::Nonce,
                value: (caller_nonce + 1).into(),
                value_prev: caller_nonce.into(),
            },
        )?;

        state.push_call(call.clone());
        // Increase callee's nonce
        for (field, value) in [
            (
                CallContextField::RwCounterEndOfReversion,
                call.rw_counter_end_of_reversion.to_word(),
            ),
            (CallContextField::IsPersistent, call.is_persistent.to_word()),
        ] {
            state.call_context_write(&mut exec_step, call.call_id, field, value);
        }

        let nonce_prev = state.sdb.get_nonce(&call.address);
        debug_assert!(nonce_prev == 0);
        state.push_op_reversible(
            &mut exec_step,
            RW::WRITE,
            AccountOp {
                address: call.address,
                field: AccountField::Nonce,
                value: 1.into(),
                value_prev: 0.into(),
            },
        )?;

        state.transfer(
            &mut exec_step,
            call.caller_address,
            call.address,
            call.value,
        )?;

        let memory_expansion_gas_cost =
            memory_expansion_gas_cost(curr_memory_word_size, next_memory_word_size);

        // EIP-150: all but one 64th of the caller's gas is sent to the callee.
        let caller_gas_left =
            (geth_step.gas.0 - geth_step.gas_cost.0 - memory_expansion_gas_cost) / 64;

        for (field, value) in [
            (
                CallContextField::ProgramCounter,
                (geth_step.pc.0 + 1).into(),
            ),
            (
                CallContextField::StackPointer,
                geth_step.stack.nth_last_filled(n_pop - 1).0.into(),
            ),
            (CallContextField::GasLeft, caller_gas_left.into()),
            (CallContextField::MemorySize, next_memory_word_size.into()),
            (
                CallContextField::ReversibleWriteCounter,
                // +2 is because we do some reversible writes before pushing the call. can be just
                // push the call later?
                (exec_step.reversible_write_counter + 2).into(),
            ),
        ] {
            state.call_context_write(&mut exec_step, current_call.call_id, field, value);
        }

        for (field, value) in [
            (CallContextField::CallerId, current_call.call_id.into()),
            (CallContextField::IsSuccess, call.is_success.to_word()),
            (CallContextField::IsPersistent, call.is_persistent.to_word()),
            (CallContextField::TxId, state.tx_ctx.id().into()),
            (
                CallContextField::CallerAddress,
                current_call.address.to_word(),
            ),
            (CallContextField::CalleeAddress, call.address.to_word()),
            (
                CallContextField::RwCounterEndOfReversion,
                call.rw_counter_end_of_reversion.to_word(),
            ),
        ] {
            state.call_context_write(&mut exec_step, call.call_id, field, value);
        }

        let keccak_input = if IS_CREATE2 {
            let salt = geth_step.stack.nth_last(3)?;
            assert_eq!(
                address,
                get_create2_address(
                    current_call.address,
                    salt.to_be_bytes().to_vec(),
                    initialization_code.clone()
                )
            );
            std::iter::once(0xffu8)
                .chain(current_call.address.to_fixed_bytes()) // also don't need to be reversed....
                .chain(salt.to_be_bytes())
                .chain(keccak256(&initialization_code))
                .collect::<Vec<_>>()
        } else {
            let mut stream = rlp::RlpStream::new();
            stream.begin_list(2);
            stream.append(&current_call.address);
            stream.append(&Word::from(caller_nonce));
            stream.out().to_vec()
        };

        assert_eq!(
            address,
            H160(keccak256(&keccak_input)[12..].try_into().unwrap())
        );

        state.block.sha3_inputs.push(keccak_input);

        if length == 0 {
            state.handle_return(geth_step)?;
        }

        Ok(vec![exec_step])
    }
}

fn handle_copy(
    state: &mut CircuitInputStateRef,
    step: &mut ExecStep,
    callee_id: usize,
    offset: usize,
    length: usize,
) -> Result<Vec<u8>, Error> {
    let initialization_bytes = state.call_ctx()?.memory.0[offset..offset + length].to_vec();
    let dst_id = NumberOrHash::Hash(H256(keccak256(&initialization_bytes)));
    let bytes: Vec<_> = Bytecode::from(initialization_bytes.clone())
        .code
        .iter()
        .map(|element| (element.value, element.is_code))
        .collect();

    let rw_counter_start = state.block_ctx.rwc;
    for (i, (byte, _)) in bytes.iter().enumerate() {
        // this could be a memory read, if this happens before we push the new call?
        state.push_op(
            step,
            RW::READ,
            MemoryOp::new(callee_id, (offset + i).into(), *byte),
        );
    }

    state.push_copy(CopyEvent {
        rw_counter_start,
        src_type: CopyDataType::Memory,
        src_id: NumberOrHash::Number(callee_id),
        src_addr: offset.try_into().unwrap(),
        src_addr_end: (offset + length).try_into().unwrap(),
        dst_type: CopyDataType::Bytecode,
        dst_id,
        dst_addr: 0,
        log_id: None,
        bytes,
    });

    Ok(initialization_bytes)
}
