use crate::{
    circuit_input_builder::{
        CircuitInputStateRef, CopyDataType, CopyEvent, ExecStep, NumberOrHash,
    },
    error::ExecError,
    evm::Opcode,
    operation::{AccountField, AccountOp, CallContextField, MemoryOp, RW},
    state_db::CodeDB,
    Error,
};
use eth_types::{Bytecode, GethExecStep, ToBigEndian, ToWord, Word, H160, H256};
use ethers_core::utils::{get_create2_address, keccak256, rlp};

#[derive(Debug, Copy, Clone)]
pub struct Create<const IS_CREATE2: bool>;

impl<const IS_CREATE2: bool> Opcode for Create<IS_CREATE2> {
    fn gen_associated_ops(
        state: &mut CircuitInputStateRef,
        geth_steps: &[GethExecStep],
    ) -> Result<Vec<ExecStep>, Error> {
        let geth_step = &geth_steps[0];
        let mut exec_step = state.new_step(geth_step)?;

        let tx_id = state.tx_ctx.id();
        let callee = state.parse_call(geth_step)?;
        let caller = state.call()?.clone();

        state.call_context_read(
            &mut exec_step,
            caller.call_id,
            CallContextField::TxId,
            tx_id.into(),
        );

        let depth = caller.depth;
        state.call_context_read(
            &mut exec_step,
            caller.call_id,
            CallContextField::Depth,
            depth.into(),
        );

        state.reversion_info_read(&mut exec_step, &caller);

        // stack operation
        // Get low Uint64 of offset to generate copy steps. Since offset could
        // be Uint64 overflow if length is zero.
        let offset = geth_step.stack.nth_last(1)?.low_u64() as usize;
        let length = geth_step.stack.nth_last(2)?.as_usize();

        if length != 0 {
            state
                .call_ctx_mut()?
                .memory
                .extend_at_least(offset + length);
        }
        let next_memory_word_size = state.call_ctx()?.memory_word_size();

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

        let callee_account = &state.sdb.get_account(&address).1.clone();
        let callee_exists = !callee_account.is_empty();
        let is_address_collision =
            callee_account.code_hash != CodeDB::empty_code_hash() || callee_account.nonce != 0;
        state.stack_write(
            &mut exec_step,
            geth_step.stack.nth_last_filled(n_pop - 1),
            if callee.is_success {
                address.to_word()
            } else {
                Word::zero()
            },
        )?;
        // stack end

        // Get caller's balance and nonce
        let caller_balance = state.sdb.get_balance(&caller.address);
        let caller_nonce = state.sdb.get_nonce(&caller.address);
        state.account_read(
            &mut exec_step,
            caller.address,
            AccountField::Balance,
            caller_balance,
        );
        state.account_read(
            &mut exec_step,
            caller.address,
            AccountField::Nonce,
            caller_nonce.into(),
        );

        // Check if an error of ErrDepth, ErrInsufficientBalance or
        // ErrNonceUintOverflow occurred.
        let is_precheck_ok =
            depth < 1025 && caller_balance >= callee.value && caller_nonce < u64::MAX;
        if is_precheck_ok {
            // Increase caller's nonce
            state.push_op_reversible(
                &mut exec_step,
                AccountOp {
                    address: caller.address,
                    field: AccountField::Nonce,
                    value: (caller_nonce + 1).into(),
                    value_prev: caller_nonce.into(),
                },
            )?;

            // add contract address to access list
            state.tx_access_list_write(&mut exec_step, address)?;

            // this could be good place for checking callee_exists = true, since above
            // operation happens in evm create() method before checking
            // ErrContractAddressCollision
            let code_hash_previous = if callee_exists {
                if is_precheck_ok && is_address_collision {
                    exec_step.error = Some(ExecError::ContractAddressCollision);
                }
                callee_account.code_hash
            } else {
                H256::zero()
            };

            state.account_read(
                &mut exec_step,
                callee.address,
                AccountField::CodeHash,
                code_hash_previous.to_word(),
            );
            // read callee nonce for address collision checking
            if !code_hash_previous.is_zero() {
                state.account_read(
                    &mut exec_step,
                    callee.address,
                    AccountField::Nonce,
                    callee_account.nonce.into(),
                );
            }
        }

        // Per EIP-150, all but one 64th of the caller's gas is sent to the
        // initialization call.
        let caller_gas_left = (geth_step.gas - geth_step.gas_cost) / 64;
        for (field, value) in [
            (CallContextField::ProgramCounter, (geth_step.pc + 1).into()),
            (
                CallContextField::StackPointer,
                geth_step.stack.nth_last_filled(n_pop - 1).0.into(),
            ),
            (CallContextField::GasLeft, caller_gas_left.into()),
            (CallContextField::MemorySize, next_memory_word_size.into()),
            (
                CallContextField::ReversibleWriteCounter,
                (exec_step.reversible_write_counter + 2).into(),
            ),
        ] {
            state.call_context_write(&mut exec_step, caller.call_id, field, value);
        }

        let (initialization_code, code_hash) = if length > 0 {
            handle_copy(state, &mut exec_step, state.call()?.call_id, offset, length)?
        } else {
            (vec![], CodeDB::empty_code_hash())
        };

        state.push_call(callee.clone());
        state.reversion_info_write(&mut exec_step, &callee);

        // handle init_code hashing & address generation
        if is_precheck_ok {
            // handle keccak_table_lookup
            let keccak_input = if IS_CREATE2 {
                let salt = geth_step.stack.nth_last(3)?;
                assert_eq!(
                    address,
                    get_create2_address(
                        caller.address,
                        salt.to_be_bytes(),
                        initialization_code.clone(),
                    )
                );
                std::iter::once(0xffu8)
                    .chain(caller.address.to_fixed_bytes())
                    .chain(salt.to_be_bytes())
                    .chain(code_hash.to_fixed_bytes())
                    .collect::<Vec<_>>()
            } else {
                let mut stream = rlp::RlpStream::new();
                stream.begin_list(2);
                stream.append(&caller.address);
                stream.append(&Word::from(caller_nonce));
                stream.out().to_vec()
            };
            assert_eq!(
                address,
                H160(keccak256(&keccak_input)[12..].try_into().unwrap())
            );

            state.block.sha3_inputs.push(keccak_input);
            state.block.sha3_inputs.push(initialization_code);
        }
        if is_precheck_ok && !is_address_collision {
            // Transfer function will skip transfer if the value is zero
            state.transfer(
                &mut exec_step,
                caller.address,
                callee.address,
                callee_exists,
                !callee_exists,
                callee.value,
            )?;

            // EIP 161, increase callee's nonce
            state.push_op_reversible(
                &mut exec_step,
                AccountOp {
                    address: callee.address,
                    field: AccountField::Nonce,
                    value: 1.into(),
                    value_prev: 0.into(),
                },
            )?;

            if length > 0 {
                for (field, value) in [
                    (CallContextField::CallerId, caller.call_id.into()),
                    (CallContextField::IsSuccess, callee.is_success.to_word()),
                    (
                        CallContextField::IsPersistent,
                        callee.is_persistent.to_word(),
                    ),
                    (CallContextField::TxId, state.tx_ctx.id().into()),
                    (
                        CallContextField::CallerAddress,
                        callee.caller_address.to_word(),
                    ),
                    (CallContextField::CalleeAddress, callee.address.to_word()),
                    (
                        CallContextField::RwCounterEndOfReversion,
                        callee.rw_counter_end_of_reversion.to_word(),
                    ),
                    (CallContextField::Depth, callee.depth.to_word()),
                    (CallContextField::IsRoot, false.to_word()),
                    (CallContextField::IsStatic, false.to_word()),
                    (CallContextField::IsCreate, true.to_word()),
                    (CallContextField::CodeHash, code_hash.to_word()),
                    (CallContextField::Value, callee.value),
                ] {
                    state.call_context_write(&mut exec_step, callee.call_id, field, value);
                }
            }
            // if it's empty init code
            else {
                for (field, value) in [
                    (CallContextField::LastCalleeId, callee.call_id.into()),
                    (CallContextField::LastCalleeReturnDataOffset, 0.into()),
                    (CallContextField::LastCalleeReturnDataLength, 0.into()),
                ] {
                    state.call_context_write(&mut exec_step, caller.call_id, field, value);
                }
                state.handle_return(&mut exec_step, geth_steps, false)?;
            };
        }
        // failed case: is_precheck_ok is false or is_address_collision is true
        else {
            for (field, value) in [
                (CallContextField::LastCalleeId, callee.call_id.into()),
                (CallContextField::LastCalleeReturnDataOffset, 0.into()),
                (CallContextField::LastCalleeReturnDataLength, 0.into()),
            ] {
                state.call_context_write(&mut exec_step, caller.call_id, field, value);
            }
            state.handle_return(&mut exec_step, geth_steps, false)?;
        }

        Ok(vec![exec_step])
    }
}

fn handle_copy(
    state: &mut CircuitInputStateRef,
    step: &mut ExecStep,
    call_id: usize,
    offset: usize,
    length: usize,
) -> Result<(Vec<u8>, H256), Error> {
    let initialization_bytes = state.caller_ctx()?.memory.0[offset..(offset + length)].to_vec();

    let initialization = Bytecode::from(initialization_bytes.clone());
    let code_hash = initialization.hash_h256();
    let bytes = initialization.code_vec();

    let rw_counter_start = state.block_ctx.rwc;
    for (i, (byte, _)) in bytes.iter().enumerate() {
        state.push_op(
            step,
            RW::READ,
            MemoryOp::new(call_id, (offset + i).into(), *byte),
        );
    }

    state.push_copy(
        step,
        CopyEvent {
            rw_counter_start,
            src_type: CopyDataType::Memory,
            src_id: NumberOrHash::Number(call_id),
            src_addr: offset.try_into().unwrap(),
            src_addr_end: (offset + length).try_into().unwrap(),
            dst_type: CopyDataType::Bytecode,
            dst_id: NumberOrHash::Hash(code_hash),
            dst_addr: 0,
            log_id: None,
            bytes,
        },
    );

    Ok((initialization_bytes, code_hash))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{circuit_input_builder::ExecState, mock::BlockData, operation::RW};
    use eth_types::{bytecode, evm_types::OpcodeId, geth_types::GethData, word};
    use mock::{test_ctx::helpers::account_0_code_account_1_no_code, TestContext};

    #[test]
    fn test_create_address_collision_error() {
        let code = bytecode! {
            PUSH21(word!("6B6020600060003760206000F3600052600C6014F3"))
            PUSH1(0)
            MSTORE

            PUSH1 (0xef) // salt
            PUSH1 (0x15) // size
            PUSH1 (0xB) // offset
            PUSH1 (0)   // value
            CREATE2

            PUSH1 (0xef) // salt
            PUSH1 (0x15) // size
            PUSH1 (0xB) // offset
            PUSH1 (0)   // value
            CREATE2

            PUSH1 (0x20)   // retLength
            PUSH1 (0x20)   // retOffset
            PUSH1 (0x20)   // argsLength
            PUSH1 (0x00)      // argsOffset
            PUSH1 (0x00)      // value
            DUP6           // addr from above CREATE2
            PUSH2 (0xFFFF) // gas
            CALL
            STOP
        };

        // Get the execution steps from the external tracer
        let block: GethData = TestContext::<2, 1>::new(
            None,
            account_0_code_account_1_no_code(code),
            |mut txs, accs| {
                txs[0].from(accs[1].address).to(accs[0].address);
            },
            |block, _tx| block.number(0xcafeu64),
        )
        .unwrap()
        .into();

        let builder = BlockData::new_from_geth_data(block.clone()).new_circuit_input_builder();
        let builder = builder
            .handle_block(&block.eth_block, &block.geth_traces)
            .unwrap();

        let tx_id = 1;
        let transaction = &builder.block.txs()[tx_id - 1];
        let step = transaction
            .steps()
            .iter()
            .filter(|step| step.exec_state == ExecState::Op(OpcodeId::CREATE2))
            .last()
            .unwrap();

        assert_eq!(step.error, Some(ExecError::ContractAddressCollision));

        let container = builder.block.container.clone();
        println!("{:?}", container.stack);
        println!("-----");
        println!("{:?}", step.bus_mapping_instance);
        println!("-----");
        let operation = &container.stack[step.bus_mapping_instance[5].as_usize()];
        assert_eq!(operation.rw(), RW::READ);
    }
}
