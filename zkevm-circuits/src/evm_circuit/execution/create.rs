use bus_mapping::{circuit_input_builder::CopyDataType, evm::OpcodeId};
use eth_types::{evm_types::GasCost, Field, ToBigEndian, ToLittleEndian, ToScalar, U256};
use ethers_core::utils::keccak256;
use gadgets::util::{expr_from_bytes, not, select, Expr};
use halo2_proofs::{circuit::Value, plonk::Error};
use keccak256::EMPTY_HASH_LE;
use std::iter::once;

use crate::{
    evm_circuit::{
        param::{N_BYTES_GAS, N_BYTES_MEMORY_ADDRESS, N_BYTES_MEMORY_WORD_SIZE, N_BYTES_WORD},
        step::ExecutionState,
        util::{
            common_gadget::TransferGadget,
            constraint_builder::{
                ConstraintBuilder, ReversionInfo, StepStateTransition,
                Transition::{Delta, To},
            },
            math_gadget::{ConstantDivisionGadget, ContractCreateGadget},
            memory_gadget::{MemoryAddressGadget, MemoryExpansionGadget},
            CachedRegion, Cell, Word,
        },
    },
    table::{AccountFieldTag, CallContextFieldTag},
    witness::{Block, Call, ExecStep, Transaction},
};

use super::ExecutionGadget;

#[derive(Clone, Debug)]
pub(crate) struct CreateGadget<F, const IS_CREATE2: bool, const S: ExecutionState> {
    opcode: Cell<F>,
    value: Word<F>,
    tx_id: Cell<F>,
    reversion_info: ReversionInfo<F>,
    was_warm: Cell<F>,
    depth: Cell<F>,
    callee_reversion_info: ReversionInfo<F>,
    callee_is_success: Cell<F>,
    transfer: TransferGadget<F>,
    init_code: MemoryAddressGadget<F>,
    init_code_word_size: ConstantDivisionGadget<F, N_BYTES_MEMORY_ADDRESS>,
    memory_expansion: MemoryExpansionGadget<F, 1, N_BYTES_MEMORY_WORD_SIZE>,
    gas_left: ConstantDivisionGadget<F, N_BYTES_GAS>,
    create: ContractCreateGadget<F, IS_CREATE2>,
    keccak_output: Word<F>,
}

impl<F: Field, const IS_CREATE2: bool, const S: ExecutionState> ExecutionGadget<F>
    for CreateGadget<F, IS_CREATE2, S>
{
    const NAME: &'static str = "CREATE";

    const EXECUTION_STATE: ExecutionState = S;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        let callee_call_id = cb.curr.state.rw_counter.clone();

        let opcode = cb.query_cell();
        cb.opcode_lookup(opcode.expr(), 1.expr());

        cb.require_equal(
            "Opcode is CREATE or CREATE2",
            opcode.expr(),
            select::expr(
                IS_CREATE2.expr(),
                OpcodeId::CREATE2.expr(),
                OpcodeId::CREATE.expr(),
            ),
        );

        let value = cb.query_word_rlc();

        let init_code_memory_offset = cb.query_cell_phase2();
        let init_code_length = cb.query_word_rlc();
        let init_code =
            MemoryAddressGadget::construct(cb, init_code_memory_offset, init_code_length);

        let keccak_output = cb.query_word_rlc();
        let new_address_rlc = cb.word_rlc::<N_BYTES_MEMORY_ADDRESS>(
            keccak_output
                .cells
                .iter()
                .take(N_BYTES_MEMORY_ADDRESS)
                .map(Expr::expr)
                .collect::<Vec<_>>()
                .try_into()
                .unwrap(),
        );
        let new_address = expr_from_bytes(&keccak_output.cells[..N_BYTES_MEMORY_ADDRESS]);

        let callee_is_success = cb.query_bool();

        let create = ContractCreateGadget::construct(cb);

        cb.stack_pop(value.expr());
        cb.stack_pop(init_code.offset_rlc());
        cb.stack_pop(init_code.length_rlc());
        cb.condition(IS_CREATE2.expr(), |cb| {
            cb.stack_pop(create.salt_rlc());
        });
        cb.stack_push(callee_is_success.expr() * new_address_rlc);

        cb.condition(init_code.has_length(), |cb| {
            cb.copy_table_lookup(
                cb.curr.state.call_id.expr(),
                CopyDataType::Memory.expr(),
                create.code_hash_rlc(),
                CopyDataType::Bytecode.expr(),
                init_code.offset(),
                init_code.address(),
                0.expr(),
                init_code.length(),
                0.expr(),
                init_code.length(),
            );
        });
        cb.condition(not::expr(init_code.has_length()), |cb| {
            cb.require_equal(
                "Empty code",
                create.code_hash_rlc(),
                cb.word_rlc((*EMPTY_HASH_LE).map(|b| b.expr())),
            );
        });

        let tx_id = cb.call_context(None, CallContextFieldTag::TxId);
        let mut reversion_info = cb.reversion_info_read(None);
        let was_warm = cb.query_bool();
        cb.account_access_list_write(
            tx_id.expr(),
            new_address.clone(),
            1.expr(),
            was_warm.expr(),
            Some(&mut reversion_info),
        );
        cb.call_context_lookup(
            0.expr(),
            None,
            CallContextFieldTag::CalleeAddress,
            create.caller_address(),
        );
        cb.account_write(
            create.caller_address(),
            AccountFieldTag::Nonce,
            create.caller_nonce() + 1.expr(),
            create.caller_nonce(),
            Some(&mut reversion_info),
        );

        let mut callee_reversion_info = cb.reversion_info_write(Some(callee_call_id.expr()));
        cb.require_equal(
            "callee_is_persistent == is_persistent ⋅ is_success",
            callee_reversion_info.is_persistent(),
            reversion_info.is_persistent() * callee_is_success.expr(),
        );
        cb.condition(callee_is_success.expr() * (1.expr() - reversion_info.is_persistent()), |cb| {
            cb.require_equal(
                "callee_rw_counter_end_of_reversion == rw_counter_end_of_reversion - (reversible_write_counter + 1)",
                callee_reversion_info.rw_counter_end_of_reversion(),
                reversion_info.rw_counter_of_reversion(),
            );
        });
        cb.account_write(
            new_address.clone(),
            AccountFieldTag::Nonce,
            1.expr(),
            0.expr(),
            Some(&mut callee_reversion_info),
        );

        let transfer = TransferGadget::construct(
            cb,
            create.caller_address(),
            new_address.clone(),
            value.clone(),
            &mut callee_reversion_info,
        );

        let memory_expansion = MemoryExpansionGadget::construct(cb, [init_code.address()]);
        let init_code_word_size = ConstantDivisionGadget::construct(
            cb,
            init_code.length() + (N_BYTES_WORD - 1).expr(),
            N_BYTES_WORD as u64,
        );

        let keccak_gas_cost =
            GasCost::COPY_SHA3.expr() * IS_CREATE2.expr() * init_code_word_size.quotient();

        let gas_cost = GasCost::CREATE.expr() + memory_expansion.gas_cost() + keccak_gas_cost;
        let gas_remaining = cb.curr.state.gas_left.expr() - gas_cost.clone();
        let gas_left = ConstantDivisionGadget::construct(cb, gas_remaining.clone(), 64);
        let callee_gas_left = gas_remaining - gas_left.quotient();

        for (field_tag, value) in [
            (
                CallContextFieldTag::ProgramCounter,
                cb.curr.state.program_counter.expr() + 1.expr(),
            ),
            (
                CallContextFieldTag::StackPointer,
                cb.curr.state.stack_pointer.expr() + 2.expr() + IS_CREATE2.expr(),
            ),
            (CallContextFieldTag::GasLeft, gas_left.quotient()),
            (
                CallContextFieldTag::MemorySize,
                memory_expansion.next_memory_word_size(),
            ),
            (
                CallContextFieldTag::ReversibleWriteCounter,
                cb.curr.state.reversible_write_counter.expr() + 2.expr(),
            ),
        ] {
            cb.call_context_lookup(true.expr(), None, field_tag, value);
        }

        let depth = cb.call_context(None, CallContextFieldTag::Depth);

        for (field_tag, value) in [
            (CallContextFieldTag::CallerId, cb.curr.state.call_id.expr()),
            (CallContextFieldTag::IsSuccess, callee_is_success.expr()),
            (
                CallContextFieldTag::IsPersistent,
                callee_reversion_info.is_persistent(),
            ),
            (CallContextFieldTag::TxId, tx_id.expr()),
            (CallContextFieldTag::CallerAddress, create.caller_address()),
            (CallContextFieldTag::CalleeAddress, new_address),
            (
                CallContextFieldTag::RwCounterEndOfReversion,
                callee_reversion_info.rw_counter_end_of_reversion(),
            ),
            (CallContextFieldTag::Depth, depth.expr() + 1.expr()),
            (CallContextFieldTag::IsRoot, false.expr()),
            (CallContextFieldTag::IsStatic, false.expr()),
            (CallContextFieldTag::IsCreate, true.expr()),
            (CallContextFieldTag::CodeHash, create.code_hash_rlc()),
        ] {
            cb.call_context_lookup(true.expr(), Some(callee_call_id.expr()), field_tag, value);
        }

        cb.keccak_table_lookup(
            create.input_rlc(cb),
            create.input_length(),
            keccak_output.expr(),
        );

        cb.condition(init_code.has_length(), |cb| {
            cb.require_step_state_transition(StepStateTransition {
                rw_counter: Delta(cb.rw_counter_offset()),
                call_id: To(callee_call_id.expr()),
                is_root: To(false.expr()),
                is_create: To(true.expr()),
                code_hash: To(create.code_hash_rlc()),
                gas_left: To(callee_gas_left),
                reversible_write_counter: To(3.expr()),
                ..StepStateTransition::new_context()
            })
        });

        cb.condition(not::expr(init_code.has_length()), |cb| {
            cb.require_step_state_transition(StepStateTransition {
                rw_counter: Delta(cb.rw_counter_offset()),
                program_counter: Delta(1.expr()),
                stack_pointer: Delta(2.expr() + IS_CREATE2.expr()),
                gas_left: Delta(-gas_cost),
                reversible_write_counter: Delta(5.expr()),
                ..Default::default()
            })
        });

        Self {
            opcode,
            reversion_info,
            tx_id,
            was_warm,
            value,
            depth,
            callee_reversion_info,
            transfer,
            init_code,
            memory_expansion,
            gas_left,
            callee_is_success,
            init_code_word_size,
            create,
            keccak_output,
        }
    }

    #[allow(unused_variables)]
    fn assign_exec_step(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        block: &Block<F>,
        tx: &Transaction,
        call: &Call,
        step: &ExecStep,
    ) -> Result<(), Error> {
        let opcode = step.opcode.unwrap();
        let is_create2 = opcode == OpcodeId::CREATE2;
        self.opcode
            .assign(region, offset, Value::known(F::from(opcode.as_u64())))?;

        let [value, init_code_start, init_code_length] = [0, 1, 2]
            .map(|i| step.rw_indices[i])
            .map(|idx| block.rws[idx].stack_value());
        self.value
            .assign(region, offset, Some(value.to_le_bytes()))?;

        let salt = if is_create2 {
            block.rws[step.rw_indices[3]].stack_value()
        } else {
            U256::zero()
        };

        let values: Vec<_> = (4 + usize::from(is_create2)
            ..4 + usize::from(is_create2) + init_code_length.as_usize())
            .map(|i| block.rws[step.rw_indices[i]].memory_value())
            .collect();

        let init_code_address =
            self.init_code
                .assign(region, offset, init_code_start, init_code_length)?;

        self.tx_id
            .assign(region, offset, Value::known(tx.id.to_scalar().unwrap()))?;
        self.depth.assign(
            region,
            offset,
            Value::known(call.depth.to_scalar().unwrap()),
        )?;

        self.reversion_info.assign(
            region,
            offset,
            call.rw_counter_end_of_reversion,
            call.is_persistent,
        )?;

        let copy_rw_increase = init_code_length.as_usize();
        let tx_access_rw =
            block.rws[step.rw_indices[7 + usize::from(is_create2) + copy_rw_increase]];
        self.was_warm.assign(
            region,
            offset,
            Value::known(
                tx_access_rw
                    .tx_access_list_value_pair()
                    .1
                    .to_scalar()
                    .unwrap(),
            ),
        )?;

        let caller_nonce = block.rws
            [step.rw_indices[9 + usize::from(is_create2) + copy_rw_increase]]
            .account_value_pair()
            .1
            .low_u64();

        let [callee_rw_counter_end_of_reversion, callee_is_persistent] = [10, 11].map(|i| {
            block.rws[step.rw_indices[i + usize::from(is_create2) + copy_rw_increase]]
                .call_context_value()
        });

        self.callee_reversion_info.assign(
            region,
            offset,
            callee_rw_counter_end_of_reversion
                .low_u64()
                .try_into()
                .unwrap(),
            callee_is_persistent.low_u64() != 0,
        )?;

        let [caller_balance_pair, callee_balance_pair] = [13, 14].map(|i| {
            block.rws[step.rw_indices[i + usize::from(is_create2) + copy_rw_increase]]
                .account_value_pair()
        });
        self.transfer.assign(
            region,
            offset,
            caller_balance_pair,
            callee_balance_pair,
            value,
        )?;

        let (_next_memory_word_size, memory_expansion_gas_cost) = self.memory_expansion.assign(
            region,
            offset,
            step.memory_word_size(),
            [init_code_address],
        )?;

        let (init_code_word_size, _remainder) = self.init_code_word_size.assign(
            region,
            offset,
            (31u64 + init_code_length.as_u64()).into(),
        )?;

        self.gas_left.assign(
            region,
            offset,
            (step.gas_left
                - GasCost::CREATE.as_u64()
                - memory_expansion_gas_cost
                - if is_create2 {
                    u64::try_from(init_code_word_size).unwrap() * GasCost::COPY_SHA3.as_u64()
                } else {
                    0
                })
            .into(),
        )?;

        self.callee_is_success.assign(
            region,
            offset,
            Value::known(
                block.rws[step.rw_indices[22 + usize::from(is_create2) + copy_rw_increase]]
                    .call_context_value()
                    .to_scalar()
                    .unwrap(),
            ),
        )?;

        let keccak_input: Vec<u8> = if is_create2 {
            once(0xffu8)
                .chain(call.callee_address.to_fixed_bytes())
                .chain(salt.to_be_bytes())
                .chain(keccak256(&values))
                .collect()
        } else {
            let mut stream = ethers_core::utils::rlp::RlpStream::new();
            stream.begin_list(2);
            stream.append(&call.callee_address);
            stream.append(&U256::from(caller_nonce));
            stream.out().to_vec()
        };
        let mut keccak_output = keccak256(&keccak_input);
        keccak_output.reverse();

        self.keccak_output
            .assign(region, offset, Some(keccak_output))?;

        let mut code_hash = keccak256(&values);
        code_hash.reverse();
        self.create.assign(
            region,
            offset,
            call.callee_address,
            caller_nonce,
            Some(U256::from_big_endian(&code_hash)),
            Some(salt),
        )?;

        Ok(())
    }
}
