use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        param::{
            N_BYTES_ACCOUNT_ADDRESS, N_BYTES_GAS, N_BYTES_MEMORY_ADDRESS, N_BYTES_MEMORY_WORD_SIZE,
            N_BYTES_U64, N_BYTES_WORD,
        },
        step::ExecutionState,
        util::{
            common_gadget::TransferGadget,
            constraint_builder::{
                ConstrainBuilderCommon, EVMConstraintBuilder, ReversionInfo, StepStateTransition,
                Transition::{Delta, To},
            },
            math_gadget::{
                ConstantDivisionGadget, ContractCreateGadget, IsZeroGadget, LtGadget, LtWordGadget,
            },
            memory_gadget::{MemoryAddressGadget, MemoryExpansionGadget},
            not, CachedRegion, Cell, Word,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    table::{AccountFieldTag, CallContextFieldTag},
    util::Expr,
};
use bus_mapping::{circuit_input_builder::CopyDataType, evm::OpcodeId, state_db::CodeDB};
use eth_types::{
    evm_types::{GasCost, INIT_CODE_WORD_GAS},
    Field, ToBigEndian, ToLittleEndian, ToScalar, U256,
};
use ethers_core::utils::keccak256;
use gadgets::util::{and, expr_from_bytes, or, select};
use halo2_proofs::{circuit::Value, plonk::Error};

use std::iter::once;

/// Gadget for CREATE and CREATE2 opcodes
#[derive(Clone, Debug)]
pub(crate) struct CreateGadget<F, const IS_CREATE2: bool, const S: ExecutionState> {
    opcode: Cell<F>,
    tx_id: Cell<F>,
    reversion_info: ReversionInfo<F>,
    depth: Cell<F>,

    is_create2: IsZeroGadget<F>,
    is_success: Cell<F>,
    was_warm: Cell<F>,
    value: Word<F>,

    caller_balance: Word<F>,
    callee_reversion_info: ReversionInfo<F>,
    callee_nonce: Cell<F>,
    prev_code_hash: Cell<F>,
    transfer: TransferGadget<F>,
    create: ContractCreateGadget<F, IS_CREATE2>,

    init_code: MemoryAddressGadget<F>,
    init_code_word_size: ConstantDivisionGadget<F, N_BYTES_MEMORY_ADDRESS>,
    init_code_rlc: Cell<F>,
    keccak_output: Word<F>,

    is_depth_in_range: LtGadget<F, N_BYTES_U64>,
    is_insufficient_balance: LtWordGadget<F>,
    is_nonce_in_range: LtGadget<F, N_BYTES_U64>,
    not_address_collision: IsZeroGadget<F>,

    memory_expansion: MemoryExpansionGadget<F, 1, N_BYTES_MEMORY_WORD_SIZE>,
    gas_left: ConstantDivisionGadget<F, N_BYTES_GAS>,
}

impl<F: Field, const IS_CREATE2: bool, const S: ExecutionState> ExecutionGadget<F>
    for CreateGadget<F, IS_CREATE2, S>
{
    const NAME: &'static str = "CREATE";

    const EXECUTION_STATE: ExecutionState = S;

    fn configure(cb: &mut EVMConstraintBuilder<F>) -> Self {
        let opcode = cb.query_cell();
        cb.opcode_lookup(opcode.expr(), 1.expr());
        cb.require_in_set(
            "Opcode is CREATE or CREATE2",
            opcode.expr(),
            vec![OpcodeId::CREATE2.expr(), OpcodeId::CREATE.expr()],
        );
        let is_create2 = IsZeroGadget::construct(cb, opcode.expr() - OpcodeId::CREATE2.expr());

        // Use rw_counter of the step which triggers next call as its call_id.
        let callee_call_id = cb.curr.state.rw_counter.clone();
        let current_call_id = cb.curr.state.call_id.clone();
        let is_success = cb.query_bool();

        // read from call context
        let tx_id = cb.call_context(None, CallContextFieldTag::TxId);
        let depth = cb.call_context(None, CallContextFieldTag::Depth);
        let mut reversion_info = cb.reversion_info_read(None);

        let keccak_output = cb.query_word_rlc();
        let create = ContractCreateGadget::construct(cb);
        let contract_addr = expr_from_bytes(&keccak_output.cells[..N_BYTES_ACCOUNT_ADDRESS]);
        let contract_addr_rlc = cb.word_rlc::<N_BYTES_ACCOUNT_ADDRESS>(
            keccak_output
                .cells
                .iter()
                .take(N_BYTES_ACCOUNT_ADDRESS)
                .map(Expr::expr)
                .collect::<Vec<_>>()
                .try_into()
                .unwrap(),
        );

        // stack operations
        let value = cb.query_word_rlc();
        let offset = cb.query_cell_phase2();
        let length = cb.query_word_rlc();
        cb.stack_pop(value.expr());
        cb.stack_pop(offset.expr());
        cb.stack_pop(length.expr());
        cb.condition(is_create2.expr(), |cb| {
            cb.stack_pop(create.salt_word_rlc(cb).expr());
        });
        cb.stack_push(is_success.expr() * contract_addr_rlc);

        // read caller's balance and nonce
        let caller_nonce = create.caller_nonce();
        let caller_balance = cb.query_word_rlc();
        cb.account_read(
            create.caller_address(),
            AccountFieldTag::Balance,
            caller_balance.expr(),
        );
        cb.account_read(
            create.caller_address(),
            AccountFieldTag::Nonce,
            caller_nonce.expr(),
        );

        // Pre-check: call depth, user's nonce and user's balance
        let is_depth_in_range = LtGadget::construct(cb, depth.expr(), 1025.expr());
        let is_insufficient_balance = LtWordGadget::construct(cb, &caller_balance, &value);
        let is_nonce_in_range = LtGadget::construct(cb, caller_nonce.expr(), u64::MAX.expr());
        let is_precheck_ok = and::expr([
            is_depth_in_range.expr(),
            not::expr(is_insufficient_balance.expr()),
            is_nonce_in_range.expr(),
        ]);

        // verify gas cost
        let init_code = MemoryAddressGadget::construct(cb, offset, length);
        let memory_expansion = MemoryExpansionGadget::construct(cb, [init_code.address()]);
        let init_code_word_size = ConstantDivisionGadget::construct(
            cb,
            init_code.length() + (N_BYTES_WORD - 1).expr(),
            N_BYTES_WORD as u64,
        );
        let keccak_gas_cost = init_code_word_size.quotient()
            * select::expr(
                is_create2.expr(),
                (INIT_CODE_WORD_GAS + GasCost::COPY_SHA3).expr(),
                INIT_CODE_WORD_GAS.expr(),
            );
        let gas_cost = GasCost::CREATE.expr() + memory_expansion.gas_cost() + keccak_gas_cost;
        let gas_remaining = cb.curr.state.gas_left.expr() - gas_cost.clone();
        let gas_left = ConstantDivisionGadget::construct(cb, gas_remaining.clone(), 64);
        let callee_gas_left = gas_remaining - gas_left.quotient();

        let was_warm = cb.query_bool();
        let init_code_rlc = cb.query_cell_phase2();
        let prev_code_hash = cb.query_cell();
        let callee_nonce = cb.query_cell();
        let not_address_collision = cb.condition(is_precheck_ok.expr(), |cb| {
            // increase caller's nonce
            cb.account_write(
                create.caller_address(),
                AccountFieldTag::Nonce,
                caller_nonce.expr() + 1.expr(),
                caller_nonce.expr(),
                Some(&mut reversion_info),
            );

            // add callee to access list
            cb.account_access_list_write(
                tx_id.expr(),
                contract_addr.clone(),
                1.expr(),
                was_warm.expr(),
                Some(&mut reversion_info),
            );

            // read contract's previous hash
            cb.account_read(
                contract_addr.clone(),
                AccountFieldTag::CodeHash,
                prev_code_hash.expr(),
            );

            // ErrContractAddressCollision, if any one of following criteria meets.
            // Nonce is not zero or account code hash is not either 0 or EMPTY_CODE_HASH.
            IsZeroGadget::construct(
                cb,
                callee_nonce.expr()
                    + prev_code_hash.expr() * (prev_code_hash.expr() - cb.empty_code_hash_rlc()),
            )
        });

        for (field_tag, value) in [
            (
                CallContextFieldTag::ProgramCounter,
                cb.curr.state.program_counter.expr() + 1.expr(),
            ),
            (
                CallContextFieldTag::StackPointer,
                cb.curr.state.stack_pointer.expr() + 2.expr() + is_create2.expr(),
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

        let mut callee_reversion_info = cb.reversion_info_write(Some(callee_call_id.expr()));
        let transfer = cb.condition(
            and::expr([is_precheck_ok.clone(), not_address_collision.expr()]),
            |cb| {
                cb.condition(init_code.has_length(), |cb| {
                    // the init code is being copied from memory to bytecode, so a copy table lookup
                    // to verify that the associated fields for the copy event.
                    cb.copy_table_lookup(
                        current_call_id.expr(),
                        CopyDataType::Memory.expr(),
                        create.code_hash_word_rlc(cb),
                        CopyDataType::Bytecode.expr(),
                        init_code.offset(),
                        init_code.address(),
                        0.expr(),             // dst_addr
                        init_code.length(),   // length
                        init_code_rlc.expr(), // rlc_acc
                        init_code.length(),   // rwc_inc
                    );
                });

                // keccak table lookup to verify contract address.
                cb.keccak_table_lookup(
                    create.input_rlc(cb),
                    create.input_length(),
                    keccak_output.expr(),
                );

                // propagate is_persistent
                cb.require_equal(
                    "callee_is_persistent == is_persistent ⋅ is_success",
                    callee_reversion_info.is_persistent(),
                    reversion_info.is_persistent() * is_success.expr(),
                );

                // transfer
                let transfer = TransferGadget::construct(
                    cb,
                    create.caller_address(),
                    contract_addr.clone(),
                    0.expr(),
                    1.expr(),
                    value.clone(),
                    &mut callee_reversion_info,
                );

                // EIP 161, the nonce of a newly created contract is 1
                cb.account_write(
                    contract_addr.clone(),
                    AccountFieldTag::Nonce,
                    1.expr(),
                    0.expr(),
                    Some(&mut callee_reversion_info),
                );

                cb.condition(init_code.has_length(), |cb| {
                    for (field_tag, value) in [
                        (CallContextFieldTag::CallerId, current_call_id.expr()),
                        (CallContextFieldTag::IsSuccess, is_success.expr()),
                        (
                            CallContextFieldTag::IsPersistent,
                            callee_reversion_info.is_persistent(),
                        ),
                        (CallContextFieldTag::TxId, tx_id.expr()),
                        (CallContextFieldTag::CallerAddress, create.caller_address()),
                        (CallContextFieldTag::CalleeAddress, contract_addr),
                        (
                            CallContextFieldTag::RwCounterEndOfReversion,
                            callee_reversion_info.rw_counter_end_of_reversion(),
                        ),
                        (CallContextFieldTag::Depth, depth.expr() + 1.expr()),
                        (CallContextFieldTag::IsRoot, false.expr()),
                        (CallContextFieldTag::IsStatic, false.expr()),
                        (CallContextFieldTag::IsCreate, true.expr()),
                        (CallContextFieldTag::CodeHash, create.code_hash_word_rlc(cb)),
                    ] {
                        cb.call_context_lookup(
                            true.expr(),
                            Some(callee_call_id.expr()),
                            field_tag,
                            value,
                        );
                    }

                    cb.require_step_state_transition(StepStateTransition {
                        rw_counter: Delta(cb.rw_counter_offset()),
                        call_id: To(callee_call_id.expr()),
                        is_root: To(false.expr()),
                        is_create: To(true.expr()),
                        code_hash: To(create.code_hash_word_rlc(cb)),
                        gas_left: To(callee_gas_left),
                        reversible_write_counter: To(
                            1.expr() + transfer.reversible_w_delta().expr()
                        ),
                        ..StepStateTransition::new_context()
                    })
                });

                // handle state transition if empty init code
                cb.condition(not::expr(init_code.has_length()), |cb| {
                    for field_tag in [
                        CallContextFieldTag::LastCalleeId,
                        CallContextFieldTag::LastCalleeReturnDataOffset,
                        CallContextFieldTag::LastCalleeReturnDataLength,
                    ] {
                        cb.call_context_lookup(true.expr(), None, field_tag, 0.expr());
                    }
                    cb.require_step_state_transition(StepStateTransition {
                        rw_counter: Delta(cb.rw_counter_offset()),
                        program_counter: Delta(1.expr()),
                        stack_pointer: Delta(2.expr() + is_create2.expr()),
                        gas_left: Delta(-gas_cost.expr()),
                        reversible_write_counter: Delta(
                            3.expr() + transfer.reversible_w_delta().expr(),
                        ),
                        ..Default::default()
                    })
                });

                transfer
            },
        );

        cb.condition(
            is_success.expr() * (1.expr() - reversion_info.is_persistent()),
            |cb| {
                cb.require_equal(
                    "callee_rw_counter_end_of_reversion == rw_counter_end_of_reversion-(reversible_write_counter + 1)",
                    callee_reversion_info.rw_counter_end_of_reversion(),
                    reversion_info.rw_counter_of_reversion(1.expr()),
                );
            },
        );

        // Handle the case where an error of ErrDepth, ErrInsufficientBalance,
        // ErrNonceUintOverflow or ErrContractAddressCollision occurred.
        cb.condition(
            or::expr([
                not::expr(is_precheck_ok),
                not::expr(not_address_collision.expr()),
            ]),
            |cb| {
                // Save caller's call state
                for field_tag in [
                    CallContextFieldTag::LastCalleeId,
                    CallContextFieldTag::LastCalleeReturnDataOffset,
                    CallContextFieldTag::LastCalleeReturnDataLength,
                ] {
                    cb.call_context_lookup(true.expr(), None, field_tag, 0.expr());
                }

                cb.require_step_state_transition(StepStateTransition {
                    rw_counter: Delta(cb.rw_counter_offset()),
                    program_counter: Delta(1.expr()),
                    stack_pointer: Delta(2.expr() + is_create2.expr()),
                    memory_word_size: To(memory_expansion.next_memory_word_size()),
                    gas_left: Delta(-gas_cost.expr()),
                    ..StepStateTransition::default()
                });
            },
        );

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
            init_code_rlc,
            memory_expansion,
            gas_left,
            init_code_word_size,
            create,
            caller_balance,
            is_depth_in_range,
            is_insufficient_balance,
            is_nonce_in_range,
            keccak_output,
            not_address_collision,
            is_success,
            prev_code_hash,
            callee_nonce,
            is_create2,
        }
    }

    fn assign_exec_step(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        block: &Block<F>,
        tx: &Transaction,
        call: &Call,
        step: &ExecStep,
    ) -> Result<(), Error> {
        let opcode = step.opcode().unwrap();
        let is_create2 = opcode == OpcodeId::CREATE2;
        self.opcode
            .assign(region, offset, Value::known(F::from(opcode.as_u64())))?;
        self.is_create2.assign(
            region,
            offset,
            F::from(opcode.as_u64()) - F::from(OpcodeId::CREATE2.as_u64()),
        )?;

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
            block.get_rws(step, 2).call_context_value().as_usize(),
            block.get_rws(step, 3).call_context_value().as_usize() != 0,
        )?;

        // 0..3 : TxId, Depth, RwCounterEndOfReversion and IsPersistent
        // stack value starts from 4
        let [value, init_code_start, init_code_length] =
            [4, 5, 6].map(|idx| block.get_rws(step, idx).stack_value());
        self.value
            .assign(region, offset, Some(value.to_le_bytes()))?;
        let salt = if is_create2 {
            block.get_rws(step, 7).stack_value()
        } else {
            U256::zero()
        };
        let rw_offset = if is_create2 { 8 } else { 7 };

        // Pre-check: call depth, user's nonce and user's balance
        let (caller_balance, _) = block.get_rws(step, rw_offset + 1).account_value_pair();
        let (caller_nonce, _) = block.get_rws(step, rw_offset + 2).account_value_pair();
        let is_precheck_ok =
            if call.depth < 1025 && caller_balance >= value && caller_nonce.as_u64() < u64::MAX {
                1
            } else {
                0
            };

        self.caller_balance
            .assign(region, offset, Some(caller_balance.to_le_bytes()))?;
        let (callee_prev_code_hash, was_warm) = if is_precheck_ok == 1 {
            let (_, was_warm) = block
                .get_rws(step, rw_offset + 4)
                .tx_access_list_value_pair();
            let (callee_prev_code_hash, _) =
                block.get_rws(step, rw_offset + 5).account_value_pair();
            (callee_prev_code_hash, was_warm)
        } else {
            (U256::from(0), false)
        };

        // 3 RWs while is_precheck_ok is true
        // account_write(caller), tx_access_list_write(callee) and  account_read(callee)
        let [callee_rw_counter_end_of_reversion, callee_is_persistent] = [
            rw_offset + 11 - (1 - is_precheck_ok) * 3,
            rw_offset + 12 - (1 - is_precheck_ok) * 3,
        ]
        .map(|i| block.get_rws(step, i).call_context_value());

        // retrieve code_hash for creating address
        let is_address_collision = !callee_prev_code_hash.is_zero();
        let code_hash_previous_rlc = if is_address_collision {
            region.code_hash(callee_prev_code_hash)
        } else {
            Value::known(F::ZERO)
        };
        self.prev_code_hash
            .assign(region, offset, code_hash_previous_rlc)?;
        self.not_address_collision.assign(
            region,
            offset,
            F::from((is_address_collision).into()),
        )?;

        // gas cost of memory expansion
        let init_code_address =
            self.init_code
                .assign(region, offset, init_code_start, init_code_length)?;
        let (_, memory_expansion_gas_cost) = self.memory_expansion.assign(
            region,
            offset,
            step.memory_word_size(),
            [init_code_address],
        )?;
        let (init_code_word_size, _) = self.init_code_word_size.assign(
            region,
            offset,
            (31u64 + init_code_length.as_u64()).into(),
        )?;
        let gas_left = step.gas_left
            - GasCost::CREATE
            - memory_expansion_gas_cost
            - u64::try_from(init_code_word_size).unwrap()
                * if is_create2 {
                    INIT_CODE_WORD_GAS + GasCost::COPY_SHA3
                } else {
                    INIT_CODE_WORD_GAS
                };
        self.gas_left.assign(region, offset, gas_left.into())?;
        self.callee_reversion_info.assign(
            region,
            offset,
            callee_rw_counter_end_of_reversion.low_u64() as usize,
            callee_is_persistent.low_u64() != 0,
        )?;

        // assign witness while pre-check is okay
        let copy_rw_increase = init_code_length.as_usize();
        let code_hash = if is_precheck_ok == 1 {
            // transfer
            let [caller_balance_pair, callee_balance_pair] = if !value.is_zero() {
                [
                    rw_offset + copy_rw_increase + 14,
                    rw_offset + copy_rw_increase + 15,
                ]
                .map(|i| block.get_rws(step, i).account_value_pair())
            } else {
                [(0.into(), 0.into()), (0.into(), 0.into())]
            };
            self.transfer.assign(
                region,
                offset,
                caller_balance_pair,
                callee_balance_pair,
                value,
            )?;

            // copy_table_lookup
            let values: Vec<_> = (rw_offset + 13..rw_offset + 13 + copy_rw_increase)
                .map(|i| block.get_rws(step, i).memory_value())
                .collect();
            let code_hash = CodeDB::hash(&values);
            let keccak_input: Vec<u8> = if is_create2 {
                once(0xffu8)
                    .chain(call.address.to_fixed_bytes())
                    .chain(salt.to_be_bytes())
                    .chain(code_hash.to_fixed_bytes())
                    .collect()
            } else {
                let mut stream = ethers_core::utils::rlp::RlpStream::new();
                stream.begin_list(2);
                stream.append(&call.address);
                stream.append(&caller_nonce);
                stream.out().to_vec()
            };
            let mut keccak_output = keccak256(keccak_input);
            keccak_output.reverse();

            self.keccak_output
                .assign(region, offset, Some(keccak_output))?;
            self.init_code_rlc.assign(
                region,
                offset,
                region.keccak_rlc(&values.iter().rev().cloned().collect::<Vec<u8>>()),
            )?;
            self.was_warm
                .assign(region, offset, Value::known(F::from(was_warm.into())))?;
            self.callee_nonce
                .assign(region, offset, Value::known(F::ZERO))?;

            code_hash
        } else {
            CodeDB::empty_code_hash()
        };

        self.create.assign(
            region,
            offset,
            call.address,
            caller_nonce.as_u64(),
            Some(U256::from(code_hash.to_fixed_bytes())),
            Some(salt),
        )?;

        // If transfer value is zero, there is no balance update
        let transfer_offset = if value.is_zero() { 2 } else { 0 };
        self.is_success.assign(
            region,
            offset,
            Value::known(if is_precheck_ok == 0 || is_address_collision {
                F::ZERO
            } else if init_code_length.as_usize() == 0 {
                F::ONE
            } else {
                block
                    .get_rws(step, 18 + rw_offset + copy_rw_increase - transfer_offset)
                    .call_context_value()
                    .to_scalar()
                    .unwrap()
            }),
        )?;

        self.is_insufficient_balance
            .assign(region, offset, caller_balance, value)?;
        self.is_depth_in_range
            .assign(region, offset, F::from(call.depth as u64), F::from(1025))?;
        self.is_nonce_in_range.assign(
            region,
            offset,
            F::from(caller_nonce.as_u64()),
            F::from(u64::MAX),
        )?;

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::test_util::CircuitTestBuilder;
    use eth_types::{
        address, bytecode, evm_types::OpcodeId, geth_types::Account, word, Address, Bytecode, Word,
    };
    use itertools::Itertools;
    use lazy_static::lazy_static;
    use mock::{eth, TestContext};

    const CALLEE_ADDRESS: Address = Address::repeat_byte(0xff);
    lazy_static! {
        static ref CALLER_ADDRESS: Address = address!("0x00bbccddee000000000000000000000000002400");
    }

    fn run_test_circuits(ctx: TestContext<2, 1>) {
        CircuitTestBuilder::new_from_test_ctx(ctx).run();
    }

    // RETURN or REVERT with a piece of random data,
    // We don't care the init code content bcs we don't really run it.
    // Here, we assign data with [0x60; 10],
    fn initialization_bytecode(is_success: bool) -> Bytecode {
        let memory_bytes = [0x60; 10];
        let memory_address = 0;
        let memory_value = Word::from_big_endian(&memory_bytes);
        let mut code = bytecode! {
            PUSH10(memory_value)
            PUSH1(memory_address)
            MSTORE
            PUSH2(5)
            PUSH2(32u64 - u64::try_from(memory_bytes.len()).unwrap())
        };
        code.write_op(if is_success {
            OpcodeId::RETURN
        } else {
            OpcodeId::REVERT
        });
        code
    }

    fn creator_bytecode(
        initialization_bytecode: Bytecode,
        value: Word,
        is_create2: bool,
        is_persistent: bool,
    ) -> Bytecode {
        let initialization_bytes = initialization_bytecode.code();
        let mut code = bytecode! {
            PUSH32(Word::from_big_endian(&initialization_bytes))
            PUSH1(0)
            MSTORE
        };
        if is_create2 {
            code.append(&bytecode! {PUSH1(45)}); // salt;
        }
        code.append(&bytecode! {
            PUSH1(initialization_bytes.len()) // size
            PUSH1(32 - initialization_bytes.len()) // length
            PUSH2(value) // value
        });
        code.write_op(if is_create2 {
            OpcodeId::CREATE2
        } else {
            OpcodeId::CREATE
        });
        if !is_persistent {
            code.append(&bytecode! {
                PUSH1(0)
                PUSH1(0)
                REVERT
            });
        }
        code
    }

    fn creator_bytecode_address_collision(initialization_bytecode: Bytecode) -> Bytecode {
        let initialization_bytes = initialization_bytecode.code();
        let mut code = bytecode! {
            PUSH32(Word::from_big_endian(&initialization_bytes))
            PUSH1(0)
            MSTORE
        };

        code.append(&bytecode! {PUSH1(45)}); // salt;
        code.append(&bytecode! {
            PUSH1(initialization_bytes.len()) // size
            PUSH1(32 - initialization_bytes.len()) // length
            PUSH2(23414) // value (endowment in CREATE2)
        });
        code.write_op(OpcodeId::CREATE2);

        // construct address collision by create2 twice
        code.append(&bytecode! {PUSH1(45)}); // salt;

        code.append(&bytecode! {
            PUSH1(initialization_bytes.len()) // size
            PUSH1(32 - initialization_bytes.len()) // length
            PUSH2(23414) // value (endowment in CREATE2)
        });
        code.write_op(OpcodeId::CREATE2);
        code.append(&bytecode! {
            PUSH1(0)
            PUSH1(0)
            REVERT
        });

        code
    }

    fn test_context(caller: Account) -> TestContext<2, 1> {
        TestContext::new(
            None,
            |accs| {
                accs[0]
                    .address(address!("0x000000000000000000000000000000000000cafe"))
                    .balance(eth(10));
                accs[1].account(&caller);
            },
            |mut txs, accs| {
                txs[0]
                    .from(accs[0].address)
                    .to(accs[1].address)
                    .gas(word!("0x2386F26FC10000"));
            },
            |block, _| block,
        )
        .unwrap()
    }

    #[test]
    fn test_create() {
        for ((is_success, is_create2), is_persistent) in [true, false]
            .iter()
            .cartesian_product(&[true, false])
            .cartesian_product(&[true, false])
        {
            let init_code = initialization_bytecode(*is_success);
            let root_code = creator_bytecode(init_code, 23414.into(), *is_create2, *is_persistent);
            let caller = Account {
                address: *CALLER_ADDRESS,
                code: root_code.into(),
                nonce: 1.into(),
                balance: eth(10),
                ..Default::default()
            };
            run_test_circuits(test_context(caller));
        }
    }

    #[test]
    fn test_create_rlp_nonce() {
        for nonce in [0, 1, 127, 128, 255, 256, 0x10000, u64::MAX - 1] {
            let caller = Account {
                address: *CALLER_ADDRESS,
                code: creator_bytecode(initialization_bytecode(true), 23414.into(), false, true)
                    .into(),
                nonce: nonce.into(),
                balance: eth(10),
                ..Default::default()
            };
            run_test_circuits(test_context(caller))
        }
    }

    #[test]
    fn test_create_empty_init_code() {
        for is_create2 in [true, false] {
            let caller = Account {
                address: *CALLER_ADDRESS,
                code: creator_bytecode(vec![].into(), 23414.into(), is_create2, true).into(),
                nonce: 10.into(),
                balance: eth(10),
                ..Default::default()
            };
            run_test_circuits(test_context(caller));
        }
    }

    #[test]
    fn test_create_overflow_offset_and_zero_size() {
        for is_create2 in [true, false] {
            let mut bytecode = bytecode! {
                PUSH1(0) // size
                PUSH32(Word::MAX) // offset
                PUSH2(23414) // value
            };
            bytecode.write_op(if is_create2 {
                OpcodeId::CREATE2
            } else {
                OpcodeId::CREATE
            });
            let caller = Account {
                address: *CALLER_ADDRESS,
                code: bytecode.into(),
                nonce: 10.into(),
                balance: eth(10),
                ..Default::default()
            };
            run_test_circuits(test_context(caller));
        }
    }

    #[test]
    fn test_create_address_collision_error() {
        let initialization_code = initialization_bytecode(false);
        let root_code = creator_bytecode_address_collision(initialization_code);
        let caller = Account {
            address: *CALLER_ADDRESS,
            code: root_code.into(),
            nonce: 1.into(),
            balance: eth(10),
            ..Default::default()
        };
        run_test_circuits(test_context(caller));
    }

    // Ignore this test case. It could run successfully but slow for CI.
    #[ignore]
    #[test]
    fn test_create_error_depth() {
        let code = bytecode! {
            PUSH1(0x20)
            PUSH1(0x0)
            PUSH1(0x0)
            CODECOPY
            PUSH1(0x20)
            PUSH1(0x0)
            PUSH1(0x0)
            CREATE
        }
        .into();
        let caller = Account {
            address: *CALLER_ADDRESS,
            code,
            nonce: 1.into(),
            balance: eth(10),
            ..Default::default()
        };
        run_test_circuits(test_context(caller));
    }

    #[test]
    fn test_create_insufficient_balance() {
        let value = 23414.into();
        for is_create2 in [true, false] {
            let caller = Account {
                address: mock::MOCK_ACCOUNTS[0],
                nonce: 1.into(),
                code: creator_bytecode(initialization_bytecode(false), value, is_create2, true)
                    .into(),
                balance: value - 1,
                ..Default::default()
            };
            run_test_circuits(test_context(caller));
        }
    }

    #[test]
    fn test_create_nonce_uint_overflow() {
        // TRICKY:
        // Caller nonce could not be set to `u64::MAX` directly. Since geth
        // [preCheck](https://github.com/ethereum/go-ethereum/blob/4a9fa31450d3cdcea84735b68cd5a0a8450473f8/core/state_transition.go#L262)
        // function has a check for nonce uint overflow. So there are two nested
        // CREATE (or CREATE2) in bytecode, which could increase nonce from
        // `u64::MAX - 1` to `u64::MAX` in the internal loop.
        for is_create2 in [true, false] {
            let init_code = initialization_bytecode(true);
            let mut root_code = creator_bytecode(init_code.clone(), 23414.into(), is_create2, true);
            root_code.append(&root_code.clone());

            // bytecodes.into_iter().for_each(|code| {
            let caller = Account {
                address: *CALLER_ADDRESS,
                code: root_code.into(),
                nonce: (u64::MAX - 1).into(),
                balance: eth(10),
                ..Default::default()
            };
            run_test_circuits(test_context(caller));
        }
    }
}
