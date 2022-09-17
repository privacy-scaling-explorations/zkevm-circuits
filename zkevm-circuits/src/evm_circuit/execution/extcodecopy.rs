use crate::{
    evm_circuit::{
        param::{N_BYTES_ACCOUNT_ADDRESS, N_BYTES_MEMORY_ADDRESS, N_BYTES_MEMORY_WORD_SIZE},
        step::ExecutionState,
        util::{
            common_gadget::SameContextGadget,
            constraint_builder::{
                ConstraintBuilder, ReversionInfo, StepStateTransition, Transition,
            },
            from_bytes,
            memory_gadget::{MemoryAddressGadget, MemoryCopierGasGadget, MemoryExpansionGadget},
            not, CachedRegion, Cell, MemoryAddress, RandomLinearCombination,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    table::{AccountFieldTag, CallContextFieldTag},
};
use bus_mapping::circuit_input_builder::CopyDataType;
use eth_types::{evm_types::GasCost, Field, ToAddress, ToLittleEndian, ToScalar};
use gadgets::util::Expr;
use halo2_proofs::{circuit::Value, plonk::Error};

use super::ExecutionGadget;

#[derive(Clone, Debug)]
pub(crate) struct ExtcodecopyGadget<F> {
    same_context: SameContextGadget<F>,
    external_address: RandomLinearCombination<F, N_BYTES_ACCOUNT_ADDRESS>,
    memory_address: MemoryAddressGadget<F>,
    data_offset: MemoryAddress<F>,
    tx_id: Cell<F>,
    reversion_info: ReversionInfo<F>,
    is_warm: Cell<F>,
    code_hash: Cell<F>,
    code_size: Cell<F>,
    copy_rwc_inc: Cell<F>,
    memory_expansion: MemoryExpansionGadget<F, 1, N_BYTES_MEMORY_WORD_SIZE>,
    memory_copier_gas: MemoryCopierGasGadget<F, { GasCost::COPY }>,
}

impl<F: Field> ExecutionGadget<F> for ExtcodecopyGadget<F> {
    const NAME: &'static str = "EXTCODECOPY";

    const EXECUTION_STATE: ExecutionState = ExecutionState::EXTCODECOPY;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        let opcode = cb.query_cell();

        let external_address = cb.query_rlc();
        let memory_offset = cb.query_cell();
        let data_offset = cb.query_rlc();
        let memory_length = cb.query_rlc();

        cb.stack_pop(external_address.expr());
        cb.stack_pop(memory_offset.expr());
        cb.stack_pop(data_offset.expr());
        cb.stack_pop(memory_length.expr());

        let memory_address = MemoryAddressGadget::construct(cb, memory_offset, memory_length);

        let tx_id = cb.call_context(None, CallContextFieldTag::TxId);
        let mut reversion_info = cb.reversion_info(None);
        let is_warm = cb.query_bool();
        cb.account_access_list_write(
            tx_id.expr(),
            from_bytes::expr(&external_address.cells),
            1.expr(),
            is_warm.expr(),
            Some(&mut reversion_info),
        );

        let code_hash = cb.query_cell();
        cb.account_read(
            from_bytes::expr(&external_address.cells),
            AccountFieldTag::CodeHash,
            code_hash.expr(),
        );
        let code_size = cb.bytecode_length(code_hash.expr());

        let memory_expansion = MemoryExpansionGadget::construct(
            cb,
            cb.curr.state.memory_word_size.expr(),
            [memory_address.address()],
        );
        let memory_copier_gas = MemoryCopierGasGadget::construct(
            cb,
            memory_address.length(),
            memory_expansion.gas_cost(),
        );
        let gas_cost = memory_copier_gas.gas_cost()
            + is_warm.expr() * GasCost::WARM_ACCESS.expr()
            + (1.expr() - is_warm.expr()) * GasCost::COLD_ACCOUNT_ACCESS.expr();

        let copy_rwc_inc = cb.query_cell();
        cb.condition(memory_address.has_length(), |cb| {
            cb.copy_table_lookup(
                code_hash.expr(),
                CopyDataType::Bytecode.expr(),
                cb.curr.state.call_id.expr(),
                CopyDataType::Memory.expr(),
                from_bytes::expr(&data_offset.cells),
                code_size.expr(),
                memory_address.offset(),
                memory_address.length(),
                0.expr(),
                cb.curr.state.rw_counter.expr() + cb.rw_counter_offset().expr(),
                copy_rwc_inc.expr(),
            );
        });
        cb.condition(not::expr(memory_address.has_length()), |cb| {
            cb.require_zero(
                "if no bytes to copy, copy table rwc inc == 0",
                copy_rwc_inc.expr(),
            );
        });

        let step_state_transition = StepStateTransition {
            rw_counter: Transition::Delta(cb.rw_counter_offset() + copy_rwc_inc.expr()),
            program_counter: Transition::Delta(1.expr()),
            stack_pointer: Transition::Delta(4.expr()),
            memory_word_size: Transition::To(memory_expansion.next_memory_word_size()),
            gas_left: Transition::Delta(-gas_cost),
            ..Default::default()
        };
        let same_context = SameContextGadget::construct(cb, opcode, step_state_transition);

        Self {
            same_context,
            external_address,
            memory_address,
            data_offset,
            tx_id,
            is_warm,
            reversion_info,
            code_hash,
            code_size,
            copy_rwc_inc,
            memory_expansion,
            memory_copier_gas,
        }
    }

    fn assign_exec_step(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        block: &Block<F>,
        transaction: &Transaction,
        call: &Call,
        step: &ExecStep,
    ) -> Result<(), Error> {
        self.same_context.assign_exec_step(region, offset, step)?;

        let [external_address, memory_offset, data_offset, memory_length] =
            [0, 1, 2, 3].map(|idx| block.rws[step.rw_indices[idx]].stack_value());
        let mut le_bytes = external_address.to_address().0;
        le_bytes.reverse();
        self.external_address
            .assign(region, offset, Some(le_bytes))?;

        let memory_address = self.memory_address.assign(
            region,
            offset,
            memory_offset,
            memory_length,
            block.randomness,
        )?;
        self.data_offset.assign(
            region,
            offset,
            Some(
                data_offset.to_le_bytes()[..N_BYTES_MEMORY_ADDRESS]
                    .try_into()
                    .unwrap(),
            ),
        )?;

        self.tx_id
            .assign(region, offset, Value::known(F::from(transaction.id as u64)))?;
        self.reversion_info.assign(
            region,
            offset,
            call.rw_counter_end_of_reversion,
            call.is_persistent,
        )?;
        let is_warm = match GasCost::from(step.gas_cost) {
            GasCost::COLD_ACCOUNT_ACCESS => 0,
            GasCost::WARM_ACCESS => 1,
            _ => unreachable!(),
        };
        self.is_warm
            .assign(region, offset, Value::known(F::from(is_warm)))?;

        let code_hash = block.rws[step.rw_indices[8]]
            .table_assignment(block.randomness)
            .value;
        self.code_hash.assign(region, offset, Value::known(code_hash))?;

        let (code, _) = block.rws[step.rw_indices[8]].account_value_pair();
        let bytecode = block
            .bytecodes
            .get(&code)
            .expect("could not find external bytecode");
        self.code_size
            .assign(region, offset, Value::known(F::from(bytecode.bytes.len() as u64)))?;

        self.copy_rwc_inc.assign(
            region,
            offset,
            Value::known(
                memory_length
                    .to_scalar()
                    .expect("unexpected U256 -> Scalar conversion failure"),
            ),
        )?;

        let (_, memory_expansion_gas_cost) = self.memory_expansion.assign(
            region,
            offset,
            step.memory_word_size(),
            [memory_address],
        )?;

        self.memory_copier_gas.assign(
            region,
            offset,
            memory_length.as_u64(),
            memory_expansion_gas_cost as u64,
        )?;

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::evm_circuit::test::rand_bytes_array;
    use eth_types::{
        address, bytecode, geth_types::Account, Address, Bytecode, Bytes, ToWord, Word,
    };
    use lazy_static::lazy_static;
    use mock::TestContext;

    use crate::test_util::run_test_circuits;

    lazy_static! {
        static ref EXTERNAL_ADDRESS: Address =
            address!("0xaabbccddee000000000000000000000000000000");
    }

    fn test_ok(
        external_account: Option<Account>,
        memory_offset: usize,
        data_offset: usize,
        length: usize,
        is_warm: bool,
    ) {
        let external_address = external_account
            .as_ref()
            .map(|a| a.address)
            .unwrap_or(*EXTERNAL_ADDRESS);

        let mut code = Bytecode::default();

        if is_warm {
            code.append(&bytecode! {
                PUSH20(external_address.to_word())
                EXTCODEHASH
                POP
            });
        }
        code.append(&bytecode! {
            PUSH20(external_address.to_word())
            PUSH32(memory_offset)
            PUSH32(data_offset)
            PUSH32(length)
            #[start]
            EXTCODECOPY
            STOP
        });

        let test_ctx = TestContext::<2, 1>::new(
            None,
            |accs| {
                accs[0]
                    .address(address!("0x000000000000000000000000000000000000cafe"))
                    .code(code);

                accs[1]
                    .address(address!("0x0000000000000000000000000000000000000010"))
                    .balance(Word::from(1u64 << 20));
            },
            |mut txs, accs| {
                txs[0].to(accs[0].address).from(accs[1].address);
            },
            |block, _tx| block.number(0x1111111),
        )
        .unwrap();

        assert_eq!(run_test_circuits(test_ctx, None), Ok(()));
    }

    #[test]
    fn extcodecopy_empty_account() {
        test_ok(None, 0x00, 0x00, 0x36, true); // warm account
        test_ok(None, 0x00, 0x00, 0x36, false); // cold account
    }

    #[test]
    fn extcodecopy_nonempty_account() {
        test_ok(
            Some(Account {
                address: *EXTERNAL_ADDRESS,
                code: Bytes::from([10, 40]),
                ..Default::default()
            }),
            0x00,
            0x00,
            0x36,
            true,
        ); // warm account

        test_ok(
            Some(Account {
                address: *EXTERNAL_ADDRESS,
                code: Bytes::from([10, 40]),
                ..Default::default()
            }),
            0x00,
            0x00,
            0x36,
            false,
        ); // cold account
    }

    #[test]
    fn extcodecopy_largerthan256() {
        test_ok(
            Some(Account {
                address: *EXTERNAL_ADDRESS,
                code: Bytes::from(rand_bytes_array::<256>()),
                ..Default::default()
            }),
            0x00,
            0x00,
            0x36,
            true,
        );
        test_ok(
            Some(Account {
                address: *EXTERNAL_ADDRESS,
                code: Bytes::from(rand_bytes_array::<256>()),
                ..Default::default()
            }),
            0x00,
            0x00,
            0x36,
            false,
        );
    }

    #[test]
    fn extcodecopy_outofbound() {
        test_ok(
            Some(Account {
                address: *EXTERNAL_ADDRESS,
                code: Bytes::from(rand_bytes_array::<64>()),
                ..Default::default()
            }),
            0x00,
            0x20,
            0x104,
            true,
        );
        test_ok(
            Some(Account {
                address: *EXTERNAL_ADDRESS,
                code: Bytes::from(rand_bytes_array::<64>()),
                ..Default::default()
            }),
            0x00,
            0x20,
            0x104,
            false,
        );
    }
}
