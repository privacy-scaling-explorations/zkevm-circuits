use crate::evm_circuit::{
    execution::ExecutionGadget,
    param::N_BYTES_MEMORY_WORD_SIZE,
    step::ExecutionState,
    util::{
        common_gadget::RestoreContextGadget,
        constraint_builder::{
            ConstraintBuilder, StepStateTransition,
            Transition::{Delta, Same},
        },
        math_gadget::CmpWordsGadget,
        CachedRegion, Cell,Word,
        memory_gadget::{MemoryExpansionGadget, MemoryAddressGadget}
    },

    witness::{Block, Call, ExecStep, Transaction},
};
use crate::table::{CallContextFieldTag, AccountFieldTag};
use crate::util::Expr;
use eth_types::{Field, ToLittleEndian};
use halo2_proofs::{circuit::Value, plonk::Error};


#[derive(Clone, Debug)]
pub(crate) struct ErrorInsufficientBalance<F> {
    opcode: Cell<F>,
    value: Word<F>,
    callee_address: Word<F>,
    gas_word: Word<F>,
    balance: Word<F>,
    cd_offset: Cell<F>,
    cd_length: Cell<F>,
    rd_offset: Cell<F>,
    rd_length: Cell<F>,
    //memory_expansion: MemoryExpansionGadget<F, 2, N_BYTES_MEMORY_WORD_SIZE>,
    is_success: Cell<F>,
    insufficient_value: CmpWordsGadget<F>,
    restore_context: RestoreContextGadget<F>,
}

impl<F: Field> ExecutionGadget<F> for ErrorInsufficientBalance<F> {
    const NAME: &'static str = "error_insufficient_balance";

    const EXECUTION_STATE: ExecutionState = ExecutionState::ErrorInsufficientBalance;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        let opcode = cb.query_cell();
        cb.opcode_lookup(opcode.expr(), 1.expr());

        // TODO: call op code check
        let balance = cb.query_word();
        // stack operations
        let gas_word = cb.query_word();
        let callee_address = cb.query_word();
        let value = cb.query_word();
        let cd_offset = cb.query_cell();
        let cd_length = cb.query_cell();
        let rd_offset = cb.query_cell();
        let rd_length = cb.query_cell();
        let is_success = cb.query_bool();

        // Lookup values from stack
        cb.stack_pop(gas_word.expr());
        cb.stack_pop(callee_address.expr());

        // `CALL` opcode has an additional stack pop `value`.
        cb.condition(1.expr(), |cb| 
            cb.stack_pop(value.expr()));
        [
            cd_offset.expr(),
            cd_length.expr(),
            rd_offset.expr(),
            rd_length.expr(),
        ]
        .map(|expression| cb.stack_pop(expression));
        cb.stack_push(is_success.expr());
    
        // compare value
        cb.account_read(callee_address.expr(), AccountFieldTag::Balance, value.expr());

        let insufficient_value = CmpWordsGadget::construct(cb,&balance, &value);
        cb.require_equal(
            "balance is less than transfer value",
            insufficient_value.clone().lt,
            1.expr(),
        );

        // error commom constraint
        // current call must be failed.
        cb.call_context_lookup(false.expr(), None, CallContextFieldTag::IsSuccess, 0.expr());
 
        // TODO: check if root call fail, to to end tx for this kind of error
        // Go to EndTx only when is_root
        // let is_to_end_tx = cb.next.execution_state_selector([ExecutionState::EndTx]);
        // cb.require_equal(
        //     "Go to EndTx only when is_root",
        //     cb.curr.state.is_root.expr(),
        //     is_to_end_tx,
        // );

        // When it's a root call
        cb.condition(cb.curr.state.is_root.expr(), |cb| {
            // Do step state transition
            cb.require_step_state_transition(StepStateTransition {
                call_id: Same,
                rw_counter: Delta(10.expr() + cb.curr.state.reversible_write_counter.expr()),
                ..StepStateTransition::any()
            });
        });

        // When it's an internal call, need to restore caller's state as finishing this
        // call. Restore caller state to next StepState
        let restore_context = cb.condition(1.expr() - cb.curr.state.is_root.expr(), |cb| {
            RestoreContextGadget::construct(
                cb,
                0.expr(),
                // rw_offset is handled in construct internally
                0.expr(),
                0.expr(),
                0.expr(),
                0.expr(),
            )
        });

        Self {
            opcode,
            value,
            callee_address,
            gas_word,
            balance,
            cd_offset,
            cd_length,
            rd_offset,
            rd_length,
            is_success,
            insufficient_value,
            restore_context,
        }
    }

    fn assign_exec_step(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        block: &Block<F>,
        _tx: &Transaction,
        call: &Call,
        step: &ExecStep,
    ) -> Result<(), Error> {
        let opcode = step.opcode.unwrap();
      
        let [gas, callee_address, value, cd_offset, cd_length, rd_offset, rd_length, is_success] = [
            step.rw_indices[0],
            step.rw_indices[1],
            step.rw_indices[2],
            step.rw_indices[3],
            step.rw_indices[4],
            step.rw_indices[5],
            step.rw_indices[6],
            step.rw_indices[7],
        ]
        .map(|idx| block.rws[idx].stack_value());

        let (balance, _ )=  block.rws[step.rw_indices[8]].account_value_pair();
        self.opcode
            .assign(region, offset, Value::known(F::from(opcode.as_u64())))?;
        self.value.assign(region, offset, Some(value.to_le_bytes()))?;
        self.callee_address.assign(region, offset, Some(callee_address.to_le_bytes()))?;
        self.gas_word.assign(region, offset, Some(gas.to_le_bytes()))?;
        let cd_offset_rlc = Word::random_linear_combine(cd_offset.to_le_bytes(), block.randomness);
        self.cd_offset.assign(region, offset, Value::known(cd_offset_rlc))?;
        let cd_length_rlc = Word::random_linear_combine(cd_length.to_le_bytes(), block.randomness);
        self.cd_length.assign(region, offset, Value::known(cd_length_rlc))?;

        let rd_offset_rlc = Word::random_linear_combine(rd_offset.to_le_bytes(), block.randomness);
        self.rd_offset.assign(region, offset, Value::known(rd_offset_rlc))?;
        let rd_length_rlc = Word::random_linear_combine(rd_length.to_le_bytes(), block.randomness);
        self.rd_length.assign(region, offset, Value::known(rd_length_rlc))?;
        self.is_success
        .assign(region, offset, Value::known(F::from(is_success.low_u64())))?;

        // restore_context,
        // Inputs/Outputs
        self.balance
            .assign(region, offset, Some(balance.to_le_bytes()))?;
   
        self.insufficient_value.assign(
            region,
            offset,
            balance,
            value,
        )?;

        self.restore_context
            .assign(region, offset, block, call, step, 10)?;

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::evm_circuit::{
        test::run_test_circuit_geth_data, test::run_test_circuit_geth_data_default, witness::block_convert,
    };
    use bus_mapping::evm::OpcodeId;
    use bus_mapping::circuit_input_builder::CircuitsParams;
    use eth_types::{
        self, address, bytecode, bytecode::Bytecode, evm_types::GasCost, geth_types::Account,
        geth_types::GethData, Address, ToWord, Word,
    };
    use halo2_proofs::halo2curves::bn256::Fr;

    use mock::{
        eth, gwei, test_ctx::helpers::account_0_code_account_1_no_code, TestContext, MOCK_ACCOUNTS,
    };
    use itertools::Itertools;


    fn test_ok(caller: Account, callee: Account) {
        let block: GethData = TestContext::<3, 1>::new(
            None,
            |accs| {
                accs[0]
                    .address(address!("0x000000000000000000000000000000000000cafe"))
                    .balance(Word::from(10u64.pow(19)));
                accs[1]
                    .address(caller.address)
                    .code(caller.code)
                    .nonce(caller.nonce)
                    .balance(caller.balance);
                accs[2]
                    .address(callee.address)
                    .code(callee.code)
                    .nonce(callee.nonce)
                    .balance(callee.balance);
            },
            |mut txs, accs| {
                txs[0]
                    .from(accs[0].address)
                    .to(accs[1].address)
                    .gas(100000.into());
            },
            |block, _tx| block.number(0xcafeu64),
        )
        .unwrap()
        .into();
        assert_eq!(
            run_test_circuit_geth_data::<Fr>(
                block,
                CircuitsParams {
                    max_rws: 4500,
                    ..Default::default()
                }
            ),
            Ok(())
        );
    }


    fn caller_for_insufficient_balance(opcode: OpcodeId, stack: Stack) -> Account {
        let is_call = opcode == OpcodeId::CALL;
        let terminator = OpcodeId::STOP;

        let mut bytecode = bytecode! {
            PUSH32(Word::from(stack.rd_length))
            PUSH32(Word::from(stack.rd_offset))
            PUSH32(Word::from(stack.cd_length))
            PUSH32(Word::from(stack.cd_offset))
        };
        if is_call {
            bytecode.push(32, stack.value);
        }
        bytecode.append(&bytecode! {
            PUSH32(Address::repeat_byte(0xff).to_word())
            PUSH32(Word::from(stack.gas))
            .write_op(opcode)
            .write_op(terminator)
        });

        Account {
            address: Address::repeat_byte(0xfe),
            balance: Word::from(10).pow(18.into()),
            code: bytecode.to_vec().into(),
            ..Default::default()
        }
    }

    #[derive(Clone, Copy, Debug, Default)]
    struct Stack {
        gas: u64,
        value: Word,
        cd_offset: u64,
        cd_length: u64,
        rd_offset: u64,
        rd_length: u64,
    }

    fn callee(code: Bytecode) -> Account {
        let code = code.to_vec();
        let is_empty = code.is_empty();
        Account {
            address: Address::repeat_byte(0xff),
            code: code.into(),
            nonce: if is_empty { 0 } else { 1 }.into(),
            balance: if is_empty { 0 } else { 0xdeadbeefu64 }.into(),
            ..Default::default()
        }
    }

    #[test]
    fn callop_insufficient_balance() {
        let opcodes = [OpcodeId::CALL];
        let stacks = [Stack {
            // this value is bigger than caller's balance
            value: Word::from(11).pow(18.into()),
            ..Default::default()
        }];
        let callees = [callee(bytecode! {}), callee(bytecode! { STOP })];
        for ((opcode, stack), callee) in opcodes
            .into_iter()
            .cartesian_product(stacks.into_iter())
            .cartesian_product(callees.into_iter())
        {
            test_ok(caller_for_insufficient_balance(opcode, stack), callee);
        }
    }

   }
