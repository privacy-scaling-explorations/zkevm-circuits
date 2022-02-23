use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        step::ExecutionState,
        table::{AccountFieldTag, CallContextFieldTag},
        util::{
            common_gadget::SameContextGadget,
            constraint_builder::{ConstraintBuilder, StepStateTransition, Transition::Delta},
            Cell, Word,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    util::Expr,
};
use eth_types::{ToLittleEndian, ToScalar};
use halo2::{arithmetic::FieldExt, circuit::Region, plonk::Error};

#[derive(Clone, Debug)]
pub(crate) struct SelfbalanceGadget<F> {
    same_context: SameContextGadget<F>,
    callee_address: Cell<F>,
    self_balance: Cell<F>,
}

impl<F: FieldExt> ExecutionGadget<F> for SelfbalanceGadget<F> {
    const NAME: &'static str = "SELFBALANCE";

    const EXECUTION_STATE: ExecutionState = ExecutionState::SELFBALANCE;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        let callee_address = cb.call_context(None, CallContextFieldTag::CalleeAddress);

        let self_balance = cb.query_cell();
        cb.account_read(
            callee_address.expr(),
            AccountFieldTag::Balance,
            self_balance.expr(),
        );

        cb.stack_push(self_balance.expr());

        let opcode = cb.query_cell();
        let step_state_transition = StepStateTransition {
            rw_counter: Delta(3.expr()),
            program_counter: Delta(1.expr()),
            stack_pointer: Delta((-1).expr()),
            ..Default::default()
        };
        let same_context = SameContextGadget::construct(cb, opcode, step_state_transition, None);

        Self {
            same_context,
            self_balance,
            callee_address,
        }
    }

    fn assign_exec_step(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        block: &Block<F>,
        _: &Transaction,
        call: &Call,
        step: &ExecStep,
    ) -> Result<(), Error> {
        self.same_context.assign_exec_step(region, offset, step)?;

        self.callee_address
            .assign(region, offset, call.callee_address.to_scalar())?;

        let self_balance = block.rws[step.rw_indices[2]].stack_value();
        self.self_balance.assign(
            region,
            offset,
            Some(Word::random_linear_combine(
                self_balance.to_le_bytes(),
                block.randomness,
            )),
        )?;

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::evm_circuit::{
        step::ExecutionState,
        table::{AccountFieldTag, CallContextFieldTag, RwTableTag},
        test::run_test_circuit_incomplete_fixed_table,
        witness::{Block, Bytecode, Call, CodeSource, ExecStep, Rw, RwMap, Transaction},
    };
    use crate::test_util::run_test_circuits;
    use bus_mapping::evm::OpcodeId;
    use eth_types::{address, bytecode, ToWord, Word};
    use halo2::arithmetic::BaseExt;
    use pairing::bn256::Fr;

    #[test]
    fn selfbalance_gadget_test() {
        let bytecode = Bytecode::new(
            bytecode! {
                #[start]
                SELFBALANCE
                STOP
            }
            .to_vec(),
        );

        let self_balance = 2532312423450046u64;
        let callee_address = address!("0x000000440000000000330aa00000000440000f5e");

        let tx_id = 1;
        let call_id = 1;

        let self_balance_gas_cost = OpcodeId::SELFBALANCE.constant_gas_cost().as_u64();

        let randomness = Fr::rand();
        let block = Block {
            randomness,
            txs: vec![Transaction {
                id: tx_id,
                callee_address,
                steps: vec![
                    ExecStep {
                        execution_state: ExecutionState::SELFBALANCE,
                        rw_indices: vec![
                            (RwTableTag::CallContext, 0),
                            (RwTableTag::Account, 0),
                            (RwTableTag::Stack, 0),
                        ],
                        rw_counter: 1,
                        program_counter: 0,
                        stack_pointer: 1024,
                        gas_left: self_balance_gas_cost,
                        gas_cost: self_balance_gas_cost,
                        opcode: Some(OpcodeId::SELFBALANCE),
                        ..Default::default()
                    },
                    ExecStep {
                        execution_state: ExecutionState::STOP,
                        rw_counter: 4,
                        program_counter: 1,
                        stack_pointer: 1023,
                        opcode: Some(OpcodeId::STOP),
                        ..Default::default()
                    },
                ],
                calls: vec![Call {
                    id: 1,
                    is_root: true,
                    is_create: false,
                    callee_address,
                    code_source: CodeSource::Account(bytecode.hash),
                    ..Default::default()
                }],
                ..Default::default()
            }],
            rws: RwMap(
                [
                    (
                        RwTableTag::CallContext,
                        vec![Rw::CallContext {
                            call_id,
                            rw_counter: 1,
                            is_write: false,
                            field_tag: CallContextFieldTag::CalleeAddress,
                            value: callee_address.to_word(),
                        }],
                    ),
                    (
                        RwTableTag::Account,
                        vec![Rw::Account {
                            rw_counter: 2,
                            is_write: false,
                            account_address: callee_address,
                            field_tag: AccountFieldTag::Balance,
                            value: Word::from(self_balance),
                            value_prev: Word::from(self_balance),
                        }],
                    ),
                    (
                        RwTableTag::Stack,
                        vec![Rw::Stack {
                            call_id,
                            rw_counter: 3,
                            is_write: true,
                            stack_pointer: 1023,
                            value: Word::from(self_balance),
                        }],
                    ),
                ]
                .into(),
            ),
            bytecodes: vec![bytecode],
            ..Default::default()
        };

        assert_eq!(run_test_circuit_incomplete_fixed_table(block), Ok(()));
    }

    #[test]
    fn test_selfbalance() {
        let bytecode = bytecode! {
            #[start]
            SELFBALANCE
            STOP
        };
        assert_eq!(run_test_circuits(bytecode), Ok(()));
    }
}
