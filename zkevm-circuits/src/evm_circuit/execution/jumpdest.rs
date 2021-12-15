use crate::{
    evm_circuit::{
        execution::{
            bus_mapping_tmp::{Block, Call, ExecStep, Transaction},
            ExecutionGadget,
        },
        step::ExecutionState,
        util::{
            common_gadget::SameContextGadget,
            constraint_builder::{
                ConstraintBuilder, StepStateTransition, Transition::Delta,
            },
        },
    },
    util::Expr,
};
use halo2::{arithmetic::FieldExt, circuit::Region, plonk::Error};

#[derive(Clone, Debug)]
pub(crate) struct JumpdestGadget<F> {
    same_context: SameContextGadget<F>,
}

impl<F: FieldExt> ExecutionGadget<F> for JumpdestGadget<F> {
    const NAME: &'static str = "JUMPDEST";

    const EXECUTION_STATE: ExecutionState = ExecutionState::JUMPDEST;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        // State transition
        let step_state_transition = StepStateTransition {
            program_counter: Delta(1.expr()),
            ..Default::default()
        };
        let opcode = cb.query_cell();
        let same_context = SameContextGadget::construct(
            cb,
            opcode,
            step_state_transition,
            None,
        );

        Self { same_context }
    }

    fn assign_exec_step(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        _: &Block<F>,
        _: &Transaction<F>,
        _: &Call<F>,
        step: &ExecStep,
    ) -> Result<(), Error> {
        self.same_context.assign_exec_step(region, offset, step)
    }
}

#[cfg(test)]
mod test {
    use crate::evm_circuit::{
        execution::bus_mapping_tmp::{
            Block, Bytecode, Call, ExecStep, Transaction,
        },
        step::ExecutionState,
        test::run_test_circuit_incomplete_fixed_table,
        util::RandomLinearCombination,
    };
    use bus_mapping::{eth_types::ToLittleEndian, evm::OpcodeId};
    use halo2::arithmetic::BaseExt;
    use pairing::bn256::Fr as Fp;

    fn test_ok() {
        let opcode = OpcodeId::JUMPDEST;
        let randomness = Fp::rand();
        let bytecode =
            Bytecode::new(vec![opcode.as_u8(), OpcodeId::STOP.as_u8()]);
        let block = Block {
            randomness,
            txs: vec![Transaction {
                calls: vec![Call {
                    id: 1,
                    is_root: false,
                    is_create: false,
                    opcode_source:
                        RandomLinearCombination::random_linear_combine(
                            bytecode.hash.to_le_bytes(),
                            randomness,
                        ),
                }],
                steps: vec![
                    ExecStep {
                        rw_indices: vec![],
                        execution_state: ExecutionState::JUMPDEST,
                        rw_counter: 1,
                        program_counter: 0,
                        stack_pointer: 1024,
                        gas_left: 3,
                        gas_cost: 1,
                        opcode: Some(opcode),
                        ..Default::default()
                    },
                    ExecStep {
                        execution_state: ExecutionState::STOP,
                        rw_counter: 1,
                        program_counter: 1,
                        stack_pointer: 1024,
                        gas_left: 2,
                        opcode: Some(OpcodeId::STOP),
                        ..Default::default()
                    },
                ],
                ..Default::default()
            }],
            rws: vec![],
            bytecodes: vec![bytecode],
        };
        assert_eq!(run_test_circuit_incomplete_fixed_table(block), Ok(()));
    }

    #[test]
    fn jumpdest_gadget_simple() {
        test_ok();
    }
}
