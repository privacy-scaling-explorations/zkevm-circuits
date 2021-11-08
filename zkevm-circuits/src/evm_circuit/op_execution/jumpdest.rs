use super::super::{Case, Cell, Constraint, ExecutionStep};
use super::utils;
use super::utils::common_cases::OutOfGasCase;
use super::utils::constraint_builder::ConstraintBuilder;
use super::{
    CaseAllocation, CaseConfig, CoreStateInstance, OpExecutionState, OpGadget,
};
use crate::impl_op_gadget;
use crate::util::Expr;
use bus_mapping::evm::{GasCost, OpcodeId};
use halo2::plonk::Error;
use halo2::{arithmetic::FieldExt, circuit::Region};
use std::convert::TryInto;

const GC_DELTA: usize = 0;
const PC_DELTA: usize = 1;
const SP_DELTA: usize = 0;
const GAS: GasCost = GasCost::ONE;

impl_op_gadget!(
    [JUMPDEST]
    JumpdestGadget {
        JumpdestSuccessCase(),
        OutOfGasCase(GAS.as_usize()),
    }
);

#[derive(Clone, Debug)]
struct JumpdestSuccessCase<F> {
    case_selector: Cell<F>,
}

impl<F: FieldExt> JumpdestSuccessCase<F> {
    pub(crate) const CASE_CONFIG: &'static CaseConfig = &CaseConfig {
        case: Case::Success,
        num_word: 0,
        num_cell: 0,
        will_halt: false,
    };

    pub(crate) fn construct(alloc: &mut CaseAllocation<F>) -> Self {
        Self {
            case_selector: alloc.selector.clone(),
        }
    }

    pub(crate) fn constraint(
        &self,
        state_curr: &OpExecutionState<F>,
        state_next: &OpExecutionState<F>,
        name: &'static str,
    ) -> Constraint<F> {
        let mut cb = ConstraintBuilder::default();
        // State transitions
        utils::StateTransitions {
            gc_delta: Some(GC_DELTA.expr()),
            sp_delta: Some(SP_DELTA.expr()),
            pc_delta: Some(PC_DELTA.expr()),
            gas_delta: Some(GAS.expr()),
        }
        .constraints(&mut cb, state_curr, state_next);

        // Generate the constraint
        cb.constraint(self.case_selector.expr(), name)
    }

    fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        state: &mut CoreStateInstance,
        _step: &ExecutionStep,
    ) -> Result<(), Error> {
        state.global_counter += GC_DELTA;
        state.program_counter += PC_DELTA;
        state.stack_pointer += SP_DELTA;
        state.gas_counter += GAS.as_usize();

        self.case_selector
            .assign(region, offset, Some(F::from_u64(1)))
            .unwrap();
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::super::super::{
        test::TestCircuit, Case, ExecutionStep, Operation,
    };
    use bus_mapping::{evm::OpcodeId, operation::Target};
    use halo2::{arithmetic::FieldExt, dev::MockProver};
    use num::BigUint;
    use pasta_curves::pallas::Base;

    macro_rules! try_test_circuit {
        ($execution_steps:expr, $operations:expr, $result:expr) => {{
            let circuit =
                TestCircuit::<Base>::new($execution_steps, $operations);
            let prover = MockProver::<Base>::run(10, &circuit, vec![]).unwrap();
            assert_eq!(prover.verify(), $result);
        }};
    }

    #[test]
    fn jumpdest_gadget() {
        try_test_circuit!(
            vec![
                ExecutionStep {
                    opcode: OpcodeId::PUSH2,
                    case: Case::Success,
                    values: vec![
                        BigUint::from(0x02_03u64),
                        BigUint::from(0x01_01u64),
                    ],
                },
                ExecutionStep {
                    // jumpdest
                    opcode: OpcodeId::JUMPDEST,
                    case: Case::Success,
                    values: vec![],
                }
            ],
            vec![Operation {
                gc: 1,
                target: Target::Stack,
                is_write: true,
                values: [
                    Base::zero(),
                    Base::from_u64(1023),
                    Base::from_u64(2 + 3),
                    Base::zero(),
                ]
            }],
            Ok(())
        );
    }
}
