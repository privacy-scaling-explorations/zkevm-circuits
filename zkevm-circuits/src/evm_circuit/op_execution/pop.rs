//use crate::evm_circuit::{FixedLookup, Lookup};
use super::super::{Case, Cell, Constraint, ExecutionStep};
use super::{
    CaseAllocation, CaseConfig, OpExecutionState, CoreStateInstance,
    OpGadget
};
use halo2::plonk::Error;
use halo2::{arithmetic::FieldExt, circuit::Region, plonk::Expression};
use std::convert::TryInto;

#[derive(Clone, Debug)]
struct PopSuccessAllocation<F> {
    case_selector: Cell<F>,
    // word: Word<F>,
    // selector: Cell<F>
}

#[derive(Clone, Debug)]
pub struct PopGadget<F> {
    success: PopSuccessAllocation<F>,
    stack_underflow: Cell<F>, // case selector
    out_of_gas: (
        Cell<F>, // case selector
        Cell<F>, // gas available
    ),
}

impl<F: FieldExt> OpGadget<F> for PopGadget<F> {
    const RESPONSIBLE_OPCODES: &'static [u8] = &[
        80 // 0x50 of op id
    ];

    const CASE_CONFIGS: &'static [CaseConfig] = &[
        CaseConfig {
            case: Case::Success,
            num_word: 0,// no operand required for pop 
            num_cell: 0, 
            will_resume: false,
        },
        CaseConfig {
            case: Case::StackUnderflow,
            num_word: 0,
            num_cell: 0,
            will_resume: true,
        },
        CaseConfig {
            case: Case::OutOfGas,
            num_word: 0,
            num_cell: 0,
            will_resume: true,
        },
    ];

    fn construct(case_allocations: Vec<CaseAllocation<F>>) -> Self {
        let [ success, stack_underflow, out_of_gas]: [CaseAllocation<F>; 3] =
            case_allocations.try_into().unwrap();
        Self {
            success: PopSuccessAllocation {
                case_selector: success.selector.clone(),
                // no more for pop
            },
            stack_underflow: stack_underflow.selector.clone(),
            out_of_gas: (
                out_of_gas.selector.clone(),
                out_of_gas.resumption.unwrap().gas_available.clone(),
            ),
        }
    }

    fn constraints(
        &self,
        op_execution_state_curr: &OpExecutionState<F>,
        op_execution_state_next: &OpExecutionState<F>,
    ) -> Vec<Constraint<F>> {
        let pop = Expression::Constant(F::from_u64(80));
        let OpExecutionState { opcode, .. } = &op_execution_state_curr;
        let common_polys = vec![(opcode.expr() - pop.clone())];
        
        let success = {
            // interpreter state transition constraints
            let op_execution_state_transition_constraints = vec![
                op_execution_state_next.global_counter.expr()
                    - (op_execution_state_curr.global_counter.expr()
                        + Expression::Constant(F::from_u64(1))),
                op_execution_state_next.stack_pointer.expr()
                    - (op_execution_state_curr.stack_pointer.expr()
                        + Expression::Constant(F::from_u64(1))),
                op_execution_state_next.program_counter.expr()
                    - (op_execution_state_curr.program_counter.expr()
                        + Expression::Constant(F::from_u64(1))),
                op_execution_state_next.gas_counter.expr()
                    - (op_execution_state_curr.gas_counter.expr()
                        + Expression::Constant(F::from_u64(2))),
            ];

            let PopSuccessAllocation {
                case_selector,
                // word,
                // selector,
            } = &self.success;

            // TODO: consider more about pop constraint ?

            Constraint {
                name: "PopGadget success",
                selector: case_selector.expr(),
                polys: [
                    common_polys.clone(),
                    op_execution_state_transition_constraints,
                ]
                .concat(),
                lookups: vec![] //[byte_range_lookup, bus_mapping_lookups].concat()]
            }
        };

        let stack_underflow = {
            let (zero, minus_one) = (
                Expression::Constant(F::from_u64(1024)),
                Expression::Constant(F::from_u64(1023)),
            );
            let stack_pointer = op_execution_state_curr.stack_pointer.expr();
            Constraint {
                name: "PopGadget stack underflow",
                selector: self.stack_underflow.expr(),
                polys: vec![
                    common_polys.clone(),
                     vec![
                        (stack_pointer.clone() - zero)
                            * (stack_pointer - minus_one),
                    ],
                ]
                .concat(),
                lookups: vec![],
            }
        };

        let out_of_gas = {
            let (one, two, three) = (
                Expression::Constant(F::from_u64(1)),
                Expression::Constant(F::from_u64(2)),
                Expression::Constant(F::from_u64(3)),
            );
            let (case_selector, gas_available) = &self.out_of_gas;
            let gas_overdemand = op_execution_state_curr.gas_counter.expr()
                + three.clone()
                - gas_available.expr();
            Constraint {
                name: "PopGadget out of gas",
                selector: case_selector.expr(),
                polys: [
                    common_polys,
                    vec![
                        (gas_overdemand.clone() - one)
                            * (gas_overdemand.clone() - two)
                            * (gas_overdemand - three),
                    ],
                ]
                .concat(),
                lookups: vec![],
            }
        };

        vec![success,stack_underflow, out_of_gas]
    }

    fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        op_execution_state: &mut CoreStateInstance,
        execution_step: &ExecutionStep,
    ) -> Result<(), Error> {
        match execution_step.case {
            Case::Success => self.assign_success(
                region,
                offset,
                op_execution_state,
                execution_step,
            ),
            Case::StackOverflow => {
                unimplemented!()
            }
            Case::OutOfGas => {
                unimplemented!()
            }
            _ => unreachable!(),
        }
    }
}

impl<F: FieldExt> PopGadget<F> {
    fn assign_success(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        op_execution_state: &mut CoreStateInstance,
        _execution_step: &ExecutionStep,
    ) -> Result<(), Error> {
        op_execution_state.global_counter += 1;
        op_execution_state.program_counter += 1;
        op_execution_state.stack_pointer += 1;
        op_execution_state.gas_counter += 2;  // pop consume 2 gas point
       // no word assignments 
        
        self.success.case_selector.assign(
            region, offset, Some(F::from_u64(1))
            ).unwrap();
         Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::super::super::{test::TestCircuit, Case, ExecutionStep};
    use halo2::dev::MockProver;
    use pasta_curves::pallas::Base;

    macro_rules! try_test_circuit {
        ($execution_steps:expr, $result:expr) => {{
            let circuit = TestCircuit::<Base>::new($execution_steps);
            let prover = MockProver::<Base>::run(10, &circuit, vec![]).unwrap();
            assert_eq!(prover.verify(), $result);
        }};
    }

    // TODO: use evm word
    // TODO: add failure cases

    #[test]
    fn pop_gadget() {
        try_test_circuit!(
            vec![ExecutionStep {
                opcode: 80, // pop
                case: Case::Success,
                values: vec![],
            }],
            Ok(())
        );
    }
}
