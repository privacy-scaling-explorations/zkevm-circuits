use super::super::{
    Case, Cell, Constraint, CoreStateInstance, ExecutionStep, Word,
};
use super::{CaseAllocation, CaseConfig, OpExecutionState, OpGadget};
use halo2::plonk::Error;
use halo2::{arithmetic::FieldExt, circuit::Region, plonk::Expression};
use std::convert::TryInto;

#[derive(Clone, Debug)]
struct PushSuccessAllocation<F> {
    case_selector: Cell<F>,
    word: Word<F>,
    selectors: [Cell<F>; 32], /* whether its PUSH1, ..., or PUSH32 ([1, 1,
                               * 0, ..., 0] means PUSH2) */
}

#[derive(Clone, Debug)]
pub struct PushGadget<F> {
    success: PushSuccessAllocation<F>,
    stack_underflow: Cell<F>, // case selector
    out_of_gas: (
        Cell<F>, // case selector
        Cell<F>, // gas available
    ),
}

impl<F: FieldExt> OpGadget<F> for PushGadget<F> {
    const RESPONSIBLE_OPCODES: &'static [u8] = &[
        96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110,
        111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124,
        125, 126, 127,
    ];

    const CASE_CONFIGS: &'static [CaseConfig] = &[
        CaseConfig {
            case: Case::Success,
            num_word: 1,
            num_cell: 32, // for PUSH selectors
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
        let [mut success, stack_underflow, out_of_gas]: [CaseAllocation<F>; 3] =
            case_allocations.try_into().unwrap();
        Self {
            success: PushSuccessAllocation {
                case_selector: success.selector.clone(),
                word: success.words.pop().unwrap(),
                selectors: success.cells.to_owned().try_into().unwrap(),
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
        let push1 = Expression::Constant(F::from_u64(96));
        let opcode = op_execution_state_curr.opcode.expr();

        let common = {
            Constraint {
                name: "PushGadget common",
                selector: Expression::Constant(F::one()),
                polys: vec![],
                lookups: vec![], /* TODO: opcode - push1
                                  * in 1..32 */
            }
        };

        let success = {
            let one = Expression::Constant(F::one());

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
                        + opcode.clone()
                        - push1.clone()
                        + one.clone()),
                op_execution_state_next.gas_counter.expr()
                    - (op_execution_state_curr.gas_counter.expr()
                        + Expression::Constant(F::from_u64(3))),
            ];

            let PushSuccessAllocation {
                case_selector,
                word,
                selectors,
            } = &self.success;

            let mut push_constraints = vec![];
            for idx in 1..32 {
                // selector can transit from 1 to 0 only once as [1, 1, 1, ...,
                // 0, 0, 0]
                if idx > 0 {
                    let diff =
                        selectors[idx - 1].expr() - selectors[idx].expr();
                    push_constraints.push(diff.clone() * (one.clone() - diff));
                }
                // selectors needs to be 0 or 1
                push_constraints.push(
                    selectors[idx].expr()
                        * (one.clone() - selectors[idx].expr()),
                );
                // word byte should be 0 when selector is 0
                push_constraints.push(
                    word.cells[idx].expr()
                        * (one.clone() - selectors[idx].expr()),
                );
            }

            let selectors_sum = selectors
                .iter()
                .fold(Expression::Constant(F::zero()), |sum, s| sum + s.expr());
            push_constraints.push(selectors_sum - opcode + push1 - one);

            let bus_mapping_lookups = vec![/*Lookup::BusMappingLookup(BusMappingLookup::Stack {
                    index_offset: 1,
                    value: word.expr(),
                    is_write: false,
                })*/];

            Constraint {
                name: "PushGadget success",
                selector: case_selector.expr(),
                polys: [
                    op_execution_state_transition_constraints,
                    push_constraints,
                ]
                .concat(),
                lookups: bus_mapping_lookups,
            }
        };

        let stack_underflow = {
            let (zero, minus_one) = (
                Expression::Constant(F::from_u64(1024)),
                Expression::Constant(F::from_u64(1023)),
            );
            let stack_pointer = op_execution_state_curr.stack_pointer.expr();
            Constraint {
                name: "PushGadget stack underflow",
                selector: self.stack_underflow.expr(),
                polys: vec![
                    (stack_pointer.clone() - zero)
                        * (stack_pointer - minus_one),
                ],
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
                name: "PushGadget out of gas",
                selector: case_selector.expr(),
                polys: vec![
                    (gas_overdemand.clone() - one)
                        * (gas_overdemand.clone() - two)
                        * (gas_overdemand - three),
                ],
                lookups: vec![],
            }
        };

        vec![common, success, stack_underflow, out_of_gas]
    }

    fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        core_state: &mut CoreStateInstance,
        execution_step: &ExecutionStep,
    ) -> Result<(), Error> {
        match execution_step.case {
            Case::Success => {
                self.assign_success(region, offset, core_state, execution_step)
            }
            Case::StackUnderflow => {
                unimplemented!()
            }
            Case::OutOfGas => {
                unimplemented!()
            }
            _ => unreachable!(),
        }
    }
}

impl<F: FieldExt> PushGadget<F> {
    fn assign_success(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        core_state: &mut CoreStateInstance,
        execution_step: &ExecutionStep,
    ) -> Result<(), Error> {
        core_state.global_counter += 1;
        core_state.program_counter += (execution_step.opcode - 95) as usize;
        core_state.stack_pointer += 1;
        core_state.gas_counter += 3;

        self.success.word.assign(
            region,
            offset,
            Some(execution_step.values[0]),
        )?;
        self.success
            .selectors
            .iter()
            .zip(execution_step.values[1].iter())
            .map(|(alloc, bit)| {
                alloc.assign(region, offset, Some(F::from_u64(*bit as u64)))
            })
            .collect::<Result<Vec<_>, _>>()?;
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
    fn push_gadget() {
        try_test_circuit!(
            vec![ExecutionStep {
                opcode: 97, // PUSH2
                case: Case::Success,
                values: vec![
                    [
                        2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, //
                        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    ],
                    [
                        1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, //
                        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    ]
                ],
            }],
            Ok(())
        );
    }
}
