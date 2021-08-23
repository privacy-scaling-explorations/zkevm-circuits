use super::super::{
    BusMappingLookup, Case, Cell, Constraint, ExecutionStep, Lookup, Word,
};
use super::{
    CaseAllocation, CaseConfig, OpExecutionState, OpExecutionStateInstance,
    OpGadget,
};
use halo2::plonk::Error;
use halo2::{arithmetic::FieldExt, circuit::Region, plonk::Expression};
use std::convert::TryInto;

#[derive(Clone, Debug)]
struct AddSuccessAllocation<F> {
    case_selector: Cell<F>,
    swap: Cell<F>,
    a: Word<F>,
    b: Word<F>,
    c: Word<F>,
    carry: [Cell<F>; 32],
}

#[derive(Clone, Debug)]
pub struct AddGadget<F> {
    success: AddSuccessAllocation<F>,
    stack_underflow: Cell<F>, // case selector
    out_of_gas: (
        Cell<F>, // case selector
        Cell<F>, // gas available
    ),
}

impl<F: FieldExt> OpGadget<F> for AddGadget<F> {
    // AddGadget verifies ADD and SUB at the same time by an extra swap flag,
    // when it's ADD, we annotate stack as [a, b, ...] and [c, ...],
    // when it's SUB, we annotate stack as [c, b, ...] and [a, ...].
    // Then we verify if a + b - c is zero.
    const RESPONSIBLE_OPCODES: &'static [u8] = &[1, 3];

    const CASE_CONFIGS: &'static [CaseConfig] = &[
        CaseConfig {
            case: Case::Success,
            num_word: 3,  // a + b + c
            num_cell: 33, // 32 carry + swap
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
            success: AddSuccessAllocation {
                case_selector: success.case_selector.clone(),
                swap: success.cells[0].clone(),
                a: success.words.pop().unwrap(),
                b: success.words.pop().unwrap(),
                c: success.words.pop().unwrap(),
                carry: success.cells[1..].to_owned().try_into().unwrap(),
            },
            stack_underflow: stack_underflow.case_selector.clone(),
            out_of_gas: (
                out_of_gas.case_selector.clone(),
                out_of_gas.resumption.unwrap().gas_available.clone(),
            ),
        }
    }

    fn constraints(
        &self,
        op_execution_state_curr: &OpExecutionState<F>,
        op_execution_state_next: &OpExecutionState<F>,
    ) -> Vec<Constraint<F>> {
        let (add, sub) = (
            Expression::Constant(F::from_u64(1)),
            Expression::Constant(F::from_u64(3)),
        );
        let opcode = op_execution_state_curr.opcode.exp();

        let common = {
            Constraint {
                name: "AddGadget common",
                selector: Expression::Constant(F::one()),
                linear_combinations: vec![
                    (opcode.clone() - add.clone())
                        * (opcode.clone() - sub.clone()),
                ],
                lookups: vec![],
            }
        };

        let success = {
            let (one, exp_256) = (
                Expression::Constant(F::one()),
                Expression::Constant(F::from_u64(1 << 8)),
            );

            // interpreter state transition constraints
            let op_execution_state_transition_constraints = vec![
                op_execution_state_next.global_counter.exp()
                    - (op_execution_state_curr.global_counter.exp()
                        + Expression::Constant(F::from_u64(3))),
                op_execution_state_next.stack_pointer.exp()
                    - (op_execution_state_curr.stack_pointer.exp()
                        + Expression::Constant(F::from_u64(1))),
                op_execution_state_next.program_counter.exp()
                    - (op_execution_state_curr.program_counter.exp()
                        + Expression::Constant(F::from_u64(1))),
                op_execution_state_next.gas_counter.exp()
                    - (op_execution_state_curr.gas_counter.exp()
                        + Expression::Constant(F::from_u64(3))),
            ];

            let AddSuccessAllocation {
                case_selector,
                swap,
                a,
                b,
                c,
                carry,
            } = &self.success;

            // swap a and c if it's SUB
            let no_swap = one - swap.exp();
            let swap_constraints = vec![
                swap.exp() * no_swap.clone(),
                swap.exp() * (opcode.clone() - sub),
                no_swap.clone() * (opcode - add),
            ];

            // add constraints
            let mut add_constraints = vec![
                (carry[0].exp() * exp_256.clone() + c.cells[0].exp())
                    - (a.cells[0].exp() + b.cells[0].exp()),
            ];
            for idx in 1..32 {
                add_constraints.push(
                    (carry[idx].exp() * exp_256.clone() + c.cells[idx].exp())
                        - (a.cells[idx].exp()
                            + b.cells[idx].exp()
                            + carry[idx - 1].exp()),
                )
            }

            #[allow(clippy::suspicious_operation_groupings)]
            Constraint {
                name: "AddGadget success",
                selector: case_selector.exp(),
                linear_combinations: [
                    op_execution_state_transition_constraints,
                    swap_constraints,
                    add_constraints,
                ]
                .concat(),
                lookups: vec![
                    Lookup::BusMappingLookup(BusMappingLookup::Stack {
                        index_offset: 1,
                        value: swap.exp() * c.exp() + no_swap.clone() * a.exp(),
                        is_write: false,
                    }),
                    Lookup::BusMappingLookup(BusMappingLookup::Stack {
                        index_offset: 2,
                        value: b.exp(),
                        is_write: false,
                    }),
                    Lookup::BusMappingLookup(BusMappingLookup::Stack {
                        index_offset: 1,
                        value: swap.exp() * a.exp() + no_swap * c.exp(),
                        is_write: true,
                    }),
                ],
            }
        };

        let stack_underflow = {
            let (zero, minus_one) = (
                Expression::Constant(F::from_u64(1024)),
                Expression::Constant(F::from_u64(1023)),
            );
            let stack_pointer = op_execution_state_curr.stack_pointer.exp();
            Constraint {
                name: "AddGadget stack underflow",
                selector: self.stack_underflow.exp(),
                linear_combinations: vec![
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
            let gas_overdemand = op_execution_state_curr.gas_counter.exp()
                + three.clone()
                - gas_available.exp();
            Constraint {
                name: "AddGadget out of gas",
                selector: case_selector.exp(),
                linear_combinations: vec![
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
        op_execution_state: &mut OpExecutionStateInstance,
        execution_step: &ExecutionStep,
    ) -> Result<(), Error> {
        match execution_step.case {
            Case::Success => self.assign_success(
                region,
                offset,
                op_execution_state,
                execution_step,
            ),
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

impl<F: FieldExt> AddGadget<F> {
    fn assign_success(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        op_execution_state: &mut OpExecutionStateInstance,
        execution_step: &ExecutionStep,
    ) -> Result<(), Error> {
        op_execution_state.global_counter += 3;
        op_execution_state.program_counter += 1;
        op_execution_state.stack_pointer += 1;
        op_execution_state.gas_counter += 3;

        self.success.swap.assign(
            region,
            offset,
            Some(F::from_u64((execution_step.opcode == 3) as u64)),
        )?;
        self.success.a.assign(
            region,
            offset,
            Some(execution_step.values[0]),
        )?;
        self.success.b.assign(
            region,
            offset,
            Some(execution_step.values[1]),
        )?;
        self.success.c.assign(
            region,
            offset,
            Some(execution_step.values[2]),
        )?;
        self.success
            .carry
            .iter()
            .zip(execution_step.values[3].iter())
            .map(|(alloc, byte)| {
                alloc.assign(region, offset, Some(F::from_u64(*byte as u64)))
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
    fn add_gadget() {
        // ADD
        try_test_circuit!(
            vec![ExecutionStep {
                opcode: 1,
                case: Case::Success,
                values: vec![
                    [
                        1, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, //
                        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    ],
                    [
                        4, 5, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, //
                        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    ],
                    [
                        5, 7, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, //
                        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    ],
                    [
                        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, //
                        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    ]
                ],
            }],
            Ok(())
        );
        // SUB
        try_test_circuit!(
            vec![ExecutionStep {
                opcode: 3,
                case: Case::Success,
                values: vec![
                    [
                        1, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, //
                        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    ],
                    [
                        4, 5, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, //
                        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    ],
                    [
                        5, 7, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, //
                        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    ],
                    [
                        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, //
                        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    ]
                ],
            }],
            Ok(())
        );
    }
}
