use super::super::{
    BusMappingLookup, Case, Cell, Constraint, CoreStateInstance, ExecutionStep,
    Lookup, Word,
};
use super::{CaseAllocation, CaseConfig, OpExecutionState, OpGadget};
use bus_mapping::evm::OpcodeId;
use halo2::{
    arithmetic::FieldExt,
    circuit::Region,
    plonk::{Error, Expression},
};
use std::{array, convert::TryInto};

#[derive(Clone, Debug)]
struct AddSuccessAllocation<F> {
    selector: Cell<F>,
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
    const RESPONSIBLE_OPCODES: &'static [OpcodeId] =
        &[OpcodeId::ADD, OpcodeId::SUB];

    const CASE_CONFIGS: &'static [CaseConfig] = &[
        CaseConfig {
            case: Case::Success,
            num_word: 3,  // a + b + c
            num_cell: 33, // 32 carry + swap
            will_halt: false,
        },
        CaseConfig {
            case: Case::StackUnderflow,
            num_word: 0,
            num_cell: 0,
            will_halt: true,
        },
        CaseConfig {
            case: Case::OutOfGas,
            num_word: 0,
            num_cell: 0,
            will_halt: true,
        },
    ];

    fn construct(case_allocations: Vec<CaseAllocation<F>>) -> Self {
        let [mut success, stack_underflow, out_of_gas]: [CaseAllocation<F>; 3] =
            case_allocations.try_into().unwrap();
        Self {
            success: AddSuccessAllocation {
                selector: success.selector,
                swap: success.cells.pop().unwrap(),
                a: success.words.pop().unwrap(),
                b: success.words.pop().unwrap(),
                c: success.words.pop().unwrap(),
                carry: success.cells.try_into().unwrap(),
            },
            stack_underflow: stack_underflow.selector,
            out_of_gas: (
                out_of_gas.selector,
                out_of_gas.resumption.unwrap().gas_available,
            ),
        }
    }

    fn constraints(
        &self,
        state_curr: &OpExecutionState<F>,
        state_next: &OpExecutionState<F>,
    ) -> Vec<Constraint<F>> {
        let (add, sub) = (
            Expression::Constant(F::from_u64(1)),
            Expression::Constant(F::from_u64(3)),
        );

        let OpExecutionState { opcode, .. } = &state_curr;

        let common_polys =
            vec![(opcode.expr() - add.clone()) * (opcode.expr() - sub.clone())];

        let success = {
            let (one, expr_256) = (
                Expression::Constant(F::one()),
                Expression::Constant(F::from_u64(1 << 8)),
            );

            // interpreter state transition constraints
            let state_transition_constraints = vec![
                state_next.global_counter.expr()
                    - (state_curr.global_counter.expr()
                        + Expression::Constant(F::from_u64(3))),
                state_next.program_counter.expr()
                    - (state_curr.program_counter.expr()
                        + Expression::Constant(F::from_u64(1))),
                state_next.stack_pointer.expr()
                    - (state_curr.stack_pointer.expr()
                        + Expression::Constant(F::from_u64(1))),
                state_next.gas_counter.expr()
                    - (state_curr.gas_counter.expr()
                        + Expression::Constant(F::from_u64(3))),
            ];

            let AddSuccessAllocation {
                selector,
                swap,
                a,
                b,
                c,
                carry,
            } = &self.success;

            // swap a and c if it's SUB
            let no_swap = one - swap.expr();
            let swap_constraints = vec![
                swap.expr() * no_swap.clone(),
                swap.expr() * (opcode.expr() - sub),
                no_swap.clone() * (opcode.expr() - add),
            ];

            // add constraints
            let mut add_constraints = vec![
                (carry[0].expr() * expr_256.clone() + c.cells[0].expr())
                    - (a.cells[0].expr() + b.cells[0].expr()),
            ];
            for idx in 1..32 {
                add_constraints.push(
                    (carry[idx].expr() * expr_256.clone()
                        + c.cells[idx].expr())
                        - (a.cells[idx].expr()
                            + b.cells[idx].expr()
                            + carry[idx - 1].expr()),
                )
            }

            #[allow(clippy::suspicious_operation_groupings)]
            let bus_mapping_lookups = vec![
                Lookup::BusMappingLookup(BusMappingLookup::Stack {
                    index_offset: 0,
                    value: swap.expr() * c.expr() + no_swap.clone() * a.expr(),
                    is_write: false,
                }),
                Lookup::BusMappingLookup(BusMappingLookup::Stack {
                    index_offset: 1,
                    value: b.expr(),
                    is_write: false,
                }),
                Lookup::BusMappingLookup(BusMappingLookup::Stack {
                    index_offset: 1,
                    value: swap.expr() * a.expr() + no_swap * c.expr(),
                    is_write: true,
                }),
            ];

            Constraint {
                name: "AddGadget success",
                selector: selector.expr(),
                polys: [
                    state_transition_constraints,
                    swap_constraints,
                    add_constraints,
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
            let stack_pointer = state_curr.stack_pointer.expr();
            Constraint {
                name: "AddGadget stack underflow",
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
            let (selector, gas_available) = &self.out_of_gas;
            let gas_overdemand = state_curr.gas_counter.expr() + three.clone()
                - gas_available.expr();
            Constraint {
                name: "AddGadget out of gas",
                selector: selector.expr(),
                polys: vec![
                    (gas_overdemand.clone() - one)
                        * (gas_overdemand.clone() - two)
                        * (gas_overdemand - three),
                ],
                lookups: vec![],
            }
        };

        array::IntoIter::new([success, stack_underflow, out_of_gas])
            .map(move |mut constraint| {
                constraint.polys =
                    [common_polys.clone(), constraint.polys].concat();
                constraint
            })
            .collect()
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
                // TODO:
                unimplemented!()
            }
            Case::OutOfGas => {
                // TODO:
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
        core_state: &mut CoreStateInstance,
        execution_step: &ExecutionStep,
    ) -> Result<(), Error> {
        core_state.global_counter += 3;
        core_state.program_counter += 1;
        core_state.stack_pointer += 1;
        core_state.gas_counter += 3;

        self.success.swap.assign(
            region,
            offset,
            Some(F::from_u64((execution_step.opcode == OpcodeId::SUB) as u64)),
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
            .map(|(alloc, carry)| {
                alloc.assign(region, offset, Some(F::from_u64(*carry as u64)))
            })
            .collect::<Result<Vec<_>, _>>()?;
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
    use pasta_curves::pallas::Base;

    macro_rules! try_test_circuit {
        ($execution_steps:expr, $operations:expr, $result:expr) => {{
            let circuit =
                TestCircuit::<Base>::new($execution_steps, $operations);
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
            vec![
                ExecutionStep {
                    opcode: OpcodeId::PUSH3,
                    case: Case::Success,
                    values: vec![
                        [
                            1, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, //
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        ],
                        [
                            1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, //
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        ]
                    ],
                },
                ExecutionStep {
                    opcode: OpcodeId::PUSH3,
                    case: Case::Success,
                    values: vec![
                        [
                            4, 5, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, //
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        ],
                        [
                            1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, //
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        ]
                    ],
                },
                ExecutionStep {
                    opcode: OpcodeId::ADD,
                    case: Case::Success,
                    values: vec![
                        [
                            1, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, //
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        ],
                        [
                            4, 5, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, //
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        ],
                        [
                            5, 7, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, //
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        ],
                        [
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, //
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        ]
                    ],
                }
            ],
            vec![
                Operation {
                    gc: 1,
                    target: Target::Stack,
                    is_write: true,
                    values: [
                        Base::zero(),
                        Base::from_u64(1023),
                        Base::from_u64(1 + 2 + 3),
                        Base::zero(),
                    ]
                },
                Operation {
                    gc: 2,
                    target: Target::Stack,
                    is_write: true,
                    values: [
                        Base::zero(),
                        Base::from_u64(1022),
                        Base::from_u64(4 + 5 + 6),
                        Base::zero(),
                    ]
                },
                Operation {
                    gc: 3,
                    target: Target::Stack,
                    is_write: false,
                    values: [
                        Base::zero(),
                        Base::from_u64(1022),
                        Base::from_u64(1 + 2 + 3),
                        Base::zero(),
                    ]
                },
                Operation {
                    gc: 4,
                    target: Target::Stack,
                    is_write: false,
                    values: [
                        Base::zero(),
                        Base::from_u64(1023),
                        Base::from_u64(4 + 5 + 6),
                        Base::zero(),
                    ]
                },
                Operation {
                    gc: 5,
                    target: Target::Stack,
                    is_write: true,
                    values: [
                        Base::zero(),
                        Base::from_u64(1023),
                        Base::from_u64(5 + 7 + 9),
                        Base::zero(),
                    ]
                }
            ],
            Ok(())
        );
        // SUB
        try_test_circuit!(
            vec![
                ExecutionStep {
                    opcode: OpcodeId::PUSH3,
                    case: Case::Success,
                    values: vec![
                        [
                            5, 7, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, //
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        ],
                        [
                            1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, //
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        ]
                    ],
                },
                ExecutionStep {
                    opcode: OpcodeId::PUSH3,
                    case: Case::Success,
                    values: vec![
                        [
                            4, 5, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, //
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        ],
                        [
                            1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, //
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        ]
                    ],
                },
                ExecutionStep {
                    opcode: OpcodeId::SUB,
                    case: Case::Success,
                    values: vec![
                        [
                            1, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, //
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        ],
                        [
                            4, 5, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, //
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        ],
                        [
                            5, 7, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, //
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        ],
                        [
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, //
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        ]
                    ],
                }
            ],
            vec![
                Operation {
                    gc: 1,
                    target: Target::Stack,
                    is_write: true,
                    values: [
                        Base::zero(),
                        Base::from_u64(1023),
                        Base::from_u64(5 + 7 + 9),
                        Base::zero(),
                    ]
                },
                Operation {
                    gc: 2,
                    target: Target::Stack,
                    is_write: true,
                    values: [
                        Base::zero(),
                        Base::from_u64(1022),
                        Base::from_u64(4 + 5 + 6),
                        Base::zero(),
                    ]
                },
                Operation {
                    gc: 3,
                    target: Target::Stack,
                    is_write: false,
                    values: [
                        Base::zero(),
                        Base::from_u64(1022),
                        Base::from_u64(5 + 7 + 9),
                        Base::zero(),
                    ]
                },
                Operation {
                    gc: 4,
                    target: Target::Stack,
                    is_write: false,
                    values: [
                        Base::zero(),
                        Base::from_u64(1023),
                        Base::from_u64(4 + 5 + 6),
                        Base::zero(),
                    ]
                },
                Operation {
                    gc: 5,
                    target: Target::Stack,
                    is_write: true,
                    values: [
                        Base::zero(),
                        Base::from_u64(1023),
                        Base::from_u64(1 + 2 + 3),
                        Base::zero(),
                    ]
                }
            ],
            Ok(())
        );
    }
}
