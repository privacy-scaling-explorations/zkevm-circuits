use super::super::{
    BusMappingLookup, Case, Cell, Constraint, CoreStateInstance, ExecutionStep,
    FixedLookup, Lookup, Word,
};
use super::{CaseAllocation, CaseConfig, OpExecutionState, OpGadget};
use crate::util::{Expr, ToWord};
use bus_mapping::evm::{GasCost, OpcodeId};
use halo2::{arithmetic::FieldExt, circuit::Region, plonk::Error};
use std::{array, convert::TryInto};

#[derive(Clone, Debug)]
struct DupSuccessAllocation<F> {
    case_selector: Cell<F>,
    word: Word<F>, // target word to dup （witness）
}

#[derive(Clone, Debug)]
pub struct DupGadget<F> {
    success: DupSuccessAllocation<F>,
    stack_overflow: Cell<F>, // case selector
    stack_underflow: Cell<F>,
    out_of_gas: (
        Cell<F>, // case selector
        Cell<F>, // gas available
    ),
}

impl<F: FieldExt> OpGadget<F> for DupGadget<F> {
    const RESPONSIBLE_OPCODES: &'static [OpcodeId] = &[
        OpcodeId::DUP1,
        OpcodeId::DUP2,
        OpcodeId::DUP3,
        OpcodeId::DUP4,
        OpcodeId::DUP5,
        OpcodeId::DUP6,
        OpcodeId::DUP7,
        OpcodeId::DUP8,
        OpcodeId::DUP9,
        OpcodeId::DUP10,
        OpcodeId::DUP11,
        OpcodeId::DUP12,
        OpcodeId::DUP13,
        OpcodeId::DUP14,
        OpcodeId::DUP15,
        OpcodeId::DUP16,
    ];

    const CASE_CONFIGS: &'static [CaseConfig] = &[
        CaseConfig {
            case: Case::Success,
            num_word: 1,
            num_cell: 16, // for DUP selectors
            will_halt: false,
        },
        CaseConfig {
            case: Case::StackOverflow,
            num_word: 0,
            num_cell: 0,
            will_halt: true,
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
        let [mut success, stack_overflow, stack_underflow, out_of_gas]: [CaseAllocation<F>; 4] =
            case_allocations.try_into().unwrap();
        Self {
            success: DupSuccessAllocation {
                case_selector: success.selector.clone(),
                word: success.words.pop().unwrap(),
            },
            stack_overflow: stack_overflow.selector,
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
        let OpExecutionState { opcode, .. } = &state_curr;
        // use num_duplicated to represents 'x' value of 'dupx'
        let num_duplicated = opcode.expr() - OpcodeId::DUP1.expr() + 1.expr();
        // lookup in range 16 for dup
        let common_lookups = vec![Lookup::FixedLookup(
            FixedLookup::Range16,
            [opcode.expr() - OpcodeId::DUP1.expr(), 0.expr(), 0.expr()],
        )];

        let success = {
            // interpreter state transition constraints
            let state_transition_constraints = vec![
                state_next.global_counter.expr()
                    - (state_curr.global_counter.expr() + 2.expr()),
                state_next.program_counter.expr()
                    - (state_curr.program_counter.expr() + 1.expr()),
                // dupx contains one time push operation
                state_next.stack_pointer.expr()
                    - (state_curr.stack_pointer.expr() - 1.expr()),
                state_next.gas_counter.expr()
                    - (state_curr.gas_counter.expr() + GasCost::FASTEST.expr()),
            ];

            let DupSuccessAllocation {
                case_selector,
                word,
            } = &self.success;

            let bus_mapping_lookups = [
                // TODO: add 32 Bytecode lookups when supported
                vec![Lookup::BusMappingLookup(BusMappingLookup::Stack {
                    index_offset: num_duplicated.clone() - 1.expr(),
                    value: word.expr(),
                    is_write: false,
                })],
                vec![Lookup::BusMappingLookup(BusMappingLookup::Stack {
                    index_offset: (-1).expr(), // fixed as DUP decreases the stack pointer
                    value: word.expr(),
                    is_write: true,
                })],
            ]
            .concat();

            Constraint {
                name: "DupGadget success",
                selector: case_selector.expr(),
                polys: [state_transition_constraints].concat(),
                lookups: bus_mapping_lookups, //vec![]
            }
        };

        let stack_overflow = {
            let stack_pointer = state_curr.stack_pointer.expr();
            Constraint {
                name: "DupGadget stack overflow",
                selector: self.stack_overflow.expr(),
                polys: vec![stack_pointer],
                lookups: vec![],
            }
        };

        let stack_pointer = state_curr.stack_pointer.expr();
        let diff = num_duplicated + stack_pointer - 1025.expr();
        // diff's maxium is 15 when stack_pointer = 1024 and num_duplicated = 16,
        // the minimum is 0 when num_duplicated + stack_pointer = 1025 , i.e. stack_point = 1020, num_duplicated = 5
        let stack_underflow = {
            Constraint {
                name: "DupGadget stack underflow",
                selector: self.stack_underflow.expr(),
                polys: vec![],
                lookups: vec![Lookup::FixedLookup(
                    FixedLookup::Range16,
                    [diff, 0.expr(), 0.expr()],
                )],
            }
        };

        let out_of_gas = {
            let (one, two, three) = (1.expr(), 2.expr(), 3.expr());
            let (case_selector, gas_available) = &self.out_of_gas;
            let gas_overdemand = state_curr.gas_counter.expr()
                + GasCost::FASTEST.expr()
                - gas_available.expr();
            Constraint {
                name: "DupGadget out of gas",
                selector: case_selector.expr(),
                polys: vec![
                    (gas_overdemand.clone() - one)
                        * (gas_overdemand.clone() - two)
                        * (gas_overdemand - three),
                ],
                lookups: vec![],
            }
        };

        array::IntoIter::new([
            success,
            stack_overflow,
            stack_underflow,
            out_of_gas,
        ])
        .map(move |mut constraint| {
            constraint.lookups =
                [common_lookups.clone(), constraint.lookups].concat();
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
            Case::StackOverflow => {
                unimplemented!()
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

impl<F: FieldExt> DupGadget<F> {
    fn assign_success(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        core_state: &mut CoreStateInstance,
        execution_step: &ExecutionStep,
    ) -> Result<(), Error> {
        core_state.global_counter += 2; // read + write operation
        core_state.program_counter += 1;
        core_state.stack_pointer -= 1;
        core_state.gas_counter += 3;

        self.success.word.assign(
            region,
            offset,
            Some(execution_step.values[0].to_word()),
        )?;

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
    fn dup2_gadget() {
        try_test_circuit!(
            vec![
                ExecutionStep {
                    opcode: OpcodeId::PUSH3,
                    case: Case::Success,
                    values: vec![
                        BigUint::from(0x04_05_06u64),
                        BigUint::from(0x01_01_01u64),
                    ],
                },
                ExecutionStep {
                    opcode: OpcodeId::PUSH1,
                    case: Case::Success,
                    values: vec![
                        BigUint::from(0x03u64),
                        BigUint::from(0x01u64),
                    ],
                },
                ExecutionStep {
                    opcode: OpcodeId::DUP2, // dup2 for testing
                    case: Case::Success,
                    values: vec![BigUint::from(0x04_05_06u64)],
                },
            ],
            vec![
                Operation {
                    gc: 1,
                    target: Target::Stack,
                    is_write: true,
                    values: [
                        Base::zero(),
                        Base::from_u64(1023),
                        Base::from_u64(4 + 5 + 6),
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
                        Base::from_u64(3),
                        Base::zero(),
                    ]
                },
                Operation {
                    gc: 3,
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
                    gc: 4,
                    target: Target::Stack,
                    is_write: true,
                    values: [
                        Base::zero(),
                        Base::from_u64(1021),
                        Base::from_u64(4 + 5 + 6),
                        Base::zero(),
                    ]
                }
            ],
            Ok(())
        );
    }

    #[test]
    fn dup1_gadget() {
        try_test_circuit!(
            vec![
                ExecutionStep {
                    opcode: OpcodeId::PUSH3,
                    case: Case::Success,
                    values: vec![
                        BigUint::from(0x04_05_06u64),
                        BigUint::from(0x01_01_01u64),
                    ],
                },
                ExecutionStep {
                    opcode: OpcodeId::PUSH1,
                    case: Case::Success,
                    values: vec![
                        BigUint::from(0x03u64),
                        BigUint::from(0x01u64),
                    ],
                },
                ExecutionStep {
                    opcode: OpcodeId::DUP1, // dup1 for testing
                    case: Case::Success,
                    values: vec![BigUint::from(0x03u64)],
                },
            ],
            vec![
                Operation {
                    gc: 1,
                    target: Target::Stack,
                    is_write: true,
                    values: [
                        Base::zero(),
                        Base::from_u64(1023),
                        Base::from_u64(4 + 5 + 6),
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
                        Base::from_u64(3),
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
                        Base::from_u64(3),
                        Base::zero(),
                    ]
                },
                Operation {
                    gc: 4,
                    target: Target::Stack,
                    is_write: true,
                    values: [
                        Base::zero(),
                        Base::from_u64(1021),
                        Base::from_u64(3),
                        Base::zero(),
                    ]
                }
            ],
            Ok(())
        );
    }
}
