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
struct PushSuccessAllocation<F> {
    case_selector: Cell<F>,
    word: Word<F>,
    selectors: [Cell<F>; 32], /* whether its PUSH1, ..., or PUSH32 ([1, 1,
                               * 0, ..., 0] means PUSH2) */
}

#[derive(Clone, Debug)]
pub struct PushGadget<F> {
    success: PushSuccessAllocation<F>,
    stack_overflow: Cell<F>, // case selector
    out_of_gas: (
        Cell<F>, // case selector
        Cell<F>, // gas available
    ),
}

impl<F: FieldExt> OpGadget<F> for PushGadget<F> {
    const RESPONSIBLE_OPCODES: &'static [OpcodeId] = &[
        OpcodeId::PUSH1,
        OpcodeId::PUSH2,
        OpcodeId::PUSH3,
        OpcodeId::PUSH4,
        OpcodeId::PUSH5,
        OpcodeId::PUSH6,
        OpcodeId::PUSH7,
        OpcodeId::PUSH8,
        OpcodeId::PUSH9,
        OpcodeId::PUSH10,
        OpcodeId::PUSH11,
        OpcodeId::PUSH12,
        OpcodeId::PUSH13,
        OpcodeId::PUSH14,
        OpcodeId::PUSH15,
        OpcodeId::PUSH16,
        OpcodeId::PUSH17,
        OpcodeId::PUSH18,
        OpcodeId::PUSH19,
        OpcodeId::PUSH20,
        OpcodeId::PUSH21,
        OpcodeId::PUSH22,
        OpcodeId::PUSH23,
        OpcodeId::PUSH24,
        OpcodeId::PUSH25,
        OpcodeId::PUSH26,
        OpcodeId::PUSH27,
        OpcodeId::PUSH28,
        OpcodeId::PUSH29,
        OpcodeId::PUSH30,
        OpcodeId::PUSH31,
        OpcodeId::PUSH32,
    ];

    const CASE_CONFIGS: &'static [CaseConfig] = &[
        CaseConfig {
            case: Case::Success,
            num_word: 1,
            num_cell: 32, // for PUSH selectors
            will_halt: false,
        },
        CaseConfig {
            case: Case::StackOverflow,
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
        let [mut success, stack_overflow, out_of_gas]: [CaseAllocation<F>; 3] =
            case_allocations.try_into().unwrap();
        Self {
            success: PushSuccessAllocation {
                case_selector: success.selector.clone(),
                word: success.words.pop().unwrap(),
                selectors: success.cells.try_into().unwrap(),
            },
            stack_overflow: stack_overflow.selector,
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

        let common_lookups = vec![Lookup::FixedLookup(
            FixedLookup::Range32,
            [opcode.expr() - OpcodeId::PUSH1.expr(), 0.expr(), 0.expr()],
        )];

        let success = {
            let num_pushed = opcode.expr() - OpcodeId::PUSH1.expr() + 1.expr();

            // interpreter state transition constraints
            let state_transition_constraints = vec![
                state_next.global_counter.expr()
                    - (state_curr.global_counter.expr() + 1.expr()),
                state_next.program_counter.expr()
                    - (state_curr.program_counter.expr()
                        + 1.expr()
                        + num_pushed.clone()),
                state_next.stack_pointer.expr()
                    - (state_curr.stack_pointer.expr() - 1.expr()),
                state_next.gas_counter.expr()
                    - (state_curr.gas_counter.expr() + GasCost::FASTEST.expr()),
            ];

            let PushSuccessAllocation {
                case_selector,
                word,
                selectors,
            } = &self.success;

            let mut push_constraints = vec![];
            for idx in 0..31 {
                // selector can transit from 1 to 0 only once as [1, 1, 1, ...,
                // 0, 0, 0]
                if idx > 0 {
                    let diff =
                        selectors[idx - 1].expr() - selectors[idx].expr();
                    push_constraints.push(diff.clone() * (1.expr() - diff));
                }
                // selectors needs to be 0 or 1
                push_constraints.push(
                    selectors[idx].expr() * (1.expr() - selectors[idx].expr()),
                );
                // word byte should be 0 when selector is 0
                push_constraints.push(
                    word.cells[idx].expr() * (1.expr() - selectors[idx].expr()),
                );
            }

            let selectors_sum =
                selectors.iter().fold(0.expr(), |sum, s| sum + s.expr());
            push_constraints.push(selectors_sum - num_pushed);

            let bus_mapping_lookups =
                [vec![Lookup::BusMappingLookup(BusMappingLookup::Stack {
                    index_offset: -1,
                    value: word.expr(),
                    is_write: true,
                })]]
                .concat();

            Constraint {
                name: "PushGadget success",
                selector: case_selector.expr(),
                polys: [state_transition_constraints, push_constraints]
                    .concat(),
                lookups: bus_mapping_lookups,
            }
        };

        let stack_overflow = {
            let stack_pointer = state_curr.stack_pointer.expr();
            Constraint {
                name: "PushGadget stack overflow",
                selector: self.stack_overflow.expr(),
                polys: vec![stack_pointer],
                lookups: vec![],
            }
        };

        let out_of_gas = {
            let (case_selector, gas_available) = &self.out_of_gas;
            let gas_overdemand = state_curr.gas_counter.expr()
                + GasCost::FASTEST.expr()
                - gas_available.expr();
            Constraint {
                name: "PushGadget out of gas",
                selector: case_selector.expr(),
                polys: vec![
                    (gas_overdemand.clone() - 1.expr())
                        * (gas_overdemand.clone() - 2.expr())
                        * (gas_overdemand - 3.expr()),
                ],
                lookups: vec![],
            }
        };

        array::IntoIter::new([success, stack_overflow, out_of_gas])
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
        core_state.program_counter += 1
            + (execution_step.opcode.as_u8() - OpcodeId::PUSH1.as_u8() + 1)
                as usize;
        core_state.stack_pointer -= 1;
        core_state.gas_counter += 3;

        self.success.word.assign(
            region,
            offset,
            Some(execution_step.values[0].to_word()),
        )?;
        self.success
            .selectors
            .iter()
            .zip(execution_step.values[1].to_word().iter())
            .map(|(alloc, bit)| {
                alloc.assign(region, offset, Some(F::from_u64(*bit as u64)))
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

    // TODO: use evm word
    // TODO: add failure cases

    #[test]
    fn push_gadget() {
        try_test_circuit!(
            vec![ExecutionStep {
                opcode: OpcodeId::PUSH2,
                case: Case::Success,
                values: vec![
                    BigUint::from(0x02_03u64),
                    BigUint::from(0x01_01u64),
                ],
            }],
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
