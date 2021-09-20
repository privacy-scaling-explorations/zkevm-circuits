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
struct LtSuccessAllocation<F> {
    selector: Cell<F>,
    // A 0/1 value. The gadget always checks if `a < b`. When the swap value is 0,
    // the gadget performs opcode LT and treats top 2 stack values as `a, b`.
    // Otherwise, the gadget performs opcode GT, and the top 2 stack values are
    // interpreted as `b, a`.
    swap: Cell<F>,
    a: Word<F>,
    b: Word<F>,
    // A 0/1 value of opcode output.
    result: Word<F>,
    // Satisfy `a + c = b` and allow overflow at 256 bit
    c: [Cell<F>; 32],
    // The carry of the addition check `a + c = b` in 128 bit chunks.
    carry: Cell<F>,
    // The sum of all limbs in `c`.
    sumc: Cell<F>,
    // The inverse of `sumc`.
    sumc_inv: Cell<F>,
}

#[derive(Clone, Debug)]
pub struct LtGadget<F> {
    success: LtSuccessAllocation<F>,
    stack_underflow: Cell<F>,
    out_of_gas: (Cell<F>, Cell<F>),
}

impl<F: FieldExt> OpGadget<F> for LtGadget<F> {
    const RESPONSIBLE_OPCODES: &'static [OpcodeId] =
        &[OpcodeId::LT, OpcodeId::GT];

    const CASE_CONFIGS: &'static [CaseConfig] = &[
        CaseConfig {
            case: Case::Success,
            num_word: 3,
            num_cell: 36, // 32 c + swap + carry + sumc + sumc_inv
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
            success: LtSuccessAllocation {
                selector: success.selector,
                swap: success.cells.pop().unwrap(),
                a: success.words.pop().unwrap(),
                b: success.words.pop().unwrap(),
                result: success.words.pop().unwrap(),
                c: success
                    .cells
                    .drain(0..32)
                    .collect::<Vec<Cell<F>>>()
                    .try_into()
                    .unwrap(),
                carry: success.cells.pop().unwrap(),
                sumc: success.cells.pop().unwrap(),
                sumc_inv: success.cells.pop().unwrap(),
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
        let OpExecutionState { opcode, .. } = &state_curr;

        let common_polys = vec![
            (opcode.expr() - OpcodeId::LT.expr())
                * (opcode.expr() - OpcodeId::GT.expr()),
        ];

        let success = {
            // interpreter state transition constraints
            let state_transition_constraints = vec![
                state_next.global_counter.expr()
                    - (state_curr.global_counter.expr() + 3.expr()),
                state_next.stack_pointer.expr()
                    - (state_curr.stack_pointer.expr() + 1.expr()),
                state_next.program_counter.expr()
                    - (state_curr.program_counter.expr() + 1.expr()),
                state_next.gas_counter.expr()
                    - (state_curr.gas_counter.expr() + GasCost::FASTEST.expr()),
            ];

            let LtSuccessAllocation {
                selector,
                swap,
                a,
                b,
                result,
                c,
                carry,
                sumc,
                sumc_inv,
            } = &self.success;

            // swap = 0/1
            // swap = 0 <=> opcode = LT
            // swap = 1 <=> opcode = GT
            let no_swap = 1.expr() - swap.expr();
            let swap_constraints = vec![
                swap.expr() * no_swap.clone(),
                swap.expr() * (opcode.expr() - OpcodeId::GT.expr()),
                no_swap.clone() * (opcode.expr() - OpcodeId::LT.expr()),
            ];

            // The sum of c limbs
            let sumc_expr =
                c.iter().fold(0.expr(), |acc, byte| acc + byte.expr());
            let sumc_is_zero_expr =
                1.expr() - sumc_expr.clone() * sumc_inv.expr();
            // same as is_zero gadget, currently we cannot use gadget inside OpGadget
            let sumc_is_zero_constraints = vec![
                sumc_expr.clone() * sumc_is_zero_expr.clone(),
                sumc_inv.expr() * sumc_is_zero_expr.clone(),
            ];
            // sumc_expr == sumc_cell
            // `result * (1 - sumc * sumc_inv) = 0`. This means `result = 1 <=> sumc_expr != 0`
            let sumc_constraints = vec![
                sumc_expr - sumc.expr(),
                result.cells[0].expr() * sumc_is_zero_expr.clone(),
            ];

            // carry = 0/1
            let mut lt_constraints =
                vec![carry.expr() * (1.expr() - carry.expr())];
            // a[15..0] + c[15..0] = carry * 256^16 + b[15..0]
            let mut exponent = 1.expr();
            let mut lhs = 0.expr();
            let mut rhs = 0.expr();
            #[allow(clippy::needless_range_loop)]
            for idx in 0..16 {
                lhs = lhs
                    + (a.cells[idx].expr() + c[idx].expr()) * exponent.clone();
                rhs = rhs + b.cells[idx].expr() * exponent.clone();
                exponent = exponent * 256.expr();
            }
            rhs = rhs + carry.expr() * exponent;
            lt_constraints.push(lhs - rhs);

            // a[31..16] + c[31..16] + carry =
            //     b[31..16] + (1 - result) * 256^16 * (1 - sumc_is_zero)
            // a < b, a + c = b, result = 1, sumc_is_zero = 0
            // a = b, a + c = b, result = 0, sumc_is_zero = 1
            // a > b, a + c = b + 2^256, result = 0, sumc_is_zero = 0
            // Note that, when result = 1, sumc != 0 is guaranteed by `sumc_constraints`,
            // and so sumc_is_zero must be 0.
            exponent = 1.expr();
            lhs = carry.expr();
            rhs = 0.expr();
            #[allow(clippy::needless_range_loop)]
            for idx in 16..32 {
                lhs = lhs
                    + (a.cells[idx].expr() + c[idx].expr()) * exponent.clone();
                rhs = rhs + b.cells[idx].expr() * exponent.clone();
                exponent = exponent * 256.expr();
            }
            rhs = rhs
                + (1.expr() - result.cells[0].expr())
                    * exponent
                    * (1.expr() - sumc_is_zero_expr);
            lt_constraints.push(lhs - rhs);

            // result[0] = 0/1, result[1..32] = 0
            let result_constraints = result
                .cells
                .iter()
                .enumerate()
                .map(|(idx, cell)| {
                    if idx == 0 {
                        cell.expr() * (1.expr() - cell.expr())
                    } else {
                        cell.expr()
                    }
                })
                .collect();

            // Check each cell in c in within 8-bit range
            let c_range_lookups = c
                .iter()
                .map(|cell| {
                    Lookup::FixedLookup(
                        FixedLookup::Range256,
                        [cell.expr(), 0.expr(), 0.expr()],
                    )
                })
                .collect();

            #[allow(clippy::suspicious_operation_groupings)]
            let bus_mapping_lookups = vec![
                Lookup::BusMappingLookup(BusMappingLookup::Stack {
                    index_offset: 0,
                    value: swap.expr() * b.expr() + no_swap.clone() * a.expr(),
                    is_write: false,
                }),
                Lookup::BusMappingLookup(BusMappingLookup::Stack {
                    index_offset: 1,
                    value: swap.expr() * a.expr() + no_swap * b.expr(),
                    is_write: false,
                }),
                Lookup::BusMappingLookup(BusMappingLookup::Stack {
                    index_offset: 1,
                    value: result.expr(),
                    is_write: true,
                }),
            ];

            Constraint {
                name: "LtGadget success",
                selector: selector.expr(),
                polys: [
                    state_transition_constraints,
                    swap_constraints,
                    sumc_constraints,
                    sumc_is_zero_constraints,
                    lt_constraints,
                    result_constraints,
                ]
                .concat(),
                lookups: [c_range_lookups, bus_mapping_lookups].concat(),
            }
        };

        let stack_underflow = {
            let stack_pointer = state_curr.stack_pointer.expr();
            Constraint {
                name: "LtGadget stack underflow",
                selector: self.stack_underflow.expr(),
                polys: vec![
                    (stack_pointer.clone() - 1024.expr())
                        * (stack_pointer - 1023.expr()),
                ],
                lookups: vec![],
            }
        };

        let out_of_gas = {
            let (selector, gas_available) = &self.out_of_gas;
            let gas_overdemand = state_curr.gas_counter.expr()
                + GasCost::FASTEST.expr()
                - gas_available.expr();
            Constraint {
                name: "LtGadget out of gas",
                selector: selector.expr(),
                polys: vec![
                    (gas_overdemand.clone() - 1.expr())
                        * (gas_overdemand.clone() - 2.expr())
                        * (gas_overdemand - 3.expr()),
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
                unimplemented!()
            }
            Case::OutOfGas => {
                unimplemented!()
            }
            _ => unreachable!(),
        }
    }
}

impl<F: FieldExt> LtGadget<F> {
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
            Some(F::from_u64((execution_step.opcode == OpcodeId::GT) as u64)),
        )?;
        self.success.a.assign(
            region,
            offset,
            Some(execution_step.values[0].to_word()),
        )?;
        self.success.b.assign(
            region,
            offset,
            Some(execution_step.values[1].to_word()),
        )?;
        self.success.result.assign(
            region,
            offset,
            Some(execution_step.values[2].to_word()),
        )?;
        self.success
            .c
            .iter()
            .zip(execution_step.values[3].to_word().iter())
            .map(|(alloc, value)| {
                alloc.assign(region, offset, Some(F::from_u64(*value as u64)))
            })
            .collect::<Result<Vec<_>, _>>()?;
        self.success.carry.assign(
            region,
            offset,
            Some(F::from_u64(
                execution_step.values[4].to_bytes_le()[0] as u64,
            )),
        )?;
        let sumc_digits = execution_step.values[5].to_u64_digits();
        let sumc = F::from_u64(if sumc_digits.is_empty() {
            0u64
        } else {
            sumc_digits[0]
        });
        let sumc_inv = sumc.invert().unwrap_or(F::zero());
        self.success.sumc.assign(region, offset, Some(sumc))?;
        self.success
            .sumc_inv
            .assign(region, offset, Some(sumc_inv))?;
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::super::super::{
        test::TestCircuit, Case, ExecutionStep, Operation,
    };
    use crate::util::ToWord;
    use bus_mapping::{evm::OpcodeId, operation::Target};
    use halo2::{arithmetic::FieldExt, dev::MockProver};
    use num::BigUint;
    use pasta_curves::pallas::Base;

    macro_rules! try_test_circuit {
        ($execution_step:expr, $operations:expr, $result:expr) => {{
            let circuit =
                TestCircuit::<Base>::new($execution_step, $operations);
            let prover = MockProver::<Base>::run(9, &circuit, vec![]).unwrap();
            assert_eq!(prover.verify(), $result);
        }};
    }

    fn subtract(a: &BigUint, b: &BigUint) -> (BigUint, BigUint, BigUint) {
        let a8s = a.to_word();
        let b8s = b.to_word();
        let mut c8s = [0u8; 32];
        let mut sub_carry: i16 = 0;
        let mut carry: u8 = 0;
        for idx in 0..32 {
            let tmp = a8s[idx] as i16 - b8s[idx] as i16 - sub_carry;
            if tmp < 0 {
                c8s[idx] = (tmp + (1 << 8)) as u8;
                sub_carry = 1;
            } else {
                c8s[idx] = tmp as u8;
                sub_carry = 0;
            }
        }
        // compute the carry
        for idx in 0..16 {
            let tmp = b8s[idx] as i16 + c8s[idx] as i16 + carry as i16;
            carry = (tmp >= (1 << 8)) as u8;
        }
        // compute the sum of all limbs in c8s
        let mut sumc: u64 = 0;
        for limb in c8s.iter() {
            sumc += *limb as u64;
        }
        (
            BigUint::from_bytes_le(&c8s),
            BigUint::from(carry),
            BigUint::from(sumc),
        )
    }

    #[test]
    fn lt_gadget() {
        let a = BigUint::from(0x03_02_01u64);
        let b = BigUint::from(0x09_07_05u64);
        let mut result = [0u8; 32];

        // LT: a < b, result = 1
        let (c, carry, sumc) = subtract(&b, &a);
        result[0] = 1;
        try_test_circuit!(
            vec![
                ExecutionStep {
                    opcode: OpcodeId::PUSH3,
                    case: Case::Success,
                    values: vec![a.clone(), BigUint::from(0x01_01_01u64)],
                },
                ExecutionStep {
                    opcode: OpcodeId::PUSH3,
                    case: Case::Success,
                    values: vec![b.clone(), BigUint::from(0x01_01_01u64)],
                },
                ExecutionStep {
                    opcode: OpcodeId::LT,
                    case: Case::Success,
                    values: vec![
                        a.clone(),
                        b.clone(),
                        BigUint::from_bytes_le(&result),
                        c,
                        carry,
                        sumc,
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
                        Base::from_u64(5 + 7 + 9),
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
                        Base::from_u64(5 + 7 + 9),
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
                        Base::from_u64(1),
                        Base::zero(),
                    ]
                }
            ],
            Ok(())
        );

        // LT: a = a, result = 0
        let (c, carry, sumc) = subtract(&a, &a);
        result[0] = 0;
        try_test_circuit!(
            vec![
                ExecutionStep {
                    opcode: OpcodeId::PUSH3,
                    case: Case::Success,
                    values: vec![a.clone(), BigUint::from(0x01_01_01u64)],
                },
                ExecutionStep {
                    opcode: OpcodeId::PUSH3,
                    case: Case::Success,
                    values: vec![a.clone(), BigUint::from(0x01_01_01u64)],
                },
                ExecutionStep {
                    opcode: OpcodeId::LT,
                    case: Case::Success,
                    values: vec![
                        a.clone(),
                        a.clone(),
                        BigUint::from_bytes_le(&result),
                        c,
                        carry,
                        sumc,
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
                        Base::from_u64(1 + 2 + 3),
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
                        Base::from_u64(1 + 2 + 3),
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
                        Base::from_u64(0),
                        Base::zero(),
                    ]
                }
            ],
            Ok(())
        );

        // LT: b > a, result = 0
        let (c, carry, sumc) = subtract(&a, &b);
        result[0] = 0;
        try_test_circuit!(
            vec![
                ExecutionStep {
                    opcode: OpcodeId::PUSH3,
                    case: Case::Success,
                    values: vec![b.clone(), BigUint::from(0x01_01_01u64)],
                },
                ExecutionStep {
                    opcode: OpcodeId::PUSH3,
                    case: Case::Success,
                    values: vec![a.clone(), BigUint::from(0x01_01_01u64)],
                },
                ExecutionStep {
                    opcode: OpcodeId::LT,
                    case: Case::Success,
                    values: vec![
                        b.clone(),
                        a.clone(),
                        BigUint::from_bytes_le(&result),
                        c,
                        carry,
                        sumc,
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
                        Base::from_u64(1 + 2 + 3),
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
                        Base::from_u64(1 + 2 + 3),
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
                        Base::from_u64(0),
                        Base::zero(),
                    ]
                }
            ],
            Ok(())
        );

        // GT: b > a, result = 1
        let (c, carry, sumc) = subtract(&b, &a);
        result[0] = 1;
        try_test_circuit!(
            vec![
                ExecutionStep {
                    opcode: OpcodeId::PUSH3,
                    case: Case::Success,
                    values: vec![b.clone(), BigUint::from(0x01_01_01u64)],
                },
                ExecutionStep {
                    opcode: OpcodeId::PUSH3,
                    case: Case::Success,
                    values: vec![a.clone(), BigUint::from(0x01_01_01u64)],
                },
                ExecutionStep {
                    opcode: OpcodeId::GT,
                    case: Case::Success,
                    values: vec![
                        a.clone(),
                        b.clone(),
                        BigUint::from_bytes_le(&result),
                        c,
                        carry,
                        sumc,
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
                        Base::from_u64(1 + 2 + 3),
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
                        Base::from_u64(1 + 2 + 3),
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
                        Base::from_u64(1),
                        Base::zero(),
                    ]
                }
            ],
            Ok(())
        );

        // GT: a = a, result = 0
        let (c, carry, sumc) = subtract(&a, &a);
        result[0] = 0;
        try_test_circuit!(
            vec![
                ExecutionStep {
                    opcode: OpcodeId::PUSH3,
                    case: Case::Success,
                    values: vec![a.clone(), BigUint::from(0x01_01_01u64)],
                },
                ExecutionStep {
                    opcode: OpcodeId::PUSH3,
                    case: Case::Success,
                    values: vec![a.clone(), BigUint::from(0x01_01_01u64)],
                },
                ExecutionStep {
                    opcode: OpcodeId::GT,
                    case: Case::Success,
                    values: vec![
                        a.clone(),
                        a.clone(),
                        BigUint::from_bytes_le(&result),
                        c,
                        carry,
                        sumc,
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
                        Base::from_u64(1 + 2 + 3),
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
                        Base::from_u64(1 + 2 + 3),
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
                        Base::from_u64(0),
                        Base::zero(),
                    ]
                }
            ],
            Ok(())
        );

        // GT: a < b, result = 0
        let (c, carry, sumc) = subtract(&a, &b);
        result[0] = 0;
        try_test_circuit!(
            vec![
                ExecutionStep {
                    opcode: OpcodeId::PUSH3,
                    case: Case::Success,
                    values: vec![a.clone(), BigUint::from(0x01_01_01u64)],
                },
                ExecutionStep {
                    opcode: OpcodeId::PUSH3,
                    case: Case::Success,
                    values: vec![b.clone(), BigUint::from(0x01_01_01u64)],
                },
                ExecutionStep {
                    opcode: OpcodeId::GT,
                    case: Case::Success,
                    values: vec![
                        b,
                        a,
                        BigUint::from_bytes_le(&result),
                        c,
                        carry,
                        sumc,
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
                        Base::from_u64(5 + 7 + 9),
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
                        Base::from_u64(5 + 7 + 9),
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
                        Base::from_u64(0),
                        Base::zero(),
                    ]
                }
            ],
            Ok(())
        );
    }
}
