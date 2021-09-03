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
use std::convert::TryInto;

#[derive(Clone, Debug)]
struct LtSuccessAllocation<F> {
    selector: Cell<F>,
    swap: Cell<F>,
    a: Word<F>,
    b: Word<F>,
    c: Word<F>,
    carry: Cell<F>,
    sumc: Cell<F>,
    sumc_inv: Cell<F>,
    result: Cell<F>,
}

#[derive(Clone, Debug)]
pub struct LtGadget<F> {
    success: LtSuccessAllocation<F>,
    stack_underflow: Cell<F>,
    out_of_gas: (
        Cell<F>,
        Cell<F>,
    ),
}

impl<F:FieldExt> OpGadget<F> for LtGadget<F> {
    const RESPONSIBLE_OPCODES: &'static [OpcodeId] =
        &[OpcodeId::LT, OpcodeId::GT];

    const CASE_CONFIGS: &'static [CaseConfig] = &[
        CaseConfig {
            case: Case::Success,
            num_word: 3,
            num_cell: 5,//cell for carry, swap, sumc, sumc_inv, result
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
                c: success.words.pop().unwrap(),
                carry: success.cells.pop().unwrap(),
                sumc: success.cells.pop().unwrap(),
                sumc_inv: success.cells.pop().unwrap(),
                result: success.cells.pop().unwrap(),
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
        let (lt, gt) = (
            Expression::Constant(F::from_u64((OpcodeId::LT).as_u8() as u64)),
            Expression::Constant(F::from_u64((OpcodeId::GT).as_u8() as u64)),
        );

        let OpExecutionState { opcode, .. } = &state_curr;

        let common_polys =
        vec![(opcode.expr() - lt.clone()) * (opcode.expr() - gt.clone())];
        let success = {
            let (one, exp_256) = (
                Expression::Constant(F::one()),
                Expression::Constant(F::from_u64(1 << 8)),
            );
            let state_transition_constraints = vec![
                state_curr.global_counter.expr()
                    - (state_next.global_counter.expr())
                        + Expression::Constant(F::from_u64(3)),
                state_curr.stack_pointer.expr()
                    - (state_next.stack_pointer.expr())
                        + Expression::Constant(F::from_u64(1)),
                state_curr.program_counter.expr()
                    - (state_next.program_counter.expr())
                        + Expression::Constant(F::from_u64(1)),
                state_curr.gas_counter.expr()
                    - (state_next.gas_counter.expr())
                        + Expression::Constant(F::from_u64(3)),
            ];

            let LtSuccessAllocation {
                selector,
                swap,
                a,
                b,
                c,
                carry,
                sumc,
                sumc_inv,
                result,
            } = &self.success;

            let no_swap = one.clone() - swap.expr();
            let swap_constraints = vec![
                swap.expr() * no_swap.clone(),
                swap.expr() * (opcode.expr() - gt),
                no_swap.clone() * (opcode.expr() - lt),
            ];

            let mut lt_constraints = vec![];

            let mut pw_now = Expression::Constant(F::from_u64(1));
            let mut lhs = Expression::Constant(F::zero());
            let mut rhs = Expression::Constant(F::zero());
            let mut sum_c_expr = Expression::Constant(F::zero());
            for idx in 0..16 {
                lhs = lhs + (a.cells[idx].expr() + c.cells[idx].expr()) * pw_now.clone();
                rhs = rhs + b.cells[idx].expr() * pw_now.clone();
                sum_c_expr = sum_c_expr + c.cells[idx].expr();
                pw_now = pw_now *  exp_256.clone();
            }
            rhs = rhs + carry.expr() * pw_now;
            lt_constraints.push(lhs - rhs);

            pw_now = Expression::Constant(F::from_u64(1));
            lhs = carry.expr();
            rhs = Expression::Constant(F::zero());
            for idx in 16..32 {
                lhs = lhs + (a.cells[idx].expr() + c.cells[idx].expr()) * pw_now.clone();
                rhs = rhs + b.cells[idx].expr() * pw_now.clone();
                sum_c_expr = sum_c_expr + c.cells[idx].expr();
                pw_now = pw_now *  exp_256.clone();
            }
            rhs = rhs + (one.clone() - result.expr()) * pw_now * (sumc.expr() * sumc_inv.expr());
            lt_constraints.push(lhs - rhs);

            let bus_mapping_lookups = vec![
                Lookup::BusMappingLookup(BusMappingLookup::Stack {
                    index_offset: 0,
                    value: swap.expr() * b.expr() + no_swap.clone() * a.expr(),
                    is_write: false,
                }),
                Lookup::BusMappingLookup(BusMappingLookup::Stack {
                    index_offset: 1,
                    value: swap.expr() * a.expr() + no_swap.clone() * b.expr(),
                    is_write: false,
                }),
                Lookup::BusMappingLookup(BusMappingLookup::Stack {
                    index_offset: 1,
                    value: result.expr(),
                    is_write: true,
                }),
            ];

            let sum_equal_constraints = vec![sum_c_expr - sumc.expr()];

            let not_zero_constraints = vec![result.expr() * (one - sumc.expr() * sumc_inv.expr())];
            Constraint {
                name: "LtGadget success",
                selector: selector.expr(),
                polys: [
                    common_polys.clone(),
                    state_transition_constraints,
                    swap_constraints,
                    lt_constraints,
                    sum_equal_constraints,
                    not_zero_constraints,
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
                name: "LtGadget stack underflow",
                selector: self.stack_underflow.expr(),
                polys: [
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
            let (selector, gas_available) = &self.out_of_gas;
            let gas_overdemand = state_curr.gas_counter.expr() + three.clone()
                - gas_available.expr();
            Constraint {
                name: "LtGadget out of gas",
                selector: selector.expr(),
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

        vec![success, stack_underflow, out_of_gas]
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
        self.success.carry.assign(
            region,
            offset,
            Some(F::from_u64(execution_step.values[3][0] as u64)),
        )?;
        let mut sumc :u64 = 0;
        let mut pw :u64 = 1;
        for idx in 0..2 {
            sumc = sumc+ (execution_step.values[4][idx] as u64) * pw;
            pw = pw * (1 << 8);
        }
        let sumc =F::from_u64(sumc);
        self.success.sumc.assign(
            region,
            offset,
            Some(sumc),
        )?;
        self.success.sumc_inv.assign(
            region,
            offset,
            Some(sumc.invert().unwrap_or(F::zero())),
        )?;
        self.success.result.assign(
            region,
            offset,
            Some(F::from_u64(execution_step.values[5][0] as u64)),
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
    use pasta_curves::pallas::Base;

    macro_rules! try_test_circuit {
        ($execution_step:expr, $operations:expr, $result:expr) => {{
            let circuit = TestCircuit::<Base>::new($execution_step, $operations);
            let prover = MockProver::<Base>::run(9, &circuit, vec![]).unwrap();
            assert_eq!(prover.verify(), $result);
        }};
    }
    fn calc_array(
        a: [u8; 32],
        b: [u8; 32],
    ) -> ([u8; 32], [u8; 32]){
        let mut c = [0 as u8; 32];
        let mut carry = [0 as u8; 32];
        let mut pre_sub :[i16; 32] = [0 as i16; 32];
        let mut pre_add :[i16; 32] = [0 as i16; 32];
        for idx in 0..32 {
            let a_tmp = a[idx] as i16 + pre_sub[idx];
            if (b[idx] as i16 - a_tmp) < 0 {
                c[idx] = (b[idx] as i16 + (1<<8) - a_tmp) as u8;
                if idx != 31 {
                    pre_sub[idx + 1] = 1;
                }
            }
            else {
                c[idx] = (b[idx] as i16 - a_tmp) as u8;
            }
        }
        for idx in 0..16 {
            let tmp_calc = a[idx] as i16 + c[idx] as i16 + pre_add[idx];
            pre_add[idx + 1] = (tmp_calc >= (1 << 8)) as i16;
        }
        carry[0] = pre_add[16] as u8;
        (c, carry)
    }
    #[test]
    fn lt_gadget(){
        let a: [u8; 32] = [
            1, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        ];
        let b: [u8; 32] = [
            5, 7, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        ];
        let (c, carry) = calc_array(a.clone(), b.clone());
        let mut result = [0 as u8; 32];
        
        let mut sumc: u64 = 0;
        let mut sumc_array = [0 as u8; 32];
        for idx in 0..32 {
            sumc = sumc + (c[idx] as u64);
        }
        for idx in 0..32 {
            sumc_array[idx] = (sumc % (1 << 8)) as u8;
            sumc = sumc >> 8;
        }
        //passed test with result 1 for LT && GT
        result[0] = 1;
        println!("result 1 test");
        for idx in 0..32 {print!("{} ",a[idx]);}
        println!("");
        for idx in 0..32 {print!("{} ",b[idx]);}
        println!("");
        for idx in 0..32 {print!("{} ",c[idx]);}
        println!("");
        for idx in 0..32 {print!("{} ",carry[idx]);}
        println!("");
        for idx in 0..32 {print!("{} ",sumc_array[idx]);}
        println!("");
        for idx in 0..32 {print!("{} ",result[idx]);}
        println!("");
        //LT
        try_test_circuit!(
            vec![
                ExecutionStep {
                    opcode: OpcodeId::PUSH3,
                    case: Case::Success,
                    values: vec![
                        a.clone(),
                        [
                            1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        ]
                    ],
                },
                ExecutionStep {
                    opcode: OpcodeId::PUSH3,
                    case: Case::Success,
                    values: vec![
                        b.clone(),
                        [
                            1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        ]
                    ],
                },
                ExecutionStep {
                    opcode: OpcodeId::LT,
                    case: Case::Success,
                    values: vec![
                        a.clone(),
                        b.clone(),
                        c.clone(),
                        carry.clone(),
                        sumc_array.clone(),
                        result.clone(),
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
        // GT
        try_test_circuit!(
            vec![
                ExecutionStep {
                    opcode: OpcodeId::PUSH3,
                    case: Case::Success,
                    values: vec![
                        b.clone(),
                        [
                            1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        ]
                    ],
                },
                ExecutionStep {
                    opcode: OpcodeId::PUSH3,
                    case: Case::Success,
                    values: vec![
                        a.clone(),
                        [
                            1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        ]
                    ],
                },
                ExecutionStep {
                    opcode: OpcodeId::GT,
                    case: Case::Success,
                    values: vec![
                        a.clone(),
                        b.clone(),
                        c.clone(),
                        carry.clone(),
                        sumc_array.clone(),
                        result.clone(),
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

        // passed test with result 0 for LT && GT(equal)
        println!("result 0 test with equal input");
        result[0] = 0;
        let (c, carry) = calc_array(a.clone(), a.clone());
        let mut sumc: u64 = 0;
        let mut sumc_array = [0 as u8; 32];
        for idx in 0..32 {
            sumc = sumc + (c[idx] as u64);
        }
        for idx in 0..32 {
            sumc_array[idx] = (sumc % (1 << 8)) as u8;
            sumc = sumc >> 8;
        }
        for idx in 0..32 {print!("{} ",a[idx]);}
        println!("");
        for idx in 0..32 {print!("{} ",a[idx]);}
        println!("");
        for idx in 0..32 {print!("{} ",c[idx]);}
        println!("");
        for idx in 0..32 {print!("{} ",carry[idx]);}
        println!("");
        for idx in 0..32 {print!("{} ",sumc_array[idx]);}
        println!("");
        for idx in 0..32 {print!("{} ",result[idx]);}
        println!("");
        //LT
        try_test_circuit!(
            vec![
                ExecutionStep {
                    opcode: OpcodeId::PUSH3,
                    case: Case::Success,
                    values: vec![
                        a.clone(),
                        [
                            1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        ]
                    ],
                },
                ExecutionStep {
                    opcode: OpcodeId::PUSH3,
                    case: Case::Success,
                    values: vec![
                        a.clone(),
                        [
                            1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        ]
                    ],
                },
                ExecutionStep {
                    opcode: OpcodeId::LT,
                    case: Case::Success,
                    values: vec![
                        a.clone(),
                        a.clone(),
                        c.clone(),
                        carry.clone(),
                        sumc_array.clone(),
                        result.clone(),
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
        // GT
        try_test_circuit!(
            vec![
                ExecutionStep {
                    opcode: OpcodeId::PUSH3,
                    case: Case::Success,
                    values: vec![
                        a.clone(),
                        [
                            1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        ]
                    ],
                },
                ExecutionStep {
                    opcode: OpcodeId::PUSH3,
                    case: Case::Success,
                    values: vec![
                        a.clone(),
                        [
                            1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        ]
                    ],
                },
                ExecutionStep {
                    opcode: OpcodeId::GT,
                    case: Case::Success,
                    values: vec![
                        a.clone(),
                        a.clone(),
                        c.clone(),
                        carry.clone(),
                        sumc_array.clone(),
                        result.clone(),
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
        // passed test with result 0 for LT && GT(not equal)
        println!("result 0 test with not equal input");
        let (c, carry) = calc_array(b.clone(), a.clone());
        let mut sumc: u64 = 0;
        let mut sumc_array = [0 as u8; 32];
        for idx in 0..32 {
            sumc = sumc + (c[idx] as u64);
        }
        for idx in 0..32 {
            sumc_array[idx] = (sumc % (1 << 8)) as u8;
            sumc = sumc >> 8;
        }
        for idx in 0..32 {print!("{} ",a[idx]);}
        println!("");
        for idx in 0..32 {print!("{} ",a[idx]);}
        println!("");
        for idx in 0..32 {print!("{} ",c[idx]);}
        println!("");
        for idx in 0..32 {print!("{} ",carry[idx]);}
        println!("");
        for idx in 0..32 {print!("{} ",sumc_array[idx]);}
        println!("");
        for idx in 0..32 {print!("{} ",result[idx]);}
        println!("");
        //LT
        try_test_circuit!(
            vec![
                ExecutionStep {
                    opcode: OpcodeId::PUSH3,
                    case: Case::Success,
                    values: vec![
                        b.clone(),
                        [
                            1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        ]
                    ],
                },
                ExecutionStep {
                    opcode: OpcodeId::PUSH3,
                    case: Case::Success,
                    values: vec![
                        a.clone(),
                        [
                            1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        ]
                    ],
                },
                ExecutionStep {
                    opcode: OpcodeId::LT,
                    case: Case::Success,
                    values: vec![
                        b.clone(),
                        a.clone(),
                        c.clone(),
                        carry.clone(),
                        sumc_array.clone(),
                        result.clone(),
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
        // GT
        try_test_circuit!(
            vec![
                ExecutionStep {
                    opcode: OpcodeId::PUSH3,
                    case: Case::Success,
                    values: vec![
                        a.clone(),
                        [
                            1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        ]
                    ],
                },
                ExecutionStep {
                    opcode: OpcodeId::PUSH3,
                    case: Case::Success,
                    values: vec![
                        b.clone(),
                        [
                            1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        ]
                    ],
                },
                ExecutionStep {
                    opcode: OpcodeId::GT,
                    case: Case::Success,
                    values: vec![
                        b.clone(),
                        a.clone(),
                        c.clone(),
                        carry.clone(),
                        sumc_array.clone(),
                        result.clone(),
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
