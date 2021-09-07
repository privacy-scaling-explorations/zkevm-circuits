use super::super::{
    BusMappingLookup, Case, Cell, Constraint, CoreStateInstance, ExecutionStep,
    Lookup, Word
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
    result: Word<F>,
    c: [Cell<F>; 32],
    carry: Cell<F>,
    sumc: Cell<F>,
    sumc_inv: Cell<F>,
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
            num_cell: 35, // 32 c + swap + carry + sumc + sumc_inv
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
                c: success.cells.drain(0..32).collect::<Vec<Cell<F>>>().try_into().unwrap(),
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
        let (lt, gt) = (
            Expression::Constant(F::from_u64((OpcodeId::LT).as_u8() as u64)),
            Expression::Constant(F::from_u64((OpcodeId::GT).as_u8() as u64)),
        );

        let OpExecutionState { opcode, .. } = &state_curr;

        let common_polys =
            vec![(opcode.expr() - lt.clone()) * (opcode.expr() - gt.clone())];

        let success = {
            let (zero, one, three, val_256) = (
                Expression::Constant(F::zero()),
                Expression::Constant(F::one()),
                Expression::Constant(F::from_u64(3)),
                Expression::Constant(F::from_u64(1 << 8)),
            );

            // interpreter state transition constraints
            let state_transition_constraints = vec![
                state_curr.global_counter.expr()
                    - (state_next.global_counter.expr() + three.clone()),
                state_curr.stack_pointer.expr()
                    - (state_next.stack_pointer.expr() + one.clone()),
                state_curr.program_counter.expr()
                    - (state_next.program_counter.expr() + one.clone()),
                state_curr.gas_counter.expr()
                    - (state_next.gas_counter.expr() + three),
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

            let no_swap = one.clone() - swap.expr();
            let swap_constraints = vec![
                swap.expr() * no_swap.clone(),
                swap.expr() * (opcode.expr() - gt),
                no_swap.clone() * (opcode.expr() - lt),
            ];

            // sumc_expr == sumc_cell
            // sumc_expr != 0
            let mut sumc_expr = zero.clone();  // The sum of c limbs
            for idx in 0..32 {
                sumc_expr = sumc_expr + c[idx].expr();
            }
            let sumc_is_zero_expr = one.clone() - sumc_expr.clone() * sumc_inv.expr();
            // same as is_zero gadget, currently we cannot use gadget inside OpGadget
            let sumc_is_zero_constraints = vec![
                sumc_expr.clone() * sumc_is_zero_expr.clone(),
                sumc_inv.expr() * sumc_is_zero_expr.clone(),
            ];
            let sumc_constraints = vec![
                sumc_expr - sumc.expr(),
                sumc_is_zero_expr.clone(),
            ];

            let mut lt_constraints = vec![];

            // a[15..0] + c[15..0] = carry * 256^16 + b[15..0]
            let mut exponent = one.clone();
            let mut lhs = zero.clone();
            let mut rhs = zero.clone();
            for idx in 0..16 {
                lhs = lhs + (a.cells[idx].expr() + c[idx].expr()) * exponent.clone();
                rhs = rhs + b.cells[idx].expr() * exponent.clone();
                exponent = exponent * val_256.clone();
            }
            rhs = rhs + carry.expr() * exponent;
            lt_constraints.push(lhs - rhs);

            // a[31..16] + c[31..16] + carry = b[31..16] + (1 - result) * 256^16 * sumc
            // - a < b, a + c = b
            // - a = b, a + c = b, c = 0
            // - a > b, a + c = b + 2^256
            exponent = one.clone();
            lhs = carry.expr();
            rhs = zero.clone();
            for idx in 16..32 {
                lhs = lhs + (a.cells[idx].expr() + c[idx].expr()) * exponent.clone();
                rhs = rhs + b.cells[idx].expr() * exponent.clone();
                exponent = exponent * val_256.clone();
            }
            rhs = rhs + (one.clone() - result.cells[0].expr()) * exponent * sumc_is_zero_expr;
            lt_constraints.push(lhs - rhs);

            // result[0] == 0/1, result[1..32] == 0
            let mut result_constraints = vec![
                result.cells[0].expr() * (one.clone() - result.cells[0].expr()),
            ];
            for idx in 1..32 {
                result_constraints.push(result.cells[idx].expr());
            }

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

            Constraint {
                name: "LtGadget success",
                selector: selector.expr(),
                polys: [
                    common_polys.clone(),
                    state_transition_constraints,
                    swap_constraints,
                    sumc_constraints,
                    sumc_is_zero_constraints,
                    lt_constraints,
                    result_constraints,
                ].concat(),
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
        self.success.result.assign(
            region,
            offset,
            Some(execution_step.values[2]),
        )?;
        self.success.c
            .iter()
            .zip(execution_step.values[3].iter())
            .map(|(alloc, value)| {
                alloc.assign(region, offset, Some(F::from_u64(*value as u64)))
            })
            .collect::<Result<Vec<_>, _>>()?;
        self.success.carry.assign(
            region,
            offset,
            Some(F::from_u64(execution_step.values[4][0] as u64)),
        )?;
        let sumc = F::from_u64(execution_step.values[4][1] as u64);
        let sumc_inv = sumc.invert().unwrap_or(F::zero());
        self.success.sumc.assign(
            region,
            offset,
            Some(sumc),
        )?;
        self.success.sumc_inv.assign(
            region,
            offset,
            Some(sumc_inv),
        )?;
        /*
        let mut sumc: u64 = 0;
        let mut pw: u64 = 1;
        for idx in 1..3 {
            sumc = sumc + (execution_step.values[4][idx] as u64) * pw;
            pw = pw * (1 << 8);
        }
        let sumc = F::from_u64(sumc);
        self.success.sumc.assign(
            region,
            offset,
            Some(sumc),
        )?;
        */
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
        a: [u64; 32],
        b: [u64; 32],
    ) -> ([u64; 32], u8){
        let mut c = [0 as u64; 32];
        let mut pre_sub: [i16; 32] = [0 as i16; 32];
        let mut pre_add: [i16; 32] = [0 as i16; 32];
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
        let carry: u8 = pre_add[16] as u8;
        (c, carry)
    }
    #[test]
    fn lt_gadget(){
        let a: [u64; 32] = [
            1, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        ];
        let b: [u64; 32] = [
            5, 7, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        ];
        let (c, carry) = calc_array(a.clone(), b.clone());
        let mut result = [0 as u64; 32];
        let mut extra = [0 as u64; 32];

        let mut sumc: u64 = 0;
        for idx in 0..32 {
            sumc = sumc + (c[idx] as u64);
        }
        extra[0] = carry as u64;
        extra[1] = sumc;
        //passed test with result 1 for LT && GT
        result[0] = 1;
        println!("result 1 test");
        for idx in 0..32 {print!("{} ",a[idx]);}
        println!("");
        for idx in 0..32 {print!("{} ",b[idx]);}
        println!("");
        for idx in 0..32 {print!("{} ",result[idx]);}
        println!("");
        for idx in 0..32 {print!("{} ",c[idx]);}
        println!("");
        println!("carry = {}", carry);
        //for idx in 0..32 {print!("{} ",sumc_array[idx]);}
        println!("sumc = {}", sumc);

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
                        result.clone(),
                        c.clone(),
                        extra.clone(),
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
