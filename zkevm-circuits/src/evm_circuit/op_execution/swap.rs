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
struct SwapSuccessAllocation<F> {
    case_selector: Cell<F>,
    words: [Word<F>; 4],
}

#[derive(Clone, Debug)]
pub struct SwapGadget<F> {
	success: SwapSuccessAllocation<F>,
	stack_underflow: Cell<F>,
	// case selector
	out_of_gas: (
		Cell<F>,    // case selector
		Cell<F>,    // gas available
	),
}

impl<F: FieldExt> OpGadget<F> for SwapGadget<F> {
	const RESPONSIBLE_OPCODES: &'static [OpcodeId] = &[
		OpcodeId::SWAP1,
		OpcodeId::SWAP2,
		 OpcodeId::SWAP3,
		 OpcodeId::SWAP4,
		OpcodeId::SWAP5,
		OpcodeId::SWAP6,
		 OpcodeId::SWAP7,
		OpcodeId::SWAP8,
		OpcodeId::SWAP9,
		 OpcodeId::SWAP10,
		 OpcodeId::SWAP11,
		  OpcodeId::SWAP12,
		  OpcodeId::SWAP13,
		  OpcodeId::SWAP14,
		 OpcodeId::SWAP15,
		 OpcodeId::SWAP16,
	];
	
	const CASE_CONFIGS: &'static [CaseConfig] = &[
		CaseConfig {
			case: Case::Success,
			num_word: 4,
			num_cell: 0,
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
		let [success, stack_underflow, out_of_gas]: [CaseAllocation<F>; 3] =
			case_allocations.try_into().unwrap();
		Self {
			success: SwapSuccessAllocation {
				case_selector: success.selector.clone(),
				words: success.words.try_into().unwrap(),
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
		
		let common_lookups = vec![
			Lookup::FixedLookup(
				FixedLookup::Range16,
				[opcode.expr() - OpcodeId::SWAP1.expr(), 0.expr(), 0.expr()],
			),
			Lookup::FixedLookup(
				FixedLookup::Range16,
				[POSITION.expr() - OpcodeId::SWAP1.expr(), 0.expr(), 0.expr()],
			),
		];
		
		let success = {
			let SwapSuccessAllocation {
				case_selector,
				words,
			} = &self.success;
			
			let state_transition_constraints = vec![
				state_next.global_counter.expr()
					- (state_curr.global_counter.expr() + 1.expr()),
				state_next.program_counter.expr()
					- (state_curr.program_counter.expr() + 1.expr()),
				state_next.gas_counter.expr()
					- (state_curr.gas_counter.expr() + GasCost::FASTEST.expr()),
			];
			
			// a == c, b == d, (a + c) == (b + d)
			let swap_constraints = vec![
				words[0].expr() - words[3].expr(),
				words[1].expr() - words[2].expr(),
				(words[0].expr() + words[1].expr()) - (words[2].expr() + words[3].expr()),
			];
			
			/*
				bus_mapping_lookup(gc, Stack, key+X, $val1, Read)
				bus_mapping_lookup(gc+1, Stack, key, $val2, Read)
				bus_mapping_lookup(gc+2, Stack, key+X, $val2, Write)
				bus_mapping_lookup(gc+3, Stack, key, $val1, Write)
			*/
			let num_swaped = (POSITION - OpcodeId::SWAP1.as_u8() + 1) as i32;
			let bus_mapping_lookups = vec![
				Lookup::BusMappingLookup(BusMappingLookup::Stack {
					index_offset: num_swaped,
					value: words[0].expr(),
					is_write: false,
				}),
				Lookup::BusMappingLookup(BusMappingLookup::Stack {
					index_offset: 0,
					value: words[1].expr(),
					is_write: false,
				}),
				Lookup::BusMappingLookup(BusMappingLookup::Stack {
					index_offset: num_swaped,
					value: words[2].expr(),
					is_write: true,
				}),
				Lookup::BusMappingLookup(BusMappingLookup::Stack {
					index_offset: 0,
					value: words[3].expr(),
					is_write: true,
				}),
			];
			
			Constraint {
				name: "PushGadget success",
				selector: case_selector.expr(),
				polys: [state_transition_constraints, swap_constraints]
					.concat(),
				lookups: bus_mapping_lookups,
			}
		};
		
		let stack_overflow = {
			let stack_pointer = state_curr.stack_pointer.expr();
			Constraint {
				name: "PushGadget stack overflow",
				selector: self.stack_underflow.expr(),
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
			Case::StackUnderflow => {
				unimplemented!()
			}
			Case::OutOfGas => {
				unimplemented!()
			}
			_ => unreachable!()
		}
	}
}

impl<F: FieldExt> SwapGadget<> {
	fn assign_success(
		&self,
		region: &mut Region<'_, F>,
		offset: usize,
		core_state: &mut CoreStateInstance,
		execution_step: &ExecutionStep,
	) -> Result<(), Error> {
		core_state.global_counter += 1;
		core_state.program_counter += 1;
		core_state.gas_counter += 3;
		
		for idx in 0..4 {
			self.success.words[idx].assign(
				region,
				offset,
				Some(execution_step.values[idx].to_word()),
			)?;
		}
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

    // TODO: add failure cases
    #[test]
    fn swap2_gadget() {
        // SWAP2
        try_test_circuit!(
            vec![
                ExecutionStep {
                    opcode: OpcodeId::PUSH3,
                    case: Case::Success,
                    values: vec![
                        BigUint::from(0x03_02_01u64),
                        BigUint::from(0x01_01_01u64)
                    ],
                },
                ExecutionStep {
                    opcode: OpcodeId::PUSH2,
                    case: Case::Success,
                    values: vec![
                        BigUint::from(0x05_04u64),
                        BigUint::from(0x01_01u64)
                    ],
                },
                ExecutionStep {
                    opcode: OpcodeId::PUSH1,
                    case: Case::Success,
                    values: vec![
                        BigUint::from(0x06u64),
                        BigUint::from(0x01u64)
                    ],
                },
                ExecutionStep {
                    opcode: OpcodeId::SWAP2,
                    case: Case::Success,
                    values: vec![
                        BigUint::from(0x03_02_01u64),
                        BigUint::from(0x06u64),
                        BigUint::from(0x06u64),
                        BigUint::from(0x03_02_01u64),
                    ],
                },
            ],
            vec![
                Operation {
                    // push3
                    gc: 1,
                    target: Target::Stack,
                    is_write: true,
                    values: [
                        Base::zero(),
                        Base::from_u64(1023),
                        Base::from_u64(1 + 2 + 3),
                        Base::zero(),
                    ],
                },
                Operation {
                    // push2
                    gc: 2,
                    target: Target::Stack,
                    is_write: true,
                    values: [
                        Base::zero(),
                        Base::from_u64(1022),
                        Base::from_u64(4 + 5),
                        Base::zero(),
                    ]
                },
                Operation {
                    // push1
                    gc: 3,
                    target: Target::Stack,
                    is_write: true,
                    values: [
                        Base::zero(),
                        Base::from_u64(1021),
                        Base::from_u64(6),
                        Base::zero(),
                    ]
                },
                // swap1 1021 <=> 1022
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
                    is_write: false,
                    values: [
                        Base::zero(),
                        Base::from_u64(1021),
                        Base::from_u64(6),
                        Base::zero(),
                    ]
                },
                Operation {
                    gc: 6,
                    target: Target::Stack,
                    is_write: true,
                    values: [
                        Base::zero(),
                        Base::from_u64(1023),
                        Base::from_u64(6),
                        Base::zero(),
                    ]
                },
                Operation {
                    gc: 7,
                    target: Target::Stack,
                    is_write: true,
                    values: [
                        Base::zero(),
                        Base::from_u64(1021),
                        Base::from_u64(1 + 2 + 3),
                        Base::zero(),
                    ]
                }
            ],
            Ok(())
        );
    }

    #[test]
    fn swap1_gadget() {
        // SWAP1
        try_test_circuit!(
            vec![
                ExecutionStep {
                    opcode: OpcodeId::PUSH3,
                    case: Case::Success,
                    values: vec![
                        BigUint::from(0x03_02_01u64),
                        BigUint::from(0x01_01_01u64)
                    ],
                },
                ExecutionStep {
                    opcode: OpcodeId::PUSH2,
                    case: Case::Success,
                    values: vec![
                        BigUint::from(0x05_04u64),
                        BigUint::from(0x01_01u64)
                    ],
                },
                ExecutionStep {
                    opcode: OpcodeId::SWAP1,
                    case: Case::Success,
                    values: vec![
                        BigUint::from(0x03_02_01u64),
                        BigUint::from(0x05_04u64),
                        BigUint::from(0x05_04u64),
                        BigUint::from(0x03_02_01u64),
                    ],
                },
            ],
            vec![
                Operation {
                    // push3
                    gc: 1,
                    target: Target::Stack,
                    is_write: true,
                    values: [
                        Base::zero(),
                        Base::from_u64(1023),
                        Base::from_u64(1 + 2 + 3),
                        Base::zero(),
                    ],
                },
                Operation {
                    // push2
                    gc: 2,
                    target: Target::Stack,
                    is_write: true,
                    values: [
                        Base::zero(),
                        Base::from_u64(1022),
                        Base::from_u64(4 + 5),
                        Base::zero(),
                    ]
                },
                // swap1 1023 <=> 1022
                Operation {
                    gc: 3,
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
                    gc: 4,
                    target: Target::Stack,
                    is_write: false,
                    values: [
                        Base::zero(),
                        Base::from_u64(1022),
                        Base::from_u64(4 + 5),
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
                        Base::from_u64(4 + 5),
                        Base::zero(),
                    ]
                },
                Operation {
                    gc: 6,
                    target: Target::Stack,
                    is_write: true,
                    values: [
                        Base::zero(),
                        Base::from_u64(1022),
                        Base::from_u64(1 + 2 + 3),
                        Base::zero(),
                    ]
                }
            ],
            Ok(())
        );
    }
}
