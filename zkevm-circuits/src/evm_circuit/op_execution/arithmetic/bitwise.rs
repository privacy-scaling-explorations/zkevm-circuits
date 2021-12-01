use super::super::super::{
    Case, Cell, Constraint, ExecutionStep, FixedLookup, Word,
};
use super::super::utils::{
    self,
    common_cases::{OutOfGasCase, StackUnderflowCase},
    constraint_builder::ConstraintBuilder,
    StateTransition,
};
use super::super::{
    CaseAllocation, CaseConfig, CoreStateInstance, OpExecutionState, OpGadget,
};
use crate::impl_op_gadget;
use crate::util::{Expr, ToWord};
use bus_mapping::evm::{GasCost, OpcodeId};
use halo2::plonk::Error;
use halo2::{arithmetic::FieldExt, circuit::Region};
use std::convert::TryInto;

static STATE_TRANSITION: StateTransition = StateTransition {
    gc_delta: Some(3), // 2 stack pops + 1 stack push
    pc_delta: Some(1),
    sp_delta: Some(1),
    gas_delta: Some(GasCost::FASTEST.as_u64()),
    next_memory_size: None,
};
const NUM_POPPED: usize = 2;

#[derive(Clone, Debug)]
struct BitwiseSuccessCase<F> {
    case_selector: Cell<F>,
    a: Word<F>,
    b: Word<F>,
    c: Word<F>,
}

macro_rules! impl_bitwise_op_gadget {
    ($op:ident) => {
        paste::paste! {
            impl_op_gadget!(
                #set[ [<$op:upper>] ]
                [<$op Gadget>] {
                    [<$op SuccessCase>](),
                    StackUnderflowCase(NUM_POPPED),
                    OutOfGasCase(STATE_TRANSITION.gas_delta.unwrap()),
                }
            );

            #[derive(Clone, Debug)]
            struct [<$op SuccessCase>]<F> {
                case_selector: Cell<F>,
                a: Word<F>,
                b: Word<F>,
                c: Word<F>,
            }

            impl<F: FieldExt> [<$op SuccessCase>]<F> {
                pub(crate) const CASE_CONFIG: &'static CaseConfig = &CaseConfig {
                    case: Case::Success,
                    num_word: 3, // a + b + c
                    num_cell: 0,
                    will_halt: false,
                };

                pub(crate) fn construct(alloc: &mut CaseAllocation<F>) -> Self {
                    Self {
                        case_selector: alloc.selector.clone(),
                        a: alloc.words.pop().unwrap(),
                        b: alloc.words.pop().unwrap(),
                        c: alloc.words.pop().unwrap(),
                    }
                }

                pub(crate) fn constraint(
                    &self,
                    state_curr: &OpExecutionState<F>,
                    state_next: &OpExecutionState<F>,
                    name: &'static str,
                ) -> Vec<Constraint<F>> {
                    let mut cb = ConstraintBuilder::default();

                    for idx in 0..32 {
                        cb.add_fixed_lookup(
                            FixedLookup::[<Bitwise $op>],
                            [
                                self.a.cells[idx].expr(),
                                self.b.cells[idx].expr(),
                                self.c.cells[idx].expr(),
                            ]
                        );
                    }

                    cb.stack_pop(self.a.expr());
                    cb.stack_pop(self.b.expr());
                    cb.stack_push(self.c.expr());

                    STATE_TRANSITION.constraints(&mut cb, state_curr, state_next);

                    vec![cb.constraint(self.case_selector.expr(), name)]
                }

                fn assign(
                    &self,
                    region: &mut Region<'_, F>,
                    offset: usize,
                    state: &mut CoreStateInstance,
                    step: &ExecutionStep,
                ) -> Result<(), Error> {

                    self.a.assign(
                        region,
                        offset,
                        Some(step.values[0].to_word()),
                    )?;
                    self.b.assign(
                        region,
                        offset,
                        Some(step.values[1].to_word()),
                    )?;
                    self.c.assign(
                        region,
                        offset,
                        Some(step.values[2].to_word()),
                    )?;

                    // State transitions
                    STATE_TRANSITION.assign(state);

                    Ok(())
                }
            }
        }
    };
}

impl_bitwise_op_gadget!(And);
impl_bitwise_op_gadget!(Or);
impl_bitwise_op_gadget!(Xor);

#[cfg(test)]
mod test {
    use super::super::super::super::{
        test::TestCircuit, Case, ExecutionStep, Operation,
    };
    use crate::{gadget::evm_word::encode, util::ToWord};
    use bus_mapping::{evm::OpcodeId, operation::Target};
    use halo2::{arithmetic::FieldExt, dev::MockProver};
    use num::BigUint;
    use pasta_curves::pallas::Base;

    macro_rules! try_test_circuit {
        ($execution_steps:expr, $operations:expr, $result:expr) => {{
            let circuit =
                TestCircuit::<Base>::new($execution_steps, $operations, true);
            let prover = MockProver::<Base>::run(18, &circuit, vec![]).unwrap();
            assert_eq!(prover.verify(), $result);
        }};
    }

    fn compress(value: BigUint) -> Base {
        let r = Base::from_u64(1);
        encode(value.to_word().to_vec().into_iter().rev(), r)
    }

    fn check(opcode: OpcodeId, a: BigUint, b: BigUint, c: BigUint) {
        // ADD
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
                    opcode,
                    case: Case::Success,
                    values: vec![a.clone(), b.clone(), c.clone()],
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
                        compress(b.clone()),
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
                        compress(a.clone()),
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
                        compress(a),
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
                        compress(b),
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
                        compress(c),
                        Base::zero(),
                    ]
                }
            ],
            Ok(())
        );
    }

    #[test]
    fn and_gadget() {
        let a = BigUint::from(0x12_34_56u64);
        let b = BigUint::from(0x78_9A_BCu64);
        let c = BigUint::from(0x10_10_14u64);
        check(OpcodeId::AND, a, b, c);
    }

    #[test]
    fn or_gadget() {
        let a = BigUint::from(0x12_34_56u64);
        let b = BigUint::from(0x78_9A_BCu64);
        let c = BigUint::from(0x7A_BE_FEu64);
        check(OpcodeId::OR, a, b, c);
    }

    #[test]
    fn xor_gadget() {
        let a = BigUint::from(0x12_34_56u64);
        let b = BigUint::from(0x78_9A_BCu64);
        let c = BigUint::from(0x6A_AE_EAu64);
        check(OpcodeId::XOR, a, b, c);
    }
}
