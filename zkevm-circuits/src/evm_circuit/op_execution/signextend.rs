use super::super::{Case, Cell, Constraint, ExecutionStep, Word};
use super::utils;
use super::utils::common_cases::{OutOfGasCase, StackUnderflowCase};
use super::utils::constraint_builder::ConstraintBuilder;
use super::utils::math_gadgets::{IsEqualGadget, IsZeroGadget};
use super::{
    CaseAllocation, CaseConfig, CoreStateInstance, OpExecutionState, OpGadget,
};
use crate::evm_circuit::{FixedLookup, Lookup};
use crate::impl_op_gadget;
use crate::util::{Expr, ToWord};
use array_init::array_init;
use bus_mapping::evm::{GasCost, OpcodeId};
use halo2::plonk::Error;
use halo2::{arithmetic::FieldExt, circuit::Region};
use num::{BigUint, ToPrimitive};
use std::convert::TryInto;

const GC_DELTA: usize = 3;
const PC_DELTA: usize = 1;
const SP_DELTA: usize = 1;
const GAS: GasCost = GasCost::FAST;
const NUM_POPPED: usize = 2;

impl_op_gadget!(
    [SIGNEXTEND],
    SignextendGadget {
        SignextendSuccessCase(),
        StackUnderflowCase(NUM_POPPED),
        OutOfGasCase(GAS.as_usize()),
    }
);

#[derive(Clone, Debug)]
struct SignextendSuccessCase<F> {
    case_selector: Cell<F>,
    index: Word<F>,
    value: Word<F>,
    result: Word<F>,
    sign_byte: Cell<F>,
    is_msb_sum_zero: IsZeroGadget<F>,
    is_byte_selected: [IsEqualGadget<F>; 32],
}

impl<F: FieldExt> SignextendSuccessCase<F> {
    pub(crate) const CASE_CONFIG: &'static CaseConfig = &CaseConfig {
        case: Case::Success,
        num_word: 3, // value + index + result
        num_cell: 1
            + IsZeroGadget::<F>::NUM_CELLS
            + IsEqualGadget::<F>::NUM_CELLS * 32, // 1x is_msb_sum_zero + 32x is_byte_selected
        will_halt: false,
    };

    pub(crate) fn construct(alloc: &mut CaseAllocation<F>) -> Self {
        Self {
            case_selector: alloc.selector.clone(),
            index: alloc.words.pop().unwrap(),
            value: alloc.words.pop().unwrap(),
            result: alloc.words.pop().unwrap(),
            sign_byte: alloc.cells.pop().unwrap(),
            is_msb_sum_zero: IsZeroGadget::construct(alloc),
            is_byte_selected: array_init(|_| IsEqualGadget::construct(alloc)),
        }
    }

    pub(crate) fn constraint(
        &self,
        state_curr: &OpExecutionState<F>,
        state_next: &OpExecutionState<F>,
        name: &'static str,
    ) -> Constraint<F> {
        let mut cb = ConstraintBuilder::default();

        // If any of the non-LSB bytes of the index word are non-zero we never need to do any changes.
        // So just sum all the non-LSB byte values here and then check if it's non-zero
        // so we can use that as an additional condition when to change byte values.
        let msb_sum_zero = self
            .is_msb_sum_zero
            .constraints(&mut cb, utils::sum::expr(&self.index.cells[1..32]));

        // Now we just need to check that `result[0]` is the sum of all copied bytes.
        // We go byte by byte and check if `idx == index[0]`.
        // If they are equal (at most once) we add the byte value to the sum, else we add 0.
        // The additional condition for this is that none of the non-LSB bytes are non-zero (see above).
        // At the end this sum needs to equal `result[0]`.
        let mut selected = vec![];
        let mut selected_byte = 0.expr();
        for idx in 0..32 {
            // Check if this byte is selected looking only at the LSB of the index word
            let is_byte_selected = utils::and::expr(
                self.is_byte_selected[idx].constraints(
                    &mut cb,
                    self.index.cells[0].expr(),
                    idx.expr(),
                ),
                msb_sum_zero.clone(),
            );
            selected.push(is_byte_selected.clone());

            // Add the byte to the sum when this byte is selected
            selected_byte = selected_byte
                + (is_byte_selected * self.value.cells[idx].expr());
        }

        // Use the sign of the selected byte to find the byte we'll use to extend the result.
        // If no byte was selected the sign byte won't be used so its value doesn't matter.
        cb.add_lookup(Lookup::FixedLookup(
            FixedLookup::SignByte,
            [selected_byte, self.sign_byte.expr(), 0.expr()],
        ));

        // The LSB always remains the same
        cb.require_equal(
            self.result.cells[0].expr(),
            self.value.cells[0].expr(),
        );
        // All other bytes could change
        let mut do_extend = 0.expr();
        for idx in 1..32 {
            do_extend = do_extend + selected[idx - 1].clone();
            let expected_byte_value = utils::select::expr(
                do_extend.clone(),
                self.sign_byte.expr().clone(),
                self.value.cells[idx].expr(),
            );
            cb.require_equal(
                self.result.cells[idx].expr(),
                expected_byte_value,
            );
        }

        // Pop the byte index and the value from the stack, push the result on the stack
        cb.stack_pop(self.index.expr());
        cb.stack_pop(self.value.expr());
        cb.stack_push(self.result.expr());

        // State transitions
        #[allow(clippy::needless_update)]
        utils::StateTransitions {
            gc_delta: Some(GC_DELTA.expr()),
            sp_delta: Some(SP_DELTA.expr()),
            pc_delta: Some(PC_DELTA.expr()),
            gas_delta: Some(GAS.expr()),
            ..Default::default()
        }
        .constraints(&mut cb, state_curr, state_next);

        // Generate the constraint
        cb.constraint(self.case_selector.expr(), name)
    }

    fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        state: &mut CoreStateInstance,
        step: &ExecutionStep,
    ) -> Result<(), Error> {
        self.index
            .assign(region, offset, Some(step.values[0].to_word()))?;
        self.value
            .assign(region, offset, Some(step.values[1].to_word()))?;
        self.result
            .assign(region, offset, Some(step.values[2].to_word()))?;

        self.is_msb_sum_zero.assign(
            region,
            offset,
            utils::sum::value(&step.values[0].to_word()[1..32]),
        )?;

        for i in 0..32 {
            self.is_byte_selected[i].assign(
                region,
                offset,
                F::from_u64(step.values[0].to_word()[0] as u64),
                F::from_u64(i as u64),
            )?;
        }

        let mut sign = 0u64;
        if step.values[0] < BigUint::from(32u64) {
            let n = step.values[0].to_u32().unwrap();
            sign = (step.values[1].to_word()[n as usize] >> 7) as u64;
        }
        self.sign_byte
            .assign(region, offset, Some(F::from_u64(sign * 0xFF)))
            .unwrap();

        state.global_counter += GC_DELTA;
        state.program_counter += PC_DELTA;
        state.stack_pointer += SP_DELTA;
        state.gas_counter += GAS.as_usize();

        self.case_selector
            .assign(region, offset, Some(F::from_u64(1)))
            .unwrap();
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

    fn compress(bytes: [u8; 32]) -> Base {
        bytes
            .iter()
            .fold(Base::zero(), |acc, val| acc + Base::from_u64(*val as u64))
    }

    #[test]
    fn signextend_gadget() {
        // Extend byte 3 (LSB is at 0)
        let value = 0xF00201u64;
        let index = 2u64;
        let result = [
            0x01, 0x02, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
            0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
            0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
        ];
        try_test_circuit!(
            vec![
                ExecutionStep {
                    opcode: OpcodeId::PUSH3,
                    case: Case::Success,
                    values: vec![value.into(), 0x010101u64.into()],
                },
                ExecutionStep {
                    opcode: OpcodeId::PUSH1,
                    case: Case::Success,
                    values: vec![index.into(), 0x01u64.into()],
                },
                ExecutionStep {
                    opcode: OpcodeId::SIGNEXTEND,
                    case: Case::Success,
                    values: vec![
                        index.into(),
                        value.into(),
                        BigUint::from_bytes_le(&result),
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
                        Base::from_u64(0x01 + 0x02 + 0xF0),
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
                        Base::from_u64(index),
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
                        Base::from_u64(index),
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
                        Base::from_u64(0x01 + 0x02 + 0xF0),
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
                        compress(result),
                        Base::zero(),
                    ]
                },
            ],
            Ok(())
        );
        // Select byte 256
        /*try_test_circuit!(
            vec![
                ExecutionStep {
                    opcode: OpcodeId::PUSH3,
                    case: Case::Success,
                    values: vec![0x030201u64.into(), 0x010101u64.into()],
                },
                ExecutionStep {
                    opcode: OpcodeId::PUSH2,
                    case: Case::Success,
                    values: vec![0x0100u64.into(), 0x0101u64.into()],
                },
                ExecutionStep {
                    opcode: OpcodeId::BYTE,
                    case: Case::Success,
                    values: vec![
                        0x0100u64.into(),
                        0x030201u64.into(),
                        0u64.into(),
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
                        Base::from_u64(1),
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
                        Base::from_u64(1),
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
                },
            ],
            Ok(())
        );*/
    }
}
