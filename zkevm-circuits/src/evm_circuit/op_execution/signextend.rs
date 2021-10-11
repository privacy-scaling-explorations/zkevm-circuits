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
    is_byte_selected: [IsEqualGadget<F>; 31],
    selectors: [Cell<F>; 31],
}

impl<F: FieldExt> SignextendSuccessCase<F> {
    pub(crate) const CASE_CONFIG: &'static CaseConfig = &CaseConfig {
        case: Case::Success,
        num_word: 3, // value + index + result
        num_cell: 1                               // sign_byte
            + IsZeroGadget::<F>::NUM_CELLS        // is_msb_sum_zero
            + IsEqualGadget::<F>::NUM_CELLS * 31  // is_byte_selected
            + 31, // selectors
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
            selectors: array_init(|_| alloc.cells.pop().unwrap()),
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

        // Now we need to find the byte we have to inspect to see how we need to do the extending.
        // We go byte by byte and check if `idx == index[0]`.
        // If they are equal (at most once) we add the byte value to the sum, else we add 0.
        // The additional condition for this is that none of the non-LSB bytes are non-zero (see above).
        // At the end this sum needs to equal `result[0]`.
        // We also generate the selectors, which we'll use to decide if we need to
        // replace bytes because the the sign extending.
        // We don't have to check the MSB, if that byte is selected no changes need to be done either.
        let mut selected_byte = 0.expr();
        for idx in 0..31 {
            // Check if this byte is selected looking only at the LSB of the index word
            let is_byte_selected = utils::and::expr(
                self.is_byte_selected[idx].constraints(
                    &mut cb,
                    self.index.cells[0].expr(),
                    idx.expr(),
                ),
                msb_sum_zero.clone(),
            );

            // Add the byte to the sum when this byte is selected
            selected_byte = selected_byte
                + (is_byte_selected.clone() * self.value.cells[idx].expr());

            // Cells are used here to store intermediate results, otherwise these sums
            // are very long expressions.
            // Once a byte was selected, all following bytes need to be replaced as well,
            // so a selector is the sum of the current and all previous `is_byte_selected`.
            cb.require_equal(
                is_byte_selected.clone()
                    + (if idx > 0 {
                        self.selectors[idx - 1].expr()
                    } else {
                        0.expr()
                    }),
                self.selectors[idx].expr(),
            );
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
        // The resulting byte is either the original value or the sign byte.
        for idx in 1..32 {
            cb.require_equal(
                self.result.cells[idx].expr(),
                utils::select::expr(
                    self.selectors[idx - 1].expr(),
                    self.sign_byte.expr().clone(),
                    self.value.cells[idx].expr(),
                ),
            );
        }

        // Pop the byte index and the value from the stack, push the result on the stack
        cb.stack_pop(self.index.expr());
        cb.stack_pop(self.value.expr());
        cb.stack_push(self.result.expr());

        // State transitions
        utils::StateTransitions {
            gc_delta: Some(GC_DELTA.expr()),
            sp_delta: Some(SP_DELTA.expr()),
            pc_delta: Some(PC_DELTA.expr()),
            gas_delta: Some(GAS.expr()),
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

        let msb_sum_zero = self.is_msb_sum_zero.assign(
            region,
            offset,
            utils::sum::value(&step.values[0].to_word()[1..32]),
        )?;

        // Generated selectors
        let mut selected = [F::zero(); 32];
        for i in 0..31 {
            selected[i] = utils::and::value(
                F::from_u64(self.is_byte_selected[i].assign(
                    region,
                    offset,
                    F::from_u64(step.values[0].to_word()[0] as u64),
                    F::from_u64(i as u64),
                )? as u64),
                F::from_u64(msb_sum_zero as u64),
            );
        }

        // Generate selectors
        let mut previous_selector_value: F = 0.into();
        for i in 1..32 {
            let selector_value = selected[i - 1] + previous_selector_value;
            self.selectors[i - 1]
                .assign(region, offset, Some(selector_value))
                .unwrap();
            previous_selector_value = selector_value;
        }

        // Sign byte lookup
        let mut sign = 0u64;
        if step.values[0] < BigUint::from(32u64) {
            let n = step.values[0].to_u32().unwrap();
            sign = (step.values[1].to_word()[n as usize] >> 7) as u64;
        }
        self.sign_byte
            .assign(region, offset, Some(F::from_u64(sign * 0xFF)))
            .unwrap();

        // State transitions
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

    fn compress(value: BigUint) -> Base {
        value
            .to_bytes_le()
            .iter()
            .fold(Base::zero(), |acc, val| acc + Base::from_u64(*val as u64))
    }

    fn check_signextend_gadget(
        value: BigUint,
        index: BigUint,
        result: BigUint,
    ) {
        let all_ones = BigUint::from_bytes_le(&[1u8; 32]);
        try_test_circuit!(
            vec![
                ExecutionStep {
                    opcode: OpcodeId::PUSH32,
                    case: Case::Success,
                    values: vec![value.clone(), all_ones.clone()],
                },
                ExecutionStep {
                    opcode: OpcodeId::PUSH32,
                    case: Case::Success,
                    values: vec![index.clone(), all_ones],
                },
                ExecutionStep {
                    opcode: OpcodeId::SIGNEXTEND,
                    case: Case::Success,
                    values: vec![index.clone(), value.clone(), result.clone()],
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
                        compress(value.clone()),
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
                        compress(index.clone()),
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
                        compress(index),
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
                        compress(value),
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
    }

    #[test]
    fn signextend_gadget() {
        // Extend byte 2 (negative)
        check_signextend_gadget(
            0xF00201u64.into(),
            2u64.into(),
            BigUint::from_bytes_le(&[
                0x01, 0x02, 0xF0, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
                0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
                0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
                0xFF, 0xFF,
            ]),
        );
        // Extend byte 0 (positive)
        check_signextend_gadget(0xFF01u64.into(), 0u64.into(), 0x01u64.into());
        // Extend byte 258
        check_signextend_gadget(
            0xF00201u64.into(),
            258u64.into(),
            0xF00201u64.into(),
        );
    }

    #[test]
    #[ignore]
    fn signextend_gadget_exhaustive() {
        let pos_value: [u8; 32] = [0b01111111u8; 32];
        let neg_value: [u8; 32] = [0b10000000u8; 32];

        let pos_extend = 0u8;
        let neg_extend = 0xFFu8;

        for (value, byte_extend) in
            vec![(pos_value, pos_extend), (neg_value, neg_extend)].iter()
        {
            for idx in 0..33 {
                println!("{}", idx);
                check_signextend_gadget(
                    BigUint::from_bytes_le(value),
                    (idx as u64).into(),
                    BigUint::from_bytes_le(
                        &(0..32)
                            .map(|i| {
                                if i > idx {
                                    byte_extend.clone()
                                } else {
                                    value[i].clone()
                                }
                            })
                            .collect::<Vec<u8>>(),
                    ),
                );
            }
        }
    }
}
