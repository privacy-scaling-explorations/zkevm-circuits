use super::super::{Case, Cell, Constraint, ExecutionStep, Word};
use super::utils::constraint_builder::ConstraintBuilder;
use super::utils::math_gadgets::{IsEqualGadget, IsZeroGadget, LtGadget};
use super::utils::memory_gadgets::{
    self, address_high, address_low, MemoryExpansionGadget,
};
use super::utils::{StateTransition, StateTransitionExpressions};
use super::{
    CaseAllocation, CaseConfig, CoreStateInstance, OpExecutionState, OpGadget,
};
use crate::evm_circuit::param::{
    MAX_GAS_SIZE_IN_BYTES, MAX_MEMORY_SIZE_IN_BYTES, STACK_START_IDX,
};
use crate::impl_op_gadget;
use crate::util::{Expr, ToWord};
use bus_mapping::evm::{GasCost, OpcodeId};
use halo2::plonk::Error;
use halo2::{arithmetic::FieldExt, circuit::Region};
use std::convert::TryInto;

static STATE_TRANSITION: StateTransition = StateTransition {
    gc_delta: Some(34), // 2 stack + 32 memory
    pc_delta: Some(1),
    sp_delta: None,         // SP_DELTA_MLOAD/SP_DELTA_MSTORE
    gas_delta: None,        // GAS + memory_cost
    next_memory_size: None, // next_memory_size
};
const GAS: GasCost = GasCost::FASTEST;
const SP_DELTA_MLOAD: i32 = 0;
const SP_DELTA_MSTORE: i32 = 2;
const NUM_POPPED_MLOAD: usize = 2;
const NUM_POPPED_MSTORE: usize = 1;

impl_op_gadget!(
    #set[MLOAD, MSTORE]
    MemoryGadget {
        MemorySuccessCase(),
        MemoryStackUnderflowCase(),
        MemoryOutOfGasCase(),
    }
);

#[derive(Clone, Debug)]
struct MemorySuccessCase<F> {
    case_selector: Cell<F>,
    address: Word<F>,
    value: Word<F>,
    memory_expansion: MemoryExpansionGadget<F, MAX_GAS_SIZE_IN_BYTES>,
    is_mload: IsEqualGadget<F>,
}

impl<F: FieldExt> MemorySuccessCase<F> {
    pub(crate) const CASE_CONFIG: &'static CaseConfig = &CaseConfig {
        case: Case::Success,
        num_word: 2, // address + value,
        num_cell: MemoryExpansionGadget::<F, MAX_GAS_SIZE_IN_BYTES>::NUM_CELLS
            + IsEqualGadget::<F>::NUM_CELLS,
        will_halt: false,
    };

    pub(crate) fn construct(alloc: &mut CaseAllocation<F>) -> Self {
        Self {
            case_selector: alloc.selector.clone(),
            address: alloc.words.pop().unwrap(),
            value: alloc.words.pop().unwrap(),
            memory_expansion: MemoryExpansionGadget::construct(alloc),
            is_mload: IsEqualGadget::construct(alloc),
        }
    }

    pub(crate) fn constraint(
        &self,
        state_curr: &OpExecutionState<F>,
        state_next: &OpExecutionState<F>,
        name: &'static str,
    ) -> Constraint<F> {
        let mut cb = ConstraintBuilder::with_call_id(state_curr.call_id.expr());

        // Check if this is an MLOAD or an MSTORE
        let is_mload = self.is_mload.constraints(
            &mut cb,
            state_curr.opcode.expr(),
            OpcodeId::MLOAD.expr(),
        );
        let is_mstore = 1.expr() - is_mload.clone();

        // Not all address bytes are used to calculate the gas cost for the memory access,
        // so make sure this success case is disabled if any of those address bytes
        // are actually used.
        memory_gadgets::require_address_in_range(&mut cb, &self.address);
        // Get the capped address value we will use in the memory calculations
        let address = address_low::expr(&self.address);

        // Calculate the next memory size and the gas cost for this memory access
        let (next_memory_size, memory_cost) =
            self.memory_expansion.constraints(
                &mut cb,
                state_curr.memory_size.expr(),
                address.clone() + 32.expr(),
            );

        /* Stack operations */
        // Pop the address from the stack
        cb.stack_pop(self.address.expr());
        // For MLOAD push the value to the stack
        // FOR MSTORE pop the value from the stack
        let stack_offset = cb.stack_offset.expr() - is_mload.clone();
        cb.stack_lookup(stack_offset, self.value.expr(), is_mload);

        /* Memory operations */
        // Read/Write the value from memory at the specified address
        cb.memory_lookup(
            address,
            self.value.cells.iter().map(|cell| cell.expr()).collect(),
            is_mstore.clone(),
        );

        // State transitions
        // - `sp_delta` needs to be increased by SP_DELTA_MLOAD/SP_DELTA_MSTORE
        // - `gas_delta` needs to be increased by `GAS + memory_cost`
        // - `next_memory_size` needs to be set to `next_memory_size`
        let mut st = StateTransitionExpressions::new(STATE_TRANSITION.clone());
        st.sp_delta = Some(is_mstore * 2.expr());
        st.gas_delta = Some(GAS.expr() + memory_cost);
        st.next_memory_size = Some(next_memory_size);
        st.constraints(&mut cb, state_curr, state_next);

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
        // Inputs/Outputs
        self.address
            .assign(region, offset, Some(step.values[0].to_word()))?;
        self.value
            .assign(region, offset, Some(step.values[1].to_word()))?;

        // Check if this is an MLOAD or an MSTORE
        let is_mload = self.is_mload.assign(
            region,
            offset,
            F::from_u64(step.opcode.as_u8() as u64),
            F::from_u64(OpcodeId::MLOAD.as_u8() as u64),
        )?;

        // Memory expansion
        let address = address_low::value::<F>(step.values[0].to_word());
        let (new_memory_size, memory_cost) = self.memory_expansion.assign(
            region,
            offset,
            state.memory_size as u64,
            address + 32,
        )?;

        // State transitions
        let mut st = STATE_TRANSITION.clone();
        st.sp_delta = Some(if is_mload == F::one() {
            SP_DELTA_MLOAD
        } else {
            SP_DELTA_MSTORE
        });
        st.gas_delta = Some(GAS.as_u64() + (memory_cost as u64));
        st.next_memory_size = Some(new_memory_size);
        st.assign(state);

        Ok(())
    }
}

#[derive(Clone, Debug)]
struct MemoryOutOfGasCase<F> {
    case_selector: Cell<F>,
    gas_available: Cell<F>,
    address: Word<F>,
    address_in_range: IsZeroGadget<F>,
    memory_expansion:
        MemoryExpansionGadget<F, { MAX_MEMORY_SIZE_IN_BYTES * 2 - 1 }>,
    insufficient_gas: LtGadget<F, { MAX_MEMORY_SIZE_IN_BYTES * 2 - 1 }>,
}

impl<F: FieldExt> MemoryOutOfGasCase<F> {
    pub(crate) const CASE_CONFIG: &'static CaseConfig = &CaseConfig {
        case: Case::OutOfGas,
        num_word: 1,  // address
        num_cell: IsZeroGadget::<F>::NUM_CELLS
            + MemoryExpansionGadget::<F, { MAX_MEMORY_SIZE_IN_BYTES * 2 - 1}>::NUM_CELLS
            + LtGadget::<F, {MAX_MEMORY_SIZE_IN_BYTES*2-1}>::NUM_CELLS,
        will_halt: true,
    };

    pub(crate) fn construct(alloc: &mut CaseAllocation<F>) -> Self {
        Self {
            case_selector: alloc.selector.clone(),
            gas_available: alloc.resumption.clone().unwrap().gas_available,
            address: alloc.words.pop().unwrap(),
            address_in_range: IsZeroGadget::construct(alloc),
            memory_expansion: MemoryExpansionGadget::construct(alloc),
            insufficient_gas: LtGadget::construct(alloc),
        }
    }

    pub(crate) fn constraint(
        &self,
        state_curr: &OpExecutionState<F>,
        _state_next: &OpExecutionState<F>,
        name: &'static str,
    ) -> Constraint<F> {
        let mut cb = ConstraintBuilder::default();

        // Get the capped address value we will use in the memory calculations
        let address = address_low::expr(&self.address);
        // Get the next memory size and the gas cost for this memory access
        let (_, memory_cost) = self.memory_expansion.constraints(
            &mut cb,
            state_curr.memory_size.expr(),
            address + 32.expr(),
        );

        // Check if the memory address is too large
        let address_in_range = self
            .address_in_range
            .constraints(&mut cb, address_high::expr(&self.address));
        // Check if the amount of gas available is less than the amount of gas required
        let insufficient_gas = self.insufficient_gas.constraints(
            &mut cb,
            self.gas_available.expr(),
            state_curr.gas_counter.expr() + GAS.expr() + memory_cost,
        );

        // Make sure we are out of gas
        // Out of gas when either the address is too big and/or the amount of gas
        // available is lower than what is required.
        cb.require_zero(address_in_range * (1.expr() - insufficient_gas));

        // Pop the address from the stack
        // We still have to do this to verify the correctness of `address`
        cb.stack_pop(self.address.expr());

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
        // Inputs
        self.address
            .assign(region, offset, Some(step.values[0].to_word()))?;

        // Address in range check
        let address = address_low::value::<F>(step.values[0].to_word());
        self.address_in_range.assign(
            region,
            offset,
            (address as u64).into(),
        )?;

        // Memory expansion
        let address = address_low::value::<F>(step.values[0].to_word());
        let (_memory_size, memory_cost) = self.memory_expansion.assign(
            region,
            offset,
            state.memory_size as u64,
            address + 32,
        )?;

        // Gas insufficient check
        // Get `gas_available` variable here once it's available
        self.insufficient_gas.assign(
            region,
            offset,
            F::from_u64(
                state.gas_counter + GAS.as_u64() + (memory_cost as u64),
            ),
            F::from_bytes(&step.values[1].to_word()).unwrap(),
        )?;

        Ok(())
    }
}

#[derive(Clone, Debug)]
pub(crate) struct MemoryStackUnderflowCase<F> {
    case_selector: Cell<F>,
    is_mstore: IsEqualGadget<F>,
}

impl<F: FieldExt> MemoryStackUnderflowCase<F> {
    pub(crate) const CASE_CONFIG: &'static CaseConfig = &CaseConfig {
        case: Case::StackUnderflow,
        num_word: IsEqualGadget::<F>::NUM_WORDS,
        num_cell: IsEqualGadget::<F>::NUM_CELLS,
        will_halt: true,
    };

    pub(crate) fn construct(alloc: &mut CaseAllocation<F>) -> Self {
        Self {
            case_selector: alloc.selector.clone(),
            is_mstore: IsEqualGadget::construct(alloc),
        }
    }

    pub(crate) fn constraint(
        &self,
        state_curr: &OpExecutionState<F>,
        _state_next: &OpExecutionState<F>,
        name: &'static str,
    ) -> Constraint<F> {
        let mut cb = ConstraintBuilder::default();

        // Check if this is an MLOAD or an MSTORE
        let is_mstore = self.is_mstore.constraints(
            &mut cb,
            state_curr.opcode.expr(),
            OpcodeId::MSTORE.expr(),
        );

        // For MLOAD we only pop one value from the stack,
        // For MSTORE we pop two values from the stack.
        let set =
            vec![STACK_START_IDX.expr(), STACK_START_IDX.expr() - is_mstore];
        cb.require_in_set(state_curr.stack_pointer.expr(), set);

        // Generate the constraint
        cb.constraint(self.case_selector.expr(), name)
    }

    pub(crate) fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        _state: &mut CoreStateInstance,
        step: &ExecutionStep,
    ) -> Result<(), Error> {
        // Check if this is an MLOAD or an MSTORE
        self.is_mstore.assign(
            region,
            offset,
            F::from_u64(step.opcode.as_u8() as u64),
            F::from_u64(OpcodeId::MSTORE.as_u8() as u64),
        )?;
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
        ($execution_steps:expr, $operations:expr, $result:expr) => {{
            let circuit =
                TestCircuit::<Base>::new($execution_steps, $operations);
            let prover = MockProver::<Base>::run(11, &circuit, vec![]).unwrap();
            assert_eq!(prover.verify(), $result);
        }};
    }

    /// Helper to track gc
    /// The `gc` parameter will be modified inside this macro.
    macro_rules! advance_gc {
        ($gc:ident) => {{
            #[allow(unused_assignments, clippy::eval_order_dependence)]
            {
                *$gc += 1;
                *$gc
            }
        }};
    }

    fn compress(bytes: [u8; 32]) -> Base {
        bytes
            .iter()
            .fold(Base::zero(), |acc, val| acc + Base::from_u64(*val as u64))
    }

    fn mstore_ops(
        operations: &mut Vec<Operation<Base>>,
        gc: &mut usize,
        stack_index: u64,
        address: BigUint,
        value: BigUint,
    ) {
        operations.push(Operation {
            gc: advance_gc!(gc),
            target: Target::Stack,
            is_write: true,
            values: [
                Base::zero(),
                Base::from_u64(stack_index),
                compress(value.to_word()),
                Base::zero(),
            ],
        });
        operations.push(Operation {
            gc: advance_gc!(gc),
            target: Target::Stack,
            is_write: true,
            values: [
                Base::zero(),
                Base::from_u64(stack_index - 1),
                compress(address.to_word()),
                Base::zero(),
            ],
        });
        operations.push(Operation {
            gc: advance_gc!(gc),
            target: Target::Stack,
            is_write: false,
            values: [
                Base::zero(),
                Base::from_u64(stack_index - 1),
                compress(address.to_word()),
                Base::zero(),
            ],
        });
        operations.push(Operation {
            gc: advance_gc!(gc),
            target: Target::Stack,
            is_write: false,
            values: [
                Base::zero(),
                Base::from_u64(stack_index),
                compress(value.to_word()),
                Base::zero(),
            ],
        });
        for idx in 0..32 {
            operations.push(Operation {
                gc: advance_gc!(gc),
                target: Target::Memory,
                is_write: true,
                values: [
                    Base::zero(),
                    Base::from_bytes(
                        &(address.clone() + BigUint::from(idx as u64))
                            .to_word(),
                    )
                    .unwrap(),
                    Base::from_u64(
                        value.to_bytes_le()[31 - idx as usize] as u64,
                    ),
                    Base::zero(),
                ],
            });
        }
    }

    fn mload_ops(
        operations: &mut Vec<Operation<Base>>,
        gc: &mut usize,
        stack_index: u64,
        address: BigUint,
        value: BigUint,
    ) {
        operations.push(Operation {
            gc: advance_gc!(gc),
            target: Target::Stack,
            is_write: true,
            values: [
                Base::zero(),
                Base::from_u64(stack_index),
                compress(address.to_word()),
                Base::zero(),
            ],
        });
        operations.push(Operation {
            gc: advance_gc!(gc),
            target: Target::Stack,
            is_write: false,
            values: [
                Base::zero(),
                Base::from_u64(stack_index),
                compress(address.to_word()),
                Base::zero(),
            ],
        });
        operations.push(Operation {
            gc: advance_gc!(gc),
            target: Target::Stack,
            is_write: true,
            values: [
                Base::zero(),
                Base::from_u64(stack_index),
                compress(value.to_word()),
                Base::zero(),
            ],
        });
        for idx in 0..32 {
            operations.push(Operation {
                gc: advance_gc!(gc),
                target: Target::Memory,
                is_write: false,
                values: [
                    Base::zero(),
                    Base::from_bytes(
                        &(address.clone() + BigUint::from(idx as u64))
                            .to_word(),
                    )
                    .unwrap(),
                    Base::from_u64(
                        value.to_bytes_le()[31 - idx as usize] as u64,
                    ),
                    Base::zero(),
                ],
            });
        }
    }

    #[test]
    fn memory_gadget() {
        // Store/Load a value at address 0x12FFFF
        let address_a = BigUint::from(0x12FFFFu64);
        let value_a =
            BigUint::from_bytes_be(&(1u8..33u8).collect::<Vec<u8>>()[..]);

        // Load the memory at address_a + 16 as well
        let address_b = address_a.clone() + BigUint::from(16u64);
        let value_b = BigUint::from_bytes_be(
            &value_a.to_bytes_be()[16..]
                .to_vec()
                .into_iter()
                .chain(
                    vec![0u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
                        .into_iter(),
                )
                .collect::<Vec<u8>>()[..],
        );

        let all_ones = BigUint::from_bytes_le(&[1u8; 32]);

        let execution_steps = vec![
            ExecutionStep {
                opcode: OpcodeId::PUSH32,
                case: Case::Success,
                values: vec![value_a.clone(), all_ones.clone()],
            },
            ExecutionStep {
                opcode: OpcodeId::PUSH32,
                case: Case::Success,
                values: vec![address_a.clone(), all_ones.clone()],
            },
            ExecutionStep {
                opcode: OpcodeId::MSTORE,
                case: Case::Success,
                values: vec![address_a.clone(), value_a.clone()],
            },
            ExecutionStep {
                opcode: OpcodeId::PUSH32,
                case: Case::Success,
                values: vec![address_a.clone(), all_ones.clone()],
            },
            ExecutionStep {
                opcode: OpcodeId::MLOAD,
                case: Case::Success,
                values: vec![address_a.clone(), value_a.clone()],
            },
            ExecutionStep {
                opcode: OpcodeId::PUSH32,
                case: Case::Success,
                values: vec![address_b.clone(), all_ones],
            },
            ExecutionStep {
                opcode: OpcodeId::MLOAD,
                case: Case::Success,
                values: vec![address_b.clone(), value_b.clone()],
            },
        ];

        let mut gc = 0usize;
        let mut operations = vec![];
        mstore_ops(
            &mut operations,
            &mut gc,
            1023u64,
            address_a.clone(),
            value_a.clone(),
        );
        mload_ops(&mut operations, &mut gc, 1023u64, address_a, value_a);
        mload_ops(&mut operations, &mut gc, 1022u64, address_b, value_b);

        try_test_circuit!(execution_steps, operations, Ok(()));
    }
}
