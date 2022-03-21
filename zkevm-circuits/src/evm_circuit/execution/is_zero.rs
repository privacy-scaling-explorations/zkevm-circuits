use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        step::ExecutionState,
        util::{
            common_gadget::SameContextGadget,
            constraint_builder::{ConstraintBuilder, StepStateTransition, Transition::Delta},
            math_gadget, Word,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    util::Expr,
};
use bus_mapping::evm::OpcodeId;
use eth_types::{Field, ToLittleEndian};
use halo2_proofs::{circuit::Region, plonk::Error};

#[derive(Clone, Debug)]
pub(crate) struct IsZeroGadget<F> {
    same_context: SameContextGadget<F>,
    is_zero: math_gadget::IsZeroGadget<F>,
}

impl<F: Field> ExecutionGadget<F> for IsZeroGadget<F> {
    const NAME: &'static str = "ISZERO";

    const EXECUTION_STATE: ExecutionState = ExecutionState::ISZERO;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        let opcode = cb.query_cell();

        let a = cb.query_word();
        let is_zero = math_gadget::IsZeroGadget::construct(cb, a.expr());

        cb.stack_pop(a.expr());
        cb.stack_push(is_zero.expr());

        // State transition
        let step_state_transition = StepStateTransition {
            rw_counter: Delta(2.expr()),
            program_counter: Delta(1.expr()),
            stack_pointer: Delta(0.expr()),
            gas_left: Delta(-OpcodeId::ISZERO.constant_gas_cost().expr()),
            ..StepStateTransition::default()
        };
        let same_context = SameContextGadget::construct(cb, opcode, step_state_transition);

        Self {
            same_context,
            is_zero,
        }
    }

    fn assign_exec_step(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        block: &Block<F>,
        _: &Transaction,
        _: &Call,
        step: &ExecStep,
    ) -> Result<(), Error> {
        self.same_context.assign_exec_step(region, offset, step)?;

        let a = block.rws[step.rw_indices[0]].stack_value();
        let a = Word::random_linear_combine(a.to_le_bytes(), block.randomness);
        self.is_zero.assign(region, offset, a)?;

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::test_util::run_test_circuits;
    use eth_types::{bytecode, Word};

    fn test_ok(a: Word) {
        let bytecode = bytecode! {
            PUSH32(a)
            ISZERO
            STOP
        };
        assert_eq!(run_test_circuits(bytecode), Ok(()));
    }

    #[test]
    fn is_zero_gadget() {
        test_ok(0x060504.into());
        test_ok(0x0.into());
    }
}
