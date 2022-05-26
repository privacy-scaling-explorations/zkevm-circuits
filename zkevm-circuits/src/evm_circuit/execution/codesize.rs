use bus_mapping::evm::OpcodeId;
use eth_types::Field;
use halo2_proofs::plonk::Error;

use crate::{
    evm_circuit::{
        step::ExecutionState,
        util::{
            common_gadget::SameContextGadget,
            constraint_builder::{ConstraintBuilder, StepStateTransition, Transition},
            CachedRegion, Cell, RandomLinearCombination,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    util::Expr,
};

use super::ExecutionGadget;

#[derive(Clone, Debug)]
pub(crate) struct CodesizeGadget<F> {
    same_context: SameContextGadget<F>,
    codesize: Cell<F>,
}

impl<F: Field> ExecutionGadget<F> for CodesizeGadget<F> {
    const NAME: &'static str = "CODESIZE";

    const EXECUTION_STATE: ExecutionState = ExecutionState::CODESIZE;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        let opcode = cb.query_cell();

        let code_hash = cb.curr.state.code_hash.clone();
        let codesize = cb.bytecode_length(code_hash.expr());
        let codesize_rlc = RandomLinearCombination::random_linear_combine_expr(
            [codesize.expr()],
            cb.power_of_randomness(),
        );

        cb.require_equal(
            "Constraint: code size (bytecode table) == stack top",
            codesize_rlc.expr(),
            codesize.expr(),
        );

        cb.stack_push(codesize_rlc);

        let step_state_transition = StepStateTransition {
            gas_left: Transition::Delta(-OpcodeId::CODESIZE.constant_gas_cost().expr()),
            rw_counter: Transition::Delta(1.expr()),
            program_counter: Transition::Delta(1.expr()),
            stack_pointer: Transition::Delta((-1).expr()),
            ..Default::default()
        };
        let same_context = SameContextGadget::construct(cb, opcode, step_state_transition);

        Self {
            same_context,
            codesize,
        }
    }

    fn assign_exec_step(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        block: &Block<F>,
        _transaction: &Transaction,
        _call: &Call,
        step: &ExecStep,
    ) -> Result<(), Error> {
        self.same_context.assign_exec_step(region, offset, step)?;

        let codesize = block.rws[step.rw_indices[0]].stack_value().as_u64();
        self.codesize
            .assign(region, offset, Some(F::from(codesize)))?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use eth_types::bytecode;
    use mock::TestContext;

    use crate::test_util::run_test_circuits;

    #[test]
    fn test_codesize_gadget() {
        let code = bytecode! {
            PUSH1(0x20)
            PUSH1(0x30)
            ADD
            POP
            CALLER
            CODESIZE
            STOP
        };

        assert_eq!(
            run_test_circuits(
                TestContext::<2, 1>::simple_ctx_with_bytecode(code).unwrap(),
                None
            ),
            Ok(())
        );
    }
}
