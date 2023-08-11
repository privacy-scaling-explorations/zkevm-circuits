use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        step::ExecutionState,
        util::{
            common_gadget::SameContextGadget,
            constraint_builder::{EVMConstraintBuilder, StepStateTransition, Transition::Delta},
            CachedRegion, Cell,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    util::Expr,
};
use eth_types::{evm_types::OpcodeId, Field};
use halo2_proofs::{circuit::Value, plonk::Error};

#[derive(Clone, Debug)]
pub(crate) struct DummyPush0Gadget<F> {
    same_context: SameContextGadget<F>,
    opcode: Cell<F>,
}

impl<F: Field> ExecutionGadget<F> for DummyPush0Gadget<F> {
    const NAME: &'static str = "PUSH0";

    const EXECUTION_STATE: ExecutionState = ExecutionState::PUSH0;

    fn configure(cb: &mut EVMConstraintBuilder<F>) -> Self {
        let opcode = cb.query_cell();
        // The dummy gadget only push the zero value on the stack(increase the stack pointer by 1)
        cb.stack_push(0.expr());

        // State transition
        // `program_counter` needs to be increased by number of bytes pushed + 1
        let step_state_transition = StepStateTransition {
            rw_counter: Delta(1.expr()),
            program_counter: Delta(1.expr()),
            stack_pointer: Delta((-1).expr()),
            gas_left: Delta(-OpcodeId::PUSH0.constant_gas_cost().expr()),
            ..Default::default()
        };
        // SameContextGadget will increase the program_counter by 1
        let same_context = SameContextGadget::construct(cb, opcode.clone(), step_state_transition);

        Self {
            same_context,
            opcode,
        }
    }

    fn assign_exec_step(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        _: &Block<F>,
        _: &Transaction,
        _: &Call,
        step: &ExecStep,
    ) -> Result<(), Error> {
        self.same_context.assign_exec_step(region, offset, step)?;
        let opcode = step.opcode().unwrap();
        self.opcode
            .assign(region, offset, Value::known(F::from(opcode.as_u64())))?;
        Ok(())
    }
}
