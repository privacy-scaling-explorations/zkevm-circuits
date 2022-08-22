use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        step::ExecutionState,
        util::{
            common_gadget::SameContextGadget,
            constraint_builder::{ConstraintBuilder, StepStateTransition, Transition::Delta},
            CachedRegion
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    util::Expr,
};
use bus_mapping::evm::OpcodeId;
use eth_types::Field;
use halo2_proofs::plonk::Error;

#[derive(Clone, Debug)]
pub(crate) struct BlockHashGadget<F> {
    same_context: SameContextGadget<F>,
}

impl<F: Field> ExecutionGadget<F> for BlockHashGadget<F> {
    const NAME: &'static str = "BLOCKHASH";

    const EXECUTION_STATE: ExecutionState = ExecutionState::BLOCKHASH;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        
        let step_state_transition = StepStateTransition {
            rw_counter: Delta(2.expr()),
            program_counter: Delta(1.expr()),
            gas_left: Delta(-OpcodeId::BLOCKHASH.constant_gas_cost().expr()),
            ..Default::default()
        };

        let opcode = cb.query_cell();
        let same_context = SameContextGadget::construct(cb, opcode, step_state_transition);
        Self { same_context }
    }

    fn assign_exec_step(
            &self,
            region: &mut CachedRegion<'_, '_, F>,
            offset: usize,
            block: &Block<F>,
            transaction: &Transaction,
            call: &Call,
            step: &ExecStep,
        ) -> Result<(), Error> {
            self.same_context.assign_exec_step(region, offset, step)?;
            
            Ok(())
    }
}