// Port this to a macro if possible to avoid defining all the PushN
use super::{Opcode, OpcodeId};
use crate::{
    evm::{ExecutionStep, GlobalCounter},
    operation::{bus_mapping::BusMappingInstance, container::OperationContainer, StackOp, RW},
};
use ff::Field;
use halo2::plonk::ConstraintSystem;

#[derive(Debug, Copy, Clone)]
pub(crate) struct Push1;

impl Into<OpcodeId> for Push1 {
    fn into(self) -> OpcodeId {
        OpcodeId::PUSH1
    }
}

impl<'a, F: Field> Opcode<'a, F> for Push1 {
    fn gen_associated_operations(
        exec_step: &'a ExecutionStep<'a>,
        container: &'a mut OperationContainer,
    ) -> BusMappingInstance<'a> {
        // Push1 generates 1 Stack Write
        let write = StackOp::new(
            RW::WRITE,
            GlobalCounter::from(exec_step.gc().0 + 1),
            exec_step.stack_addr(),
            exec_step.stack()[exec_step.stack_addr().0].clone(),
        );
        let mut bm_inst = BusMappingInstance::new();
        bm_inst.insert(container.insert(write.into()));

        bm_inst
    }

    #[allow(unused_variables)]
    fn add_constraints(exec_step: &ExecutionStep<'a>, cs: &mut ConstraintSystem<F>) {
        unimplemented!()
    }
}
