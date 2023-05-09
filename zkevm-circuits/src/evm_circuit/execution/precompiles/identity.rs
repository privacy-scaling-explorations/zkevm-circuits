use bus_mapping::circuit_input_builder::{Call, CopyDataType};
use eth_types::{evm_types::GasCost, Field};
use gadgets::util::Expr;
use halo2_proofs::plonk::Error;

use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        step::ExecutionState,
        util::{
            common_gadget::RestoreContextGadget, constraint_builder::EVMConstraintBuilder,
            memory_gadget::MemoryCopierGasGadget, CachedRegion, Cell,
        },
    },
    table::CallContextFieldTag,
    witness::{Block, ExecStep, Transaction},
};

#[derive(Clone, Debug)]
pub struct IdentityGadget<F> {
    is_success: Cell<F>,
    callee_address: Cell<F>,
    caller_id: Cell<F>,
    call_data_offset: Cell<F>,
    call_data_length: Cell<F>,
    return_data_offset: Cell<F>,
    return_data_length: Cell<F>,
    copier_gadget: MemoryCopierGasGadget<F, { GasCost::PRECOMPILE_IDENTITY_PER_WORD }>,
    restore_context: RestoreContextGadget<F>,
}

impl<F: Field> ExecutionGadget<F> for IdentityGadget<F> {
    const EXECUTION_STATE: ExecutionState = ExecutionState::PrecompileIdentity;

    const NAME: &'static str = "IDENTITY";

    fn configure(cb: &mut EVMConstraintBuilder<F>) -> Self {
        let callee_address = cb.query_cell();
        cb.call_context_lookup(
            false.expr(),
            None,
            CallContextFieldTag::CalleeAddress,
            callee_address.expr(),
        );

        cb.precompile_info_lookup(
            cb.execution_state().as_u64().expr(),
            callee_address.expr(),
            GasCost::PRECOMPILE_IDENTITY_BASE.expr(),
        );

        let [is_success, caller_id, call_data_offset, call_data_length, return_data_offset, return_data_length] =
            [
                CallContextFieldTag::IsSuccess,
                CallContextFieldTag::CallerId,
                CallContextFieldTag::CallDataOffset,
                CallContextFieldTag::CallDataLength,
                CallContextFieldTag::ReturnDataOffset,
                CallContextFieldTag::ReturnDataLength,
            ]
            .map(|tag| cb.call_context(None, tag));

        let copier_gadget = MemoryCopierGasGadget::construct(
            cb,
            call_data_length.expr(),
            0.expr(), // no memory expansion.
        );
        let total_gas_cost = GasCost::PRECOMPILE_IDENTITY_BASE.expr() + copier_gadget.gas_cost();

        // copy table lookup to verify the copying of bytes from caller's memory (starting at
        // calldata offset) to caller's memory (starting at returndata offset). Condition guarded
        // only if the precompile call was successful.
        cb.condition(is_success.expr(), |cb| {
            cb.copy_table_lookup(
                caller_id.expr(),
                CopyDataType::Memory.expr(),
                caller_id.expr(),
                CopyDataType::Memory.expr(),
                call_data_offset.expr(),
                call_data_offset.expr() + call_data_length.expr(),
                return_data_offset.expr(),
                return_data_length.expr(),
                0.expr(),
                0.expr(),
            );
        });

        let restore_context = RestoreContextGadget::construct(
            cb,
            is_success.expr(),       // the call could fail if gas was insufficient.
            0.expr(),                // no more RW lookups.
            0.expr(),                // return data offset for precompile call.
            call_data_length.expr(), // return data length for precompile call.
            total_gas_cost.expr(),   // gas cost for precompile call.
            0.expr(),                // reversible RW counter does not increase.
        );

        Self {
            is_success,
            callee_address,
            caller_id,
            call_data_offset,
            call_data_length,
            return_data_offset,
            return_data_length,
            copier_gadget,
            restore_context,
        }
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
        unimplemented!()
    }
}
