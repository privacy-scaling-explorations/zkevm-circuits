use bus_mapping::circuit_input_builder::{Call, CopyDataType};
use eth_types::{evm_types::GasCost, Field, ToScalar};
use gadgets::util::{and, not, Expr};
use halo2_proofs::{circuit::Value, plonk::Error};

use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        step::ExecutionState,
        util::{
            common_gadget::RestoreContextGadget, constraint_builder::EVMConstraintBuilder,
            math_gadget::IsZeroGadget, memory_gadget::MemoryCopierGasGadget, CachedRegion, Cell,
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
    call_data_length_zero: IsZeroGadget<F>,
    return_data_length_zero: IsZeroGadget<F>,
    copier_gadget: MemoryCopierGasGadget<F, { GasCost::PRECOMPILE_IDENTITY_PER_WORD }>,
    restore_context: RestoreContextGadget<F>,
}

impl<F: Field> ExecutionGadget<F> for IdentityGadget<F> {
    const EXECUTION_STATE: ExecutionState = ExecutionState::PrecompileIdentity;

    const NAME: &'static str = "IDENTITY";

    fn configure(cb: &mut EVMConstraintBuilder<F>) -> Self {
        let [is_success, callee_address, caller_id, call_data_offset, call_data_length, return_data_offset, return_data_length] =
            [
                CallContextFieldTag::IsSuccess,
                CallContextFieldTag::CalleeAddress,
                CallContextFieldTag::CallerId,
                CallContextFieldTag::CallDataOffset,
                CallContextFieldTag::CallDataLength,
                CallContextFieldTag::ReturnDataOffset,
                CallContextFieldTag::ReturnDataLength,
            ]
            .map(|tag| cb.call_context(None, tag));

        cb.precompile_info_lookup(
            cb.execution_state().as_u64().expr(),
            callee_address.expr(),
            GasCost::PRECOMPILE_IDENTITY_BASE.expr(),
        );

        let copier_gadget = MemoryCopierGasGadget::construct(
            cb,
            call_data_length.expr(),
            0.expr(), // no memory expansion.
        );
        let total_gas_cost = GasCost::PRECOMPILE_IDENTITY_BASE.expr() + copier_gadget.gas_cost();

        let (call_data_length_zero, return_data_length_zero) = (
            IsZeroGadget::construct(cb, call_data_length.expr()),
            IsZeroGadget::construct(cb, return_data_length.expr()),
        );

        // copy table lookup to verify the copying of bytes:
        // - from caller's memory (`call_data_length` bytes starting at `call_data_offset`)
        // - to the current call's memory (`call_data_length` bytes starting at `0`).
        cb.condition(not::expr(call_data_length.expr()), |cb| {
            cb.copy_table_lookup(
                caller_id.expr(),
                CopyDataType::Memory.expr(),
                cb.curr.state.call_id.expr(),
                CopyDataType::Memory.expr(),
                call_data_offset.expr(),
                call_data_offset.expr() + call_data_length.expr(),
                0.expr(),
                call_data_length.expr(),
                0.expr(),
                0.expr(),
            );
        });

        // copy table lookup to verify the copying of bytes if the precompile call was successful.
        // - from precompile call's memory (`return_data_length` bytes starting at `0`)
        // - to caller's memory (`return_data_length` bytes starting at `return_data_offset`).
        cb.condition(
            and::expr([
                is_success.expr(),
                not::expr(call_data_length_zero.expr()),
                not::expr(return_data_length_zero.expr()),
            ]),
            |cb| {
                cb.copy_table_lookup(
                    cb.curr.state.call_id.expr(),
                    CopyDataType::Memory.expr(),
                    caller_id.expr(),
                    CopyDataType::Memory.expr(),
                    0.expr(),
                    return_data_length.expr(),
                    return_data_offset.expr(),
                    return_data_length.expr(),
                    0.expr(),
                    0.expr(),
                );
            },
        );

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
            call_data_length_zero,
            return_data_length_zero,
            copier_gadget,
            restore_context,
        }
    }

    fn assign_exec_step(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        block: &Block<F>,
        _tx: &Transaction,
        call: &Call,
        step: &ExecStep,
    ) -> Result<(), Error> {
        self.is_success.assign(
            region,
            offset,
            Value::known(F::from(u64::from(call.is_success))),
        )?;
        self.callee_address.assign(
            region,
            offset,
            Value::known(call.code_address().unwrap().to_scalar().unwrap()),
        )?;
        self.caller_id.assign(
            region,
            offset,
            Value::known(F::from(call.caller_id.try_into().unwrap())),
        )?;
        self.call_data_offset.assign(
            region,
            offset,
            Value::known(F::from(call.call_data_offset)),
        )?;
        self.call_data_length.assign(
            region,
            offset,
            Value::known(F::from(call.call_data_length)),
        )?;
        self.return_data_offset.assign(
            region,
            offset,
            Value::known(F::from(call.return_data_offset)),
        )?;
        self.return_data_length.assign(
            region,
            offset,
            Value::known(F::from(call.return_data_length)),
        )?;
        self.call_data_length_zero
            .assign(region, offset, F::from(call.call_data_length))?;
        self.return_data_length_zero
            .assign(region, offset, F::from(call.return_data_length))?;
        self.copier_gadget
            .assign(region, offset, call.call_data_length, 0)?;
        self.restore_context
            .assign(region, offset, block, call, step, 0)?;

        Ok(())
    }
}
