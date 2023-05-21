use bus_mapping::circuit_input_builder::{Call, CopyDataType};
use eth_types::{evm_types::GasCost, Field, ToScalar};
use gadgets::util::{and, not, Expr};
use halo2_proofs::{circuit::Value, plonk::Error};

use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        step::ExecutionState,
        util::{
            constraint_builder::EVMConstraintBuilder, math_gadget::IsZeroGadget,
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
    call_data_length_zero: IsZeroGadget<F>,
    return_data_length_zero: IsZeroGadget<F>,
    copier_gadget: MemoryCopierGasGadget<F, { GasCost::PRECOMPILE_IDENTITY_PER_WORD }>,
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
        let _total_gas_cost = GasCost::PRECOMPILE_IDENTITY_BASE.expr() + copier_gadget.gas_cost();

        let (call_data_length_zero, return_data_length_zero) = (
            IsZeroGadget::construct(cb, call_data_length.expr()),
            IsZeroGadget::construct(cb, return_data_length.expr()),
        );

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
                    2.expr() * return_data_length.expr(), // reads + writes
                );
            },
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
        }
    }

    fn assign_exec_step(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        _block: &Block<F>,
        _tx: &Transaction,
        call: &Call,
        _step: &ExecStep,
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

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use eth_types::bytecode;
    use mock::TestContext;

    use crate::test_util::CircuitTestBuilder;

    #[test]
    fn precompile_identity_test() {
        let bytecode = bytecode! {
            // place params in memory
            PUSH1(0xff)
            PUSH1(0x00)
            MSTORE
            // do static call to 0x04
            PUSH1(0x01)
            PUSH1(0x3f)
            PUSH1(0x01)
            PUSH1(0x1f)
            PUSH1(0x04)
            PUSH1(0xff)
            STATICCALL
            // put result on the stack
            POP
            PUSH1(0x20)
            MLOAD
        };

        CircuitTestBuilder::new_from_test_ctx(
            TestContext::<2, 1>::simple_ctx_with_bytecode(bytecode).unwrap(),
        )
        .run();
    }
}
