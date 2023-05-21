use bus_mapping::precompile::PrecompileCalls;
use eth_types::Field;
use gadgets::util::Expr;
use halo2_proofs::plonk::Expression;

use crate::evm_circuit::step::ExecutionState;

use super::{
    constraint_builder::{ConstrainBuilderCommon, EVMConstraintBuilder},
    math_gadget::BinaryNumberGadget,
    CachedRegion,
};

#[derive(Clone, Debug)]
pub struct PrecompileGadget<F> {
    address: BinaryNumberGadget<F, 4>,
}

impl<F: Field> PrecompileGadget<F> {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn construct(
        cb: &mut EVMConstraintBuilder<F>,
        is_success: Expression<F>,
        callee_address: Expression<F>,
        caller_id: Expression<F>,
        call_data_offset: Expression<F>,
        call_data_length: Expression<F>,
        return_data_offset: Expression<F>,
        return_data_length: Expression<F>,
    ) -> Self {
        let address = BinaryNumberGadget::construct(cb, callee_address.expr());

        cb.condition(address.value_equals(PrecompileCalls::Identity), |cb| {
            cb.constrain_next_step(ExecutionState::PrecompileIdentity, None, |cb| {
                let precomp_is_success = cb.query_cell();
                let precomp_callee_address = cb.query_cell();
                let precomp_caller_id = cb.query_cell();
                let precomp_call_data_offset = cb.query_cell();
                let precomp_call_data_length = cb.query_cell();
                let precomp_return_data_offset = cb.query_cell();
                let precomp_return_data_length = cb.query_cell();
                cb.require_equal(
                    "precompile call is_success check",
                    is_success,
                    precomp_is_success.expr(),
                );
                cb.require_equal(
                    "precompile call callee_address check",
                    callee_address,
                    precomp_callee_address.expr(),
                );
                cb.require_equal(
                    "precompile call caller_id check",
                    caller_id,
                    precomp_caller_id.expr(),
                );
                cb.require_equal(
                    "precompile call call_data_offset check",
                    call_data_offset,
                    precomp_call_data_offset.expr(),
                );
                cb.require_equal(
                    "precompile call call_data_length check",
                    call_data_length,
                    precomp_call_data_length.expr(),
                );
                cb.require_equal(
                    "precompile call return_data_offset check",
                    return_data_offset,
                    precomp_return_data_offset.expr(),
                );
                cb.require_equal(
                    "precompile call return_data_length check",
                    return_data_length,
                    precomp_return_data_length.expr(),
                );
            });
        });

        Self { address }
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        address: PrecompileCalls,
    ) -> Result<(), halo2_proofs::plonk::Error> {
        self.address.assign(region, offset, address)
    }
}