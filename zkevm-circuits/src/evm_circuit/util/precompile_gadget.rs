use bus_mapping::precompile::PrecompileCalls;
use eth_types::Field;
use gadgets::util::{not, Expr};
use halo2_proofs::plonk::Expression;

use crate::evm_circuit::step::{ExecutionState, ExecutionState::ErrorOutOfGasPrecompile};

use super::{
    constraint_builder::{BoxedClosure, ConstrainBuilderCommon, EVMConstraintBuilder},
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
        _is_success: Expression<F>,
        callee_address: Expression<F>,
        _caller_id: Expression<F>,
        _cd_offset: Expression<F>,
        cd_length: Expression<F>,
        _rd_offset: Expression<F>,
        _rd_length: Expression<F>,
        precompile_return_length: Expression<F>,
        // input bytes to precompile call.
        _input_bytes_rlc: Expression<F>,
        // output result from precompile call.
        _output_bytes_rlc: Expression<F>,
        // returned bytes back to caller.
        _return_bytes_rlc: Expression<F>,
    ) -> Self {
        let address = BinaryNumberGadget::construct(cb, callee_address.expr());

        let conditions = vec![
            address.value_equals(PrecompileCalls::Identity),
            // match more precompiles
        ]
        .into_iter()
        .map(|cond| {
            cond.expr() * not::expr(cb.next.execution_state_selector([ErrorOutOfGasPrecompile]))
        })
        .collect::<Vec<_>>();

        let next_states = vec![
            ExecutionState::PrecompileIdentity
            // add more precompile execution states
        ];

        let constraints: Vec<BoxedClosure<F>> = vec![
            Box::new(|cb| {
                /* Identity */
                cb.require_equal(
                    "input length and precompile return length are the same",
                    cd_length,
                    precompile_return_length
                );
            })
            // add more precompile constraint closures
        ];

        cb.constrain_mutually_exclusive_next_step(conditions, next_states, constraints);

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
