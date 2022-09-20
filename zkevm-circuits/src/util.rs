//! Common utility traits and functions.
use halo2_proofs::{
    plonk::{ConstraintSystem, Expression},
    poly::Rotation,
};

use crate::{evm_circuit::util::Cell, table::TxLogFieldTag};
use eth_types::{Field, ToAddress};
pub use ethers_core::types::{Address, U256};
pub use gadgets::util::Expr;

pub(crate) fn random_linear_combine_word<F: Field>(bytes: [u8; 32], randomness: F) -> F {
    crate::evm_circuit::util::Word::random_linear_combine(bytes, randomness)
}

/// Query N instances at current rotation and return their expressions.  This
/// function is used to get the power of randomness (passed as
/// instances) in our tests.
pub fn power_of_randomness_from_instance<F: Field, const N: usize>(
    meta: &mut ConstraintSystem<F>,
) -> [Expression<F>; N] {
    // This gate is used just to get the array of expressions from the power of
    // randomness instance column, so that later on we don't need to query
    // columns everywhere, and can pass the power of randomness array
    // expression everywhere.  The gate itself doesn't add any constraints.

    let columns = [(); N].map(|_| meta.instance_column());
    let mut power_of_randomness = None;

    meta.create_gate("power of randomness from instance", |meta| {
        power_of_randomness =
            Some(columns.map(|column| meta.query_instance(column, Rotation::cur())));

        [0.expr()]
    });

    power_of_randomness.unwrap()
}

pub(crate) fn build_tx_log_address(index: u64, field_tag: TxLogFieldTag, log_id: u64) -> Address {
    (U256::from(index) + (U256::from(field_tag as u64) << 32) + (U256::from(log_id) << 48))
        .to_address()
}

pub(crate) fn build_tx_log_from_expr_to_expression<F: halo2_proofs::arithmetic::FieldExt>(
    index: Expression<F>,
    field_tag: Expression<F>,
    log_id: Expression<F>,
) -> Expression<F> {
    index + (1u64 << 32).expr() * field_tag + ((1u64 << 48).expr()) * log_id
}

pub(crate) fn build_tx_log_expression<F: halo2_proofs::arithmetic::FieldExt>(
    index: u64,
    field_tag: TxLogFieldTag,
    log_id: &Cell<F>,
) -> Expression<F> {
    if index != 0 {
        build_tx_log_from_expr_to_expression(index.expr(), field_tag.expr(), log_id.expr())
    } else {
        (1u64 << 32).expr() * field_tag.expr() + ((1u64 << 48).expr()) * log_id.expr()
    }
}
