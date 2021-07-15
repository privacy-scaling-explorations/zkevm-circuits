//! Reusable gadgets for the zk_evm circuits.
use halo2::circuit::Cell;
use pasta_curves::arithmetic::FieldExt;

/// An assigned cell in the circuit.
#[derive(Clone, Debug)]
pub(crate) struct Variable<T, F: FieldExt> {
    pub(crate) cell: Cell,
    pub(crate) field_elem: Option<F>,
    pub(crate) value: Option<T>,
}

pub(crate) mod monotone;
