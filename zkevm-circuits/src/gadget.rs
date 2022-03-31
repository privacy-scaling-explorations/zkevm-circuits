//! Reusable gadgets for the zk_evm circuits.
use halo2_proofs::circuit::AssignedCell;
use pairing::arithmetic::FieldExt;

/// An assigned cell in the circuit.
#[derive(Clone, Debug)]
pub(crate) struct Variable<T, F: FieldExt> {
    pub(crate) assig_cell: AssignedCell<F, F>,
    pub(crate) value: Option<T>,
}

impl<T, F: FieldExt> Variable<T, F> {
    pub(crate) fn new(assig_cell: AssignedCell<F, F>, value: Option<T>) -> Self {
        Self { assig_cell, value }
    }
}

pub(crate) mod evm_word;
pub(crate) mod is_zero;
pub(crate) mod monotone;
