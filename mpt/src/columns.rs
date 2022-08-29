use std::{convert::{TryFrom}, marker::PhantomData};
use halo2_proofs::{circuit::Region, plonk::{Error, Advice, Column, ConstraintSystem}, arithmetic::FieldExt};
use num_enum::TryFromPrimitive;

// This file contains columns that are not specific to any of account leaf, storage leaf, branch, or
// extension node.

#[derive(Clone, Debug)]
pub(crate) struct ProofTypeCols<F> {
    pub(crate) is_storage_mod: Column<Advice>,
    pub(crate) is_nonce_mod: Column<Advice>,
    pub(crate) is_balance_mod: Column<Advice>,
    pub(crate) is_account_delete_mod: Column<Advice>,
    pub(crate) is_non_existing_account_proof: Column<Advice>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> ProofTypeCols<F> {
    pub(crate) fn new(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            is_storage_mod : meta.advice_column(),
            is_nonce_mod : meta.advice_column(),
            is_balance_mod : meta.advice_column(),
            is_account_delete_mod : meta.advice_column(),
            is_non_existing_account_proof : meta.advice_column(),
            _marker: PhantomData,
        }
    }
}

