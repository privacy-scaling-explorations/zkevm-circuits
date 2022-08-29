use std::{marker::PhantomData, convert::TryInto};
use halo2_proofs::{plonk::{Advice, Column, ConstraintSystem}, arithmetic::FieldExt};

use crate::param::HASH_WIDTH;

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

#[derive(Clone, Debug)]
pub(crate) struct MainCols<F> { // Main as opposed to other columns which are selectors and RLC accumulators.
    pub(crate) rlp1: Column<Advice>,
    pub(crate) rlp2: Column<Advice>,
    pub(crate) bytes: [Column<Advice>; HASH_WIDTH],
    _marker: PhantomData<F>,
}

impl<F: FieldExt> MainCols<F> {
    pub(crate) fn new(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            rlp1: meta.advice_column(),
            rlp2: meta.advice_column(),
            bytes: (0..HASH_WIDTH)
                .map(|_| meta.advice_column())
                .collect::<Vec<_>>()
                .try_into()
                .unwrap(),
            _marker: PhantomData,
        }
    }
}