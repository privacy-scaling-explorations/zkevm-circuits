pub mod account_leaf_key;
pub mod account_leaf_key_in_added_branch;
pub mod account_leaf_nonce_balance;
pub mod account_leaf_storage_codehash;
pub mod account_non_existing;

use halo2_proofs::{
    arithmetic::FieldExt,
    plonk::{Advice, Column, ConstraintSystem},
};
use std::marker::PhantomData;

#[derive(Clone, Debug)]
pub(crate) struct AccountLeafCols<F> {
    pub(crate) is_key_s: Column<Advice>,
    pub(crate) is_key_c: Column<Advice>,
    pub(crate) is_non_existing: Column<Advice>,
    pub(crate) is_nonce_balance_s: Column<Advice>,
    pub(crate) is_nonce_balance_c: Column<Advice>,
    pub(crate) is_storage_codehash_s: Column<Advice>,
    pub(crate) is_storage_codehash_c: Column<Advice>,
    pub(crate) is_in_added_branch: Column<Advice>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> AccountLeafCols<F> {
    pub(crate) fn new(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            is_key_s: meta.advice_column(),
            is_key_c: meta.advice_column(),
            is_non_existing: meta.advice_column(),
            is_nonce_balance_s: meta.advice_column(),
            is_nonce_balance_c: meta.advice_column(),
            is_storage_codehash_s: meta.advice_column(),
            is_storage_codehash_c: meta.advice_column(),
            is_in_added_branch: meta.advice_column(),
            _marker: PhantomData,
        }
    }
}

#[derive(Default, Debug)]
pub(crate) struct AccountLeaf {
    pub(crate) is_key_s: bool,
    pub(crate) is_key_c: bool,
    pub(crate) is_non_existing_account_row: bool,
    pub(crate) is_nonce_balance_s: bool,
    pub(crate) is_nonce_balance_c: bool,
    pub(crate) is_storage_codehash_s: bool,
    pub(crate) is_storage_codehash_c: bool,
    pub(crate) is_in_added_branch: bool,
}
