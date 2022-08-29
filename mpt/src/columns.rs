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

#[derive(Clone, Debug)]
pub(crate) struct AccumulatorPair<F> {
    pub(crate) rlc: Column<Advice>,
    pub(crate) mult: Column<Advice>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> AccumulatorPair<F> {
    pub(crate) fn new(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            rlc: meta.advice_column(),
            mult: meta.advice_column(),
            _marker: PhantomData,
        }
    }
}

// Columns that store values that are being accumulated across multiple rows.
#[derive(Clone, Debug)]
pub(crate) struct AccumulatorCols<F> {
    pub(crate) acc_s: AccumulatorPair<F>, // accumulating RLC for a node in S proof
    pub(crate) acc_c: AccumulatorPair<F>, // accumulating RLC for a node in C proof
    // key.rlc & key.mult used for account address, for storage key,
    // for mult_diff_nonce/mult_diff_balance in account_leaf_nonce_balance
    pub(crate) key: AccumulatorPair<F>, // accumulating RLC for address or key
    pub(crate) node_mult_diff_s: Column<Advice>, // used when accumulating branch RLC for non-hashed nodes in a branch
    pub(crate) node_mult_diff_c: Column<Advice>, // used when accumulating branch RLC for non-hashed nodes in a branch
    pub(crate) mult_diff: Column<Advice>, // power of randomness r: multiplier_curr = multiplier_prev * mult_diff (used for example for diff due to extension node nibbles)
    pub(crate) s_mod_node_rlc: Column<Advice>, // modified node s_advices RLC, TODO: used also for leaf long/short, check whether some DenoteCol could be used
    pub(crate) c_mod_node_rlc: Column<Advice>, // modified node c_advices RLC, TODO: used also for leaf long/short, check whether some DenoteCol could be used
    _marker: PhantomData<F>,
}

impl<F: FieldExt> AccumulatorCols<F> {
    pub(crate) fn new(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            acc_s: AccumulatorPair::new(meta),
            acc_c: AccumulatorPair::new(meta),
            key: AccumulatorPair::new(meta),
            node_mult_diff_s: meta.advice_column(),
            node_mult_diff_c: meta.advice_column(),
            mult_diff: meta.advice_column(),
            s_mod_node_rlc: meta.advice_column(),
            c_mod_node_rlc: meta.advice_column(),
            _marker: PhantomData,
        }
    }
}