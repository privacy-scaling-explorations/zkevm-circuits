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
    pub(crate) is_codehash_proof: Column<Advice>, // no modification possible, we only need S or C proof
    pub(crate) is_account_delete_mod: Column<Advice>,
    pub(crate) is_non_existing_account_proof: Column<Advice>, // we only need S or C proof as there is no modification
    _marker: PhantomData<F>,
}

impl<F: FieldExt> ProofTypeCols<F> {
    pub(crate) fn new(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            is_storage_mod : meta.advice_column(),
            is_nonce_mod : meta.advice_column(),
            is_balance_mod : meta.advice_column(),
            is_codehash_proof : meta.advice_column(),
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

/*
Columns that denote what kind of a row it is. These columns are used in different columns for
different purposes (as opposed to for example branch.is_child - having dedicated columns simplifies
ensuring the order of rows is corrrect, like branch.is_init appears only once and is followed
by branch.is_child ... ). For example, columns sel1, sel2 are used for denoting whether
the branch child is at modified node or whether the storage leaf is in short or long RLP format.
*/
#[derive(Clone, Debug)]
pub(crate) struct DenoteCols<F> {
    // sel1 and sel2 in branch children: denote whether there is no leaf at is_modified (when value
    // is added or deleted from trie - but no branch is added or turned into leaf)
    // sel1 and sel2 in storage leaf key: key_rlc_prev and key_rlc_mult_prev
    // sel1 and sel2 in storage leaf value (only when leaf without branch as otherwise this info is
    // in the branch above): whether leaf is just a placeholder
    // sel1 and sel2 in account leaf key specifies whether nonce / balance are short / long (check
    // nonce balance row: offset - 1)
    pub(crate) sel1: Column<Advice>, // TODO: check LeafKeyChip where sel1 stores key_rlc_prev, sel2 stores key_rlc_mult_prev
    pub(crate) sel2: Column<Advice>,
    pub(crate) is_node_hashed_s: Column<Advice>,
    pub(crate) is_node_hashed_c: Column<Advice>,
    _marker: PhantomData<F>,
}

// TODO: check whether sel1, sel2 are sometimes used for accumulated values and fix it.

impl<F: FieldExt> DenoteCols<F> {
    pub(crate) fn new(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            sel1: meta.advice_column(),
            sel2: meta.advice_column(),
            is_node_hashed_s: meta.advice_column(),
            is_node_hashed_c: meta.advice_column(),
            _marker: PhantomData,
        }
    }
}