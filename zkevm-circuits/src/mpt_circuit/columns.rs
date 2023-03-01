use eth_types::Field;
use halo2_proofs::{
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, VirtualCells},
    poly::Rotation,
};
use std::{convert::TryInto, marker::PhantomData};

use crate::{circuit_tools::constraint_builder::RLCable, mpt_circuit::param::HASH_WIDTH};

/*
This file contains columns that are not specific to any of account leaf, storage leaf, branch,
or extension node.
*/

/*
proof_type:
NonceMod = 1
BalanceMod = 2
CodeHashMod = 3
NonExistingAccountProof = 4
AccountDeleteMod = 5
StorageMod = 6
NonExistingStorageProof = 7
*/
#[derive(Clone, Copy, Debug)]
pub(crate) struct ProofTypeCols<F> {
    pub(crate) proof_type: Column<Advice>, /* between 1 and 6, should correspond to the columns
                                            * below (it enables lookups with less columns) */
    pub(crate) is_storage_mod: Column<Advice>,
    pub(crate) is_nonce_mod: Column<Advice>,
    pub(crate) is_balance_mod: Column<Advice>,
    pub(crate) is_codehash_mod: Column<Advice>,
    pub(crate) is_account_delete_mod: Column<Advice>,
    pub(crate) is_non_existing_account_proof: Column<Advice>, /* we only need C proof as
                                                               * there is no modification */
    pub(crate) is_non_existing_storage_proof: Column<Advice>, /* we only need C proof as
                                                               * there is no modification */
    _marker: PhantomData<F>,
}

impl<F: Field> ProofTypeCols<F> {
    pub(crate) fn new(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            proof_type: meta.advice_column(),
            is_storage_mod: meta.advice_column(),
            is_nonce_mod: meta.advice_column(),
            is_balance_mod: meta.advice_column(),
            is_codehash_mod: meta.advice_column(),
            is_account_delete_mod: meta.advice_column(),
            is_non_existing_account_proof: meta.advice_column(),
            is_non_existing_storage_proof: meta.advice_column(),
            _marker: PhantomData,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct MainCols<F> {
    // Main as opposed to other columns which are selectors and RLC accumulators.
    pub(crate) rlp1: Column<Advice>,
    pub(crate) rlp2: Column<Advice>,
    pub(crate) bytes: [Column<Advice>; HASH_WIDTH],
    _marker: PhantomData<F>,
}

impl<F: Field> MainCols<F> {
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

    pub(crate) fn rlp_bytes(&self) -> Vec<Column<Advice>> {
        [[self.rlp1, self.rlp2].to_vec(), self.bytes.to_vec()]
            .concat()
            .to_vec()
    }

    pub(crate) fn rlc(
        &self,
        meta: &mut VirtualCells<F>,
        rot: i32,
        r: &Vec<Expression<F>>,
    ) -> Expression<F> {
        self.expr(meta, rot).rlc(r)
    }

    pub(crate) fn bytes(&self, meta: &mut VirtualCells<F>, rot: i32) -> Vec<Expression<F>> {
        self.bytes
            .iter()
            .map(|&byte| meta.query_advice(byte, Rotation(rot)))
            .collect::<Vec<_>>()
    }

    pub(crate) fn expr(&self, meta: &mut VirtualCells<F>, rot: i32) -> Vec<Expression<F>> {
        self.rlp_bytes()
            .iter()
            .map(|&byte| meta.query_advice(byte, Rotation(rot)))
            .collect::<Vec<_>>()
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct PositionCols<F> {
    pub(crate) q_enable: Column<Fixed>,
    pub(crate) q_not_first: Column<Fixed>, // not first row
    pub(crate) not_first_level: Column<Advice>,

    _marker: PhantomData<F>,
}

impl<F: Field> PositionCols<F> {
    pub(crate) fn new(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            q_enable: meta.fixed_column(),
            q_not_first: meta.fixed_column(),
            not_first_level: meta.advice_column(),
            _marker: PhantomData,
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct MPTTable {
    pub(crate) address_rlc: Column<Advice>,
    pub(crate) proof_type: Column<Advice>,
    pub(crate) key_rlc: Column<Advice>,
    pub(crate) value_prev: Column<Advice>,
    pub(crate) value: Column<Advice>,
    pub(crate) root_prev: Column<Advice>,
    pub(crate) root: Column<Advice>,
}
