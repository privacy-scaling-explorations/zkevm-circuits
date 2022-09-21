use halo2_proofs::{
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed},
    poly::Rotation,
};
use pairing::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::{storage_leaf::StorageLeafCols, account_leaf::AccountLeafCols, columns::ProofTypeCols};

/*
The selector `not_first_level` denotes whether the node is not in the first account trie level.
Thus, each account modification proof starts with `not_first_level = 0` rows.
However, a fixed column cannot be used because the first level can appear at different rows in different
proofs. Instead, an advice column is used, but it needs to be ensured that there cannot be any rogue
assignments.

Potential attacks:
 - `not_first_level` is assigned to 1 in the first level of the proof. This way the attacker could avoid
    checking that the hash of the first level node is the same as the trie root, which would make
    the proof meaningless. We prevent this by ensuring the first row has `not_first_level = 0`
    (for the first row we have a fixed column selector), that after the storage leaf (proof
    ends with a storage leaf or account leaf) there is a row with `not_first_level = 0`,
    and that after the account leaf when it is non storage modification there
    is a row with `not_first_level = 0`.


Note: Comparing the roots with the hash of branch / extension node in the first level
(or account leaf if in the first level) is done in `branch_hash_in_parent.rs`, `extension_node.rs`
(or `account_leaf_storage_codehash.rs` if the account leaf is in the first level).
*/
#[derive(Clone, Debug)]
pub(crate) struct ProofChainConfig<F> {
    _marker: PhantomData<F>,
}

impl<F: FieldExt> ProofChainConfig<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        proof_type: ProofTypeCols<F>,
        q_enable: Column<Fixed>,
        q_not_first: Column<Fixed>,
        not_first_level: Column<Advice>,
        is_branch_init: Column<Advice>,
        account_leaf: AccountLeafCols<F>,
        storage_leaf: StorageLeafCols<F>,
        inter_start_root: Column<Advice>,
        inter_final_root: Column<Advice>,
        address_rlc: Column<Advice>,
    ) -> Self {
        let config = ProofChainConfig { _marker: PhantomData };

        meta.create_gate("Proof chaining constraints", |meta| {
            let mut constraints = vec![];

            let q_enable = meta.query_fixed(q_enable, Rotation::cur());
            let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
            let not_first_level_prev = meta.query_advice(not_first_level, Rotation::prev());
            let not_first_level_cur = meta.query_advice(not_first_level, Rotation::cur());
            let is_branch_init = meta.query_advice(is_branch_init, Rotation::cur());
            let is_account_leaf_key_s = meta.query_advice(account_leaf.is_key_s, Rotation::cur());
            let is_storage_leaf_key_s = meta.query_advice(storage_leaf.is_s_key, Rotation::cur());
            let is_storage_leaf_last_row_prev = meta.query_advice(storage_leaf.is_in_added_branch, Rotation::prev());
            let is_account_leaf_last_row_prev = meta.query_advice(account_leaf.is_in_added_branch, Rotation::prev());

            let one = Expression::Constant(F::one());
            let is_non_storage_mod_proof_type_prev = one.clone() - meta.query_advice(proof_type.is_storage_mod, Rotation::prev());

            let start_root_prev = meta.query_advice(inter_start_root, Rotation::prev());
            let start_root_cur = meta.query_advice(inter_start_root, Rotation::cur());
            let final_root_prev = meta.query_advice(inter_final_root, Rotation::prev());
            let final_root_cur = meta.query_advice(inter_final_root, Rotation::cur());

            let address_rlc_prev = meta.query_advice(address_rlc, Rotation::prev());
            let address_rlc_cur = meta.query_advice(address_rlc, Rotation::cur());

            /*
            In the first row, it needs to be `not_first_level = 0`. The selector `q_not_first`
            is a fixed column, so can rely on it we are really in the first row.

            Two nodes can appear in the first level: account leaf or branch / extension node.
            The storage leaf cannot appear as it requires to have an account leaf above it
            (a separate constraint for this).
            Here, we check for the case when the account leaf is in the first level.
            */
            constraints.push((
                "First row needs to have not_first_level = 0 (account leaf key)",
                q_enable.clone() * is_account_leaf_key_s.clone() * (one.clone() - q_not_first.clone()) * not_first_level_cur.clone(),
            ));

            /*
            In the first row, it needs to be `not_first_level = 0`. The selector `q_not_first`
            is a fixed column, so can rely on it we are really in the first row.

            Two nodes can appear in the first level: account leaf or branch / extension node.
            The storage leaf cannot appear as it requires to have an account leaf above it
            (a separate constraint for this).
            Here, we check for the case when the branch / extension node is in the first level.
            */
            constraints.push((
                "First row needs to have not_first_level = 0 (branch init)",
                q_enable.clone() * (one.clone() - q_not_first.clone()) * is_branch_init.clone() * not_first_level_cur.clone(),
            ));

            /*
            When there is a last storage leaf row in the previous row, in the current row it needs
            to be `not_first_level = 0` (we are in account leaf).
            */
            constraints.push((
                "not_first_level = 0 follows the last storage leaf row (account leaf)",
                q_not_first.clone() // for the first row, we already have a constraint for not_first_level = 0
                    * is_account_leaf_key_s.clone()
                    * (one.clone() - not_first_level_cur.clone())
                    * (one.clone() - is_storage_leaf_last_row_prev.clone()),
            ));

            /*
            When there is a last storage leaf row in the previous row, in the current row it needs
            to be `not_first_level = 0` (we are in branch init).
            */
            constraints.push((
                "not_first_level = 0 follows the last storage leaf row (branch init)",
                q_not_first.clone() // for the first row, we already have a constraint for not_first_level = 0
                    * is_branch_init.clone()
                    * (one.clone() - not_first_level_cur.clone())
                    * (one.clone() - is_storage_leaf_last_row_prev),
            ));

            /*
            When there is a last account leaf row in the previous row and the proof is about
            non storage modification (proof ends with account leaf),
            in the current row it needs to be `not_first_level = 0` (we are in account leaf).
            */
            constraints.push((
                "not_first_level = 0 follows the last account leaf row when non storage mod proof (account leaf)",
                q_not_first.clone() // for the first row, we already have a constraint for not_first_level = 0
                    * is_account_leaf_key_s.clone()
                    * (one.clone() - not_first_level_cur.clone())
                    * is_non_storage_mod_proof_type_prev.clone()
                    * (one.clone() - is_account_leaf_last_row_prev.clone()),
            ));

            /*
            When there is a last account leaf row in the previous row and the proof is about
            non storage modification (proof ends with account leaf),
            in the current row it needs to be `not_first_level = 0` (we are in branch init).
            */
            constraints.push((
                "not_first_level = 0 follows the last account leaf row when non storage mod proof (branch init)",
                q_not_first.clone() // for the first row, we already have a constraint for not_first_level = 0
                    * is_branch_init.clone()
                    * (one.clone() - not_first_level_cur.clone())
                    * is_non_storage_mod_proof_type_prev.clone()
                    * (one.clone() - is_account_leaf_last_row_prev.clone()),
            ));

            constraints.push((
                "start_root does not change when not in first level",
                q_not_first.clone()
                    * not_first_level_cur.clone()
                    * (start_root_cur.clone() - start_root_prev.clone()),
            ));

            constraints.push((
                "start_root does not change when in first level and (not in account leaf key || not in branch init)",
                q_not_first.clone()
                    * (one.clone() - not_first_level_cur.clone())
                    * (one.clone() - is_branch_init.clone())
                    * (one.clone() - is_account_leaf_key_s.clone())
                    * (start_root_cur.clone() - start_root_prev.clone()),
            ));

            constraints.push((
                "final_root does not change when not in first level",
                q_not_first.clone()
                    * not_first_level_cur.clone()
                    * (final_root_cur.clone() - final_root_prev.clone()),
            ));

            constraints.push((
                "final_root does not change when in first level and (not in account leaf key || not in branch init)",
                q_not_first.clone()
                    * (one.clone() - not_first_level_cur.clone())
                    * (one.clone() - is_branch_init.clone())
                    * (one.clone() - is_account_leaf_key_s.clone())
                    * (final_root_cur.clone() - final_root_prev.clone()),
            ));

            constraints.push((
                "final_root_prev = start_root_cur when not_first_level = 1 -> not_first_level = 0",
                q_not_first.clone()
                    * not_first_level_prev.clone()
                    * (one.clone() - not_first_level_cur.clone())
                    * (final_root_prev.clone() - start_root_cur.clone()),
            )); 

            // If not_first_level is 0 in a previous row (being in branch init),
            // then not_first_level needs to be 1 in the current row (preventing two consecutive
            // blocks to be not_first_level = 0).
            constraints.push((
                "not_first_level 0 -> 1 in branch init",
                q_not_first.clone()
                    * is_branch_init.clone()
                    * (one.clone() - not_first_level_prev.clone())
                    * (not_first_level_cur.clone() - one.clone()),
            ));

            // Note that not_first_level can change in is_branch_init or is_account_leaf.
            // The attacker could thus insert more first levels, but there will be
            // `start_root/end_root` used in lookups which will prevent this scenario.
            // Also, the attacker could potentially put first levels at wrong places, but then
            // address/key RLC constraints would fail.
            constraints.push((
                "not_first_level does not change except at is_branch_init or is_account_leaf_key_s or is_storage_leaf_key_s",
                q_not_first.clone()
                    * (one.clone() - is_branch_init.clone())
                    * (one.clone() - is_account_leaf_key_s.clone())
                    * (one.clone() - is_storage_leaf_key_s.clone()) // when storage proof doesn't have branches/extension nodes
                    * (not_first_level_cur.clone() - not_first_level_prev.clone()),
            )); 
  
            // These two address_rlc constraints are to ensure there is account proof before the
            // storage proof.
            constraints.push((
                // First row of first level can be (besides branch_init) also is_account_leaf_key_s,
                // but in this case the constraint in account_leaf_key.rs is triggered.
                "address_rlc is 0 in first row of first level",
                q_not_first.clone()
                    * (one.clone() - not_first_level_cur.clone())
                    * is_branch_init.clone()
                    * address_rlc_cur.clone()
            ));
            constraints.push((
                "address_rlc does not change except at is_account_leaf_key_s or branch init in first level",
                q_not_first.clone()
                    * (one.clone() - is_account_leaf_key_s.clone())
                    * (is_branch_init.clone() - not_first_level_cur.clone() - one.clone()) // address_rlc goes back to 0 in branch init in first level
                    * (address_rlc_cur.clone() - address_rlc_prev.clone())
            ));

            // TODO: check public roots to match with first and last inter roots

            constraints
        });

        config
    }
}