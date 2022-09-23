use halo2_proofs::{
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed},
    poly::Rotation,
};
use pairing::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::{account_leaf::AccountLeafCols, columns::{ProofTypeCols, PositionCols}, storage_leaf::StorageLeafCols};

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
 - `not_first_level` is assigned to 0 in the middle of the proof - in this case the address RLC
   constraints fail.
 - Additional proof is added between the proofs (we have more `not_first_level = 0` than expected) -
   in this case the `start_root/final_root` lookups will fail.
 - Proof without account proof part (only having storage proof) - the attacker could omit the witness
   for account proof and thus avoid any account related checks. This is prevented with constraints
   that ensure there is always an account proof before the storage proof.

It needs to be ensured that `start_root` and `final_root` change only in the first row of
the `not_first_level = 0` node.

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
        position_cols: PositionCols<F>,
        is_branch_init: Column<Advice>,
        account_leaf: AccountLeafCols<F>,
        storage_leaf: StorageLeafCols<F>,
        inter_start_root: Column<Advice>,
        inter_final_root: Column<Advice>,
        address_rlc: Column<Advice>,
    ) -> Self {
        let config = ProofChainConfig {
            _marker: PhantomData,
        };

        meta.create_gate("Proof chaining constraints", |meta| {
            let mut constraints = vec![];

            let q_enable = meta.query_fixed(position_cols.q_enable, Rotation::cur());
            let q_not_first = meta.query_fixed(position_cols.q_not_first, Rotation::cur());
            let not_first_level_prev = meta.query_advice(position_cols.not_first_level, Rotation::prev());
            let not_first_level_cur = meta.query_advice(position_cols.not_first_level, Rotation::cur());
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
                q_enable * (one.clone() - q_not_first.clone()) * is_branch_init.clone() * not_first_level_cur.clone(),
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
                    * is_non_storage_mod_proof_type_prev
                    * (one.clone() - is_account_leaf_last_row_prev),
            ));

            /*
            `not_first_level` can change only in `is_branch_init` or `is_account_leaf_key_s` or
            `is__leaf_key_s`.

            Note that the change `not_first_level = 1` to `not_first_level = 0` (going to the first level)
            is covered by the constraints above which constrain when such a change can occur.
            On the other hand, this constraint ensured that `not_first_level` is changed in the middle
            of the node rows.
            */
            constraints.push((
                "not_first_level does not change except at is_branch_init or is_account_leaf_key_s or is_storage_leaf_key_s",
                q_not_first.clone()
                    * (one.clone() - is_branch_init.clone())
                    * (one.clone() - is_account_leaf_key_s.clone())
                    * (one.clone() - is_storage_leaf_key_s.clone())
                    * (not_first_level_cur.clone() - not_first_level_prev.clone()),
            ));

            /*
            `start_root` can change only in the first row of the first level.
            We check that it stays the same always except when `not_first_level_prev = not_first_level_cur + 1`,
            that means when `not_first_level` goes from 1 to 0.
            */
            constraints.push((
                "start_root can change only when in the first row of the first level",
                q_not_first.clone()
                    * (not_first_level_prev.clone() - not_first_level_cur.clone() - one.clone())
                    * (start_root_cur.clone() - start_root_prev),
            ));

            /*
            `final_root` can change only in the first row of the first level.
            We check that it stays the same always except when `not_first_level_prev = not_first_level_cur + 1`,
            that means when `not_first_level` goes from 1 to 0.
            */
            constraints.push((
                "final_root can change only when in the first row of the first level",
                q_not_first.clone()
                    * (not_first_level_prev.clone() - not_first_level_cur.clone() - one.clone())
                    * (final_root_cur - final_root_prev.clone()),
            ));

            /*
            When we go from one modification to another, the previous `final_root` needs to be
            the same as the current `start_root`.
            */
            constraints.push((
                "final_root_prev = start_root_cur when not_first_level = 1 -> not_first_level = 0",
                q_not_first.clone()
                    * not_first_level_prev.clone()
                    * (one.clone() - not_first_level_cur.clone())
                    * (final_root_prev - start_root_cur),
            )); 

            /*
            If `not_first_level` is 0 in a previous row (being in branch init),
            then `not_first_level` needs to be 1 in the current row (preventing two consecutive
            blocks to be `not_first_level = 0`).
            */
            constraints.push((
                "not_first_level 0 -> 1 in branch init after the first level",
                q_not_first.clone()
                    * is_branch_init.clone()
                    * (one.clone() - not_first_level_prev)
                    * (not_first_level_cur.clone() - one.clone()),
            ));
 
            /*
            It needs to be ensured there is an account proof before the
            storage proof. Otherwise the attacker could use only a storage proof with a properly
            set `address_rlc` (storage mod lookup row contains `val_prev`, `val_cur`, `key_rlc`,
            `address_rlc`) and it would not be detected that the account proof has not validated
            (was not there).

            We make sure `address_rlc = 0` at the beginning of the proof (except if it is
            the account leaf which already have set the proper `address_rlc`). This makes sure
            that there is a step where `address_rlc` is set to the proper value. This step
            should happen in the account leaf first row (there is a separate constraint that
            allows `address_rlc` to be changed only in the account leaf first row).
            So to have the proper `address_rlc` we have to have an account leaf (and thus an account proof).

            If the attacker would try to use a storage proof without an account proof, the first
            storage proof node would need to be denoted by `not_first_level = 0` (otherwise
            constraints related to `not_first_level` would fail - there needs to be `not_firstl_level = 0`
            after the end of the previous proof). But then if this node is a branch, this constraint
            would make sure that `address_rlc = 0`. As `address_rlc` cannot be changed later on
            in the storage proof, the lookup will fail (except for the negligible probability that
            the lookup really requires `address_rlc = 0`). If the first node is a storage leaf, we
            need to ensure in a separate constraint that `address_rlc = 0` in this case too.
            */
            constraints.push((
                /*
                First row of first level can be (besides `branch_init`) also `is_account_leaf_key_s`,
                but in this case `address_rlc` needs to be set.
                */
                "address_rlc is 0 in first row of first level",
                q_not_first.clone()
                    * (one.clone() - not_first_level_cur.clone())
                    * is_branch_init.clone()
                    * address_rlc_cur.clone()
            ));

            /*
            Ensuring that the storage proof cannot be used without the account proof - in case the storage
            proof would consist only of a storage leaf.
            */
            constraints.push((
                "address_rlc is 0 in first row of first level when in storage leaf",
                q_not_first.clone()
                    * (one.clone() - not_first_level_cur.clone())
                    * is_storage_leaf_key_s
                    * address_rlc_cur.clone()
            ));

            /*
            It needs to be ensured that `address_rlc` changes only at the first row of the account leaf 
            or in the branch init row if it is in the first level.
            */
            constraints.push((
                "address_rlc does not change except at is_account_leaf_key_s or branch init in first level",
                q_not_first
                    * (one.clone() - is_account_leaf_key_s)
                    * (is_branch_init - not_first_level_cur - one) // address_rlc goes back to 0 in branch init in first level
                    * (address_rlc_cur - address_rlc_prev)
            ));

            // TODO: check public roots to match with first and last inter roots

            constraints
        });

        config
    }
}
