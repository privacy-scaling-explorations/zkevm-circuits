use gadgets::util::{and, not, Expr};
use halo2_proofs::{arithmetic::FieldExt, plonk::VirtualCells, poly::Rotation};
use std::marker::PhantomData;

use crate::{constraints, mpt_circuit::helpers::ColumnTransition};

use super::{helpers::BaseConstraintBuilder, MPTContext};

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
        meta: &mut VirtualCells<'_, F>,
        cb: &mut BaseConstraintBuilder<F>,
        ctx: MPTContext<F>,
    ) -> Self {
        let proof_type = ctx.proof_type;
        let position_cols = ctx.position_cols;
        let is_branch_init = ctx.branch.is_init;
        let account_leaf = ctx.account_leaf;
        let storage_leaf = ctx.storage_leaf;
        let inter_start_root = ctx.inter_start_root;
        let inter_final_root = ctx.inter_final_root;
        let address_rlc = ctx.address_rlc;
        constraints! {[meta, cb], {
            let q_enable = f!(position_cols.q_enable);
            let q_not_first = f!(position_cols.q_not_first);
            let not_first_level = ColumnTransition::new(meta, position_cols.not_first_level);
            let is_branch_init = a!(is_branch_init);
            let is_account_leaf_key_s = a!(account_leaf.is_key_s);
            let is_storage_leaf_key_s = a!(storage_leaf.is_s_key);
            let is_storage_leaf_last_row_prev = a!(storage_leaf.is_non_existing, -1);
            let is_account_leaf_last_row_prev = a!(account_leaf.is_in_added_branch, -1);
            let is_non_storage_mod_proof_type_prev = not::expr(a!(proof_type.is_storage_mod, -1));

            let start_root = ColumnTransition::new(meta, inter_start_root);
            let final_root = ColumnTransition::new(meta, inter_final_root);
            let address_rlc = ColumnTransition::new(meta, address_rlc);

            let is_branch_or_account_leaf = is_account_leaf_key_s.expr() + is_branch_init.expr();

            ifx!{q_enable => {
                ifx!{not::expr(q_not_first.expr()) => {
                    // In the first row, it needs to be `not_first_level = 0`. The selector `q_not_first`
                    // is a fixed column, so can rely on it we are really in the first row.
                    // Two nodes can appear in the first level: account leaf or branch / extension node.
                    // The storage leaf cannot appear as it requires to have an account leaf above it
                    // (a separate constraint for this).
                    // Here, we check for the case when the account leaf / branch/extension node is in the first level.
                    ifx!{is_branch_or_account_leaf => {
                        require!(not_first_level => 0);
                    }}
                } elsex {
                    // When there is a last storage leaf row in the previous row, in the current row it needs
                    // to be `not_first_level = 1` (we are in account leaf/branch init).
                    ifx!{is_branch_or_account_leaf, not::expr(is_storage_leaf_last_row_prev.expr()) => {
                        require!(not_first_level => 1);
                    }}
                    // When there is a last account leaf row in the previous row and the proof is about
                    // non storage modification (proof ends with account leaf),
                    // in the current row it needs to be `not_first_level = 1` (we are in account leaf/branch init).
                    ifx!{is_branch_or_account_leaf, is_non_storage_mod_proof_type_prev, not::expr(is_account_leaf_last_row_prev.expr()) => {
                        require!(not_first_level => 1);
                    }}
                    // If `not_first_level` is 0 in a previous row (being in branch init),
                    // then `not_first_level` needs to be 1 in the current row (preventing two consecutive
                    // blocks to be `not_first_level = 0`).
                    ifx!{is_branch_init, not::expr(not_first_level.prev())  => {
                        require!(not_first_level => 1);
                    }}
                    // `not_first_level` can change only in `is_branch_init` or `is_account_leaf_key_s` or
                    // `is__leaf_key_s`.
                    // Note that the change `not_first_level = 1` to `not_first_level = 0` (going to the first level)
                    // is covered by the constraints above which constrain when such a change can occur.
                    // On the other hand, this constraint ensured that `not_first_level` is changed in the middle
                    // of the node rows.
                    ifx!{not::expr(is_branch_init.expr()), not::expr(is_account_leaf_key_s.expr()), not::expr(is_storage_leaf_key_s.expr()) => {
                        require!(not_first_level.cur() => not_first_level.prev());
                    }}

                    // `start_root`/`final_root` can change only in the first row of the first level.
                    // We check that it stays the same always except when `not_first_level_prev = not_first_level_cur + 1`,
                    // that means when `not_first_level` goes from 1 to 0.
                    ifx!{not_first_level.prev() - (not_first_level.cur() + 1.expr())  => {
                        require!(start_root.cur() => start_root.prev());
                        require!(final_root.cur() => final_root.prev());
                    }}
                    // When we go from one modification to another, the previous `final_root` needs to be
                    // the same as the current `start_root`.
                    ifx!{not_first_level.prev(), not::expr(not_first_level.cur())  => {
                        require!(final_root.prev() => start_root.cur());
                    }}

                    // It needs to be ensured there is an account proof before the
                    // storage proof. Otherwise the attacker could use only a storage proof with a properly
                    // set `address_rlc` (storage mod lookup row contains `val_prev`, `val_cur`, `key_rlc`,
                    // `address_rlc`) and it would not be detected that the account proof has not validated
                    // (was not there).
                    // We make sure `address_rlc = 0` at the beginning of the proof (except if it is
                    // the account leaf which already have set the proper `address_rlc`). This makes sure
                    // that there is a step where `address_rlc` is set to the proper value. This step
                    // should happen in the account leaf first row (there is a separate constraint that
                    // allows `address_rlc` to be changed only in the account leaf first row).
                    // So to have the proper `address_rlc` we have to have an account leaf (and thus an account proof).
                    // If the attacker would try to use a storage proof without an account proof, the first
                    // storage proof node would need to be denoted by `not_first_level = 0` (otherwise
                    // constraints related to `not_first_level` would fail - there needs to be `not_firstl_level = 0`
                    // after the end of the previous proof). But then if this node is a branch, this constraint
                    // would make sure that `address_rlc = 0`. As `address_rlc` cannot be changed later on
                    // in the storage proof, the lookup will fail (except for the negligible probability that
                    // the lookup really requires `address_rlc = 0`). If the first node is a storage leaf, we
                    // need to ensure in a separate constraint that `address_rlc = 0` in this case too.
                    // First row of first level can be (besides `branch_init`) also `is_account_leaf_key_s`,
                    // but in this case `address_rlc` needs to be set.
                    // Ensuring that the storage proof cannot be used without the account proof - in case the storage
                    // proof would consist only of a storage leaf.
                    ifx!{is_branch_init.expr() + is_storage_leaf_key_s.expr(), not::expr(not_first_level.cur())  => {
                        require!(address_rlc => 0);
                    }}
                    // It needs to be ensured that `address_rlc` changes only at the first row of the account leaf
                    // or in the branch init row if it is in the first level.
                    ifx!{not::expr(is_account_leaf_key_s.expr()), is_branch_init.expr() - (not_first_level.cur() + 1.expr()) => {
                        require!(address_rlc.cur() => address_rlc.prev());
                    }}
                }}

                // TODO: check public roots to match with first and last inter roots
            }}
        }}

        ProofChainConfig {
            _marker: PhantomData,
        }
    }
}
