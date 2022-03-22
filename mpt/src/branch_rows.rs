use halo2_proofs::{
    circuit::Chip,
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed},
    poly::Rotation,
};
use pairing::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::{helpers::hash_expr_into_rlc, param::HASH_WIDTH};

#[derive(Clone, Debug)]
pub(crate) struct BranchRowsConfig {}

pub(crate) struct BranchRowsChip<F> {
    config: BranchRowsConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> BranchRowsChip<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_not_first: Column<Fixed>,
        is_branch_child: Column<Advice>,
        mod_node_hash_rlc: Column<Advice>,
        advices: [Column<Advice>; HASH_WIDTH],
        node_index: Column<Advice>,
        is_modified: Column<Advice>,
        is_at_drifted_pos: Column<Advice>,
        sel: Column<Advice>,
        acc_r: F,
    ) -> BranchRowsConfig {
        let config = BranchRowsConfig {};

        meta.create_gate("Branch rows", |meta| {
            let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());

            let mut constraints = vec![];
            let is_branch_child_cur = meta.query_advice(is_branch_child, Rotation::cur());

            let node_index_cur = meta.query_advice(node_index, Rotation::cur());

            // mod_node_hash_rlc is the same for all is_branch_child rows.
            // This is to enable easier comparison when in leaf row
            // where we need to compare the keccak output is the same as keccak of the
            // modified node, this way we just rotate back to one of the branch
            // children rows and we get mod_node_hash_rlc there (otherwise we
            // would need iterate over all branch children rows (many rotations) and check
            // that at is_modified the value corresponds).
            let mod_node_hash_rlc_prev = meta.query_advice(mod_node_hash_rlc, Rotation::prev());
            let mod_node_hash_cur = meta.query_advice(mod_node_hash_rlc, Rotation::cur());
            constraints.push((
                "mod_node_hash_rlc the same for all branch children",
                q_not_first.clone()
                    * is_branch_child_cur.clone()
                    * node_index_cur.clone() // ignore if node_index = 0 (there is no previous)
                    * (mod_node_hash_cur.clone() - mod_node_hash_rlc_prev),
            ));

            // s_mod_node_hash_rlc and c_mode_node_hash_rlc correspond to RLC of s_advices
            // and c_advices at the modified index
            let is_modified = meta.query_advice(is_modified, Rotation::cur());
            let is_at_drifted_pos = meta.query_advice(is_at_drifted_pos, Rotation::cur());

            // When it's NOT placeholder branch, is_modified = is_at_drifted_pos.
            // When it's placeholder branch, is_modified != is_at_drifted_pos.
            // This is used instead of having is_branch_s_placeholder and
            // is_branch_c_placeholder columns - we only have this info in
            // branch init where we don't need additional columns.

            let mut sc_hash = vec![];
            // Note: storage root is always in s_advices!
            for column in advices.iter() {
                sc_hash.push(meta.query_advice(*column, Rotation::cur()));
            }
            let hash_rlc = hash_expr_into_rlc(&sc_hash, acc_r);

            // In placeholder branch (when is_modified != is_at_drifted_pos) the following
            // constraint could be satisfied by the attacker by putting hash of is_modified
            // (while it should be is_at_drifted_pos), but then the attacker
            // would need to use is_modified node for leaf_key_in_added_branch
            // (hash of it is in keccak at is_at_drifted_pos), but then the
            // constraint of leaf_in_added_branch having the same key except for
            // the first nibble (and extension node nibbles if extension node) would fail.
            let mod_node_hash_rlc_cur = meta.query_advice(mod_node_hash_rlc, Rotation::cur());
            // Needs to correspond when is_modified or is_at_drifted_pos.
            constraints.push((
                "mod_node_hash_rlc correspond to advices at the modified index",
                q_not_first.clone()
                        * is_branch_child_cur.clone()
                        * is_at_drifted_pos.clone() // is_at_drifted_pos = is_modified when NOT placeholder
                        * is_modified.clone()
                        * (hash_rlc.clone() - mod_node_hash_rlc_cur),
            ));

            // sel - denoting whether leaf is empty at modified_node.
            // When sel = 1, *_advices need to be [128, 0, ..., 0].
            // If sel = 1, there is no leaf at this position (value is being added or
            // deleted) and we don't check the hash of it in leaf_value.

            let c128 = Expression::Constant(F::from(128));
            let sel_prev = meta.query_advice(sel, Rotation::prev());
            let sel_cur = meta.query_advice(sel, Rotation::cur());

            // advices[0] = 128
            let advices0 = meta.query_advice(advices[0], Rotation::cur());
            constraints.push((
                "branch child sel *_advices0",
                q_not_first.clone()
                    * is_branch_child_cur.clone()
                    * is_modified.clone()
                    * (advices0 - c128.clone())
                    * sel_cur.clone(),
            ));
            // advices[i] = 0 for i > 0
            for column in advices.iter().skip(1) {
                let s = meta.query_advice(*column, Rotation::cur());
                constraints.push((
                    "branch child sel *_advices",
                    q_not_first.clone()
                        * is_branch_child_cur.clone()
                        * is_modified.clone()
                        * s
                        * sel_cur.clone(),
                ));
            }

            constraints.push((
                "sel the same for all branch children",
                q_not_first.clone()
                    * is_branch_child_cur.clone()
                    * node_index_cur.clone() // ignore if node_index = 0 (there is no previous)
                    * (sel_cur - sel_prev),
            ));

            constraints
        });

        config
    }

    pub fn construct(config: BranchRowsConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }
}

impl<F: FieldExt> Chip<F> for BranchRowsChip<F> {
    type Config = BranchRowsConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}
