use halo2_proofs::{
    circuit::Chip,
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, Selector},
    poly::Rotation,
};
use pairing::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::{helpers::hash_expr_into_rlc, param::HASH_WIDTH};

#[derive(Clone, Debug)]
pub(crate) struct BranchParallelConfig {}

// Branch constraints that need to be applied on both parallel proofs in the
// same way.
pub(crate) struct BranchParallelChip<F> {
    config: BranchParallelConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> BranchParallelChip<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: Selector,
        q_not_first: Column<Fixed>,
        is_branch_child: Column<Advice>,
        mod_node_hash_rlc: Column<Advice>,
        rlp2: Column<Advice>,
        advices: [Column<Advice>; HASH_WIDTH],
        node_index: Column<Advice>,
        is_modified: Column<Advice>,
        is_at_drifted_pos: Column<Advice>,
        sel: Column<Advice>,
        acc_r: F,
    ) -> BranchParallelConfig {
        let config = BranchParallelConfig {};

        // Empty nodes have 0 at *_rlp2, have 128 at *_advices[0] and 0 everywhere else:
        // [0, 0, 128, 0, ..., 0]
        // While non-empty nodes have 160 at *_rlp2 and then any byte at *_advices:
        // [0, 160, a0, ..., a31]
        meta.create_gate("empty and non-empty", |meta| {
            let q_enable = meta.query_selector(q_enable);
            let mut constraints = vec![];

            let is_branch_child_cur = meta.query_advice(is_branch_child, Rotation::cur());
            let rlp2 = meta.query_advice(rlp2, Rotation::cur());

            // Note that s_rlp1 and c_rlp1 store RLP stream length data (subtracted
            // by the number of bytes in branch rows until that position).

            let c128 = Expression::Constant(F::from(128_u64));
            let c160 = Expression::Constant(F::from(160_u64));

            // In empty nodes: rlp2 = 0. In non-empty nodes: rlp2 = 160.
            constraints.push((
                "*_rlp2 = 0 or *_rlp2 = 160",
                q_enable.clone()
                    * is_branch_child_cur.clone()
                    * rlp2.clone()
                    * (rlp2.clone() - c160.clone()),
            ));

            // No further constraints needed for non-empty nodes (rlp2 needs to be 160
            // and values need to be bytes which is constrained by the lookups
            // on s_advices and c_advices).

            let advice0 = meta.query_advice(advices[0], Rotation::cur());
            constraints.push((
                "*_advices[0] = 128 in empty",
                q_enable.clone()
                    * is_branch_child_cur.clone()
                    * (rlp2.clone() - c160.clone())
                    * (advice0 - c128.clone()), /* If *_rlp2 = 0, then s_advices[0] can be any
                                                 * value (0-255). */
            ));

            for col in advices.iter().skip(1) {
                let s = meta.query_advice(*col, Rotation::cur());
                constraints.push((
                    "*_advices[i] = 0 for i > 0 in empty",
                    q_enable.clone()
                        * is_branch_child_cur.clone()
                        * (rlp2.clone() - c160.clone())
                        * s,
                ));
            }

            // Note that the attacker could put 160 in an empty node (the constraints
            // above doesn't/can't prevent this) and thus try to
            // modify the branch RLC (used for checking the hash of a branch), like:
            // [0, 160, 128, 0, ..., 0]
            // But then the constraints related to branch RLP would fail - first RLP bytes
            // specifies the length of the stream and this value is checked with
            // the actual length - the actual length being computed as 33 values in
            // non-empty nodes and 1 value in empty node.

            constraints
        });

        meta.create_gate("Branch hash & sel", |meta| {
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

    pub fn construct(config: BranchParallelConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }
}

impl<F: FieldExt> Chip<F> for BranchParallelChip<F> {
    type Config = BranchParallelConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}
