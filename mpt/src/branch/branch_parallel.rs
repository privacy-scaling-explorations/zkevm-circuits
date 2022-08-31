use halo2_proofs::{
    circuit::Chip,
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, VirtualCells},
    poly::Rotation,
};
use pairing::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::{helpers::{bytes_expr_into_rlc, key_len_lookup}, columns::{MainCols, AccumulatorCols}};

use super::BranchCols;

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
        q_enable: Column<Fixed>,
        q_not_first: Column<Fixed>,
        branch: BranchCols<F>,
        accs: AccumulatorCols<F>,
        main: MainCols<F>,
        sel: Column<Advice>,
        is_node_hashed: Column<Advice>,
        is_s: bool,
    ) -> BranchParallelConfig {
        let config = BranchParallelConfig {};
            
        let one = Expression::Constant(F::from(1_u64));

        // Empty nodes have 0 at *_rlp2, have 128 at *_advices[0] and 0 everywhere else:
        // [0, 0, 128, 0, ..., 0]
        // While non-empty nodes have 160 at *_rlp2 and then any byte at *_advices:
        // [0, 160, a0, ..., a31]
        meta.create_gate("empty and non-empty", |meta| {
            let q_enable = meta.query_fixed(q_enable, Rotation::cur());
            let mut constraints = vec![];

            let is_branch_child_cur = meta.query_advice(branch.is_child, Rotation::cur());
            let rlp2 = meta.query_advice(main.rlp2, Rotation::cur());

            // Note that s_rlp1 and c_rlp1 store RLP stream length data (subtracted
            // by the number of bytes in branch rows until that position).

            let c128 = Expression::Constant(F::from(128_u64));
            let c160 = Expression::Constant(F::from(160_u64));

            let is_node_hashed = meta.query_advice(is_node_hashed, Rotation::cur());

            // In empty nodes: rlp2 = 0. In non-empty nodes: rlp2 = 160.
            constraints.push((
                "*_rlp2 = 0 or *_rlp2 = 160",
                q_enable.clone()
                    * is_branch_child_cur.clone()
                    * (one.clone() - is_node_hashed.clone())
                    * rlp2.clone()
                    * (rlp2.clone() - c160.clone()),
            ));

            // No further constraints needed for non-empty nodes (rlp2 needs to be 160
            // and values need to be bytes which is constrained by the lookups
            // on s_advices and c_advices).

            let advice0 = meta.query_advice(main.bytes[0], Rotation::cur());
            constraints.push((
                "*_advices[0] = 128 in empty",
                q_enable.clone()
                    * is_branch_child_cur.clone()
                    * (one.clone() - is_node_hashed.clone())
                    * (rlp2.clone() - c160.clone())
                    * (advice0 - c128.clone()), /* If *_rlp2 = 0, then s_advices[0] can be any
                                                 * value (0-255). */
            ));

            for col in main.bytes.iter().skip(1) {
                let s = meta.query_advice(*col, Rotation::cur());
                constraints.push((
                    "*_advices[i] = 0 for i > 0 in empty",
                    q_enable.clone()
                        * is_branch_child_cur.clone()
                        * (one.clone() - is_node_hashed.clone())
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
            let is_branch_child_cur = meta.query_advice(branch.is_child, Rotation::cur());

            let node_index_cur = meta.query_advice(branch.node_index, Rotation::cur());

            // mod_node_hash_rlc is the same for all is_branch_child rows.
            // This is to enable easier comparison when in leaf row
            // where we need to compare the keccak output is the same as keccak of the
            // modified node, this way we just rotate back to one of the branch
            // children rows and we get mod_node_hash_rlc there (otherwise we
            // would need iterate over all branch children rows (many rotations) and check
            // that at is_modified the value corresponds).

            let mut mod_node_hash_rlc = accs.s_mod_node_rlc;
            if !is_s {
                mod_node_hash_rlc = accs.c_mod_node_rlc;
            }

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
            let is_modified = meta.query_advice(branch.is_modified, Rotation::cur());

            // sel - denoting whether leaf is empty at modified_node.
            // When sel = 1, *_advices need to be [128, 0, ..., 0].
            // If sel = 1, there is no leaf at this position (value is being added or
            // deleted) and we don't check the hash of it in leaf_value.

            let c128 = Expression::Constant(F::from(128));
            let sel_prev = meta.query_advice(sel, Rotation::prev());
            let sel_cur = meta.query_advice(sel, Rotation::cur());

            // advices[0] = 128
            let advices0 = meta.query_advice(main.bytes[0], Rotation::cur());
            constraints.push((
                "branch child sel *_advices0",
                q_not_first.clone()
                    * is_branch_child_cur.clone()
                    * is_modified.clone()
                    * (advices0 - c128.clone())
                    * sel_cur.clone(),
            ));
            // advices[i] = 0 for i > 0
            for column in main.bytes.iter().skip(1) {
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
        
        let sel = |meta: &mut VirtualCells<F>| {
            let q_enable = meta.query_fixed(q_enable, Rotation::cur());
            let is_branch_child_cur = meta.query_advice(branch.is_child, Rotation::cur());
            let is_node_hashed = meta.query_advice(is_node_hashed, Rotation::cur());
            
            q_enable * is_branch_child_cur * is_node_hashed
        };

        /*
        There are 0s after the last non-hashed node byte.
        for ind in 1..HASH_WIDTH {
            key_len_lookup(
                meta,
                sel,
                ind,
                main.bytes[0],
                main.bytes[ind],
                192,
                fixed_table,
            )
        }
        */

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
