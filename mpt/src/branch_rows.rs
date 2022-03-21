use halo2_proofs::{
    circuit::Chip,
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed},
    poly::Rotation,
};
use pairing::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::{
    helpers::{hash_expr_into_rlc, into_words_expr},
    param::{HASH_WIDTH, KECCAK_OUTPUT_WIDTH},
};

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
        is_at_first_nibble: Column<Advice>,
        sel: Column<Advice>,
        acc_r: F,
    ) -> BranchRowsConfig {
        let config = BranchRowsConfig {};

        meta.create_gate("Branch rows", |meta| {
            let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());

            let mut constraints = vec![];
            let is_branch_child_cur = meta.query_advice(is_branch_child, Rotation::cur());

            let node_index_cur = meta.query_advice(node_index, Rotation::cur());

            /*
            TODO for leaf:
            Let's say we have a leaf n where
                n.Key = [10,6,3,5,7,0,1,2,12,1,10,3,10,14,0,10,1,7,13,3,0,4,12,9,9,2,0,3,1,0,3,8,2,13,9,6,8,14,11,12,12,4,11,1,7,7,1,15,4,1,12,6,11,3,0,4,2,0,5,11,5,7,0,16]
                n.Val = [2].
            Before put in a proof, a leaf is hashed:
            https://github.com/ethereum/go-ethereum/blob/master/trie/proof.go#L78
            But before being hashed, Key is put in compact form:
            https://github.com/ethereum/go-ethereum/blob/master/trie/hasher.go#L110
            Key becomes:
                [58,99,87,1,44,26,58,224,161,125,48,76,153,32,49,3,130,217,104,235,204,75,23,113,244,28,107,48,66,5,181,112]
            Then the node is RLP encoded:
            https://github.com/ethereum/go-ethereum/blob/master/trie/hasher.go#L157
            RLP:
                [226,160,58,99,87,1,44,26,58,224,161,125,48,76,153,32,49,3,130,217,104,235,204,75,23,113,244,28,107,48,66,5,181,112,2]
            Finally, the RLP is hashed:
                [32,34,39,131,73,65,47,37,211,142,206,231,172,16,11,203,33,107,30,7,213,226,2,174,55,216,4,117,220,10,186,68]

            In a proof (witness), we have [226, 160, ...] in columns s_rlp1, s_rlp2, ...
            */

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
            let is_at_first_nibble = meta.query_advice(is_at_first_nibble, Rotation::cur());

            // When it's NOT placeholder branch, is_modified = is_at_first_nibble.
            // When it's placeholder branch, is_modified != is_at_first_nibble.
            // This is used instead of having is_branch_s_placeholder and
            // is_branch_c_placeholder columns - we only have this info in
            // branch init where we don't need additional columns.

            let mut sc_hash = vec![];
            // Note: storage root is always in s_advices!
            for column in advices.iter() {
                sc_hash.push(meta.query_advice(*column, Rotation::cur()));
            }
            let hash_rlc = hash_expr_into_rlc(&sc_hash, acc_r);

            // In placeholder branch (when is_modified != is_at_first_nibble) the following
            // constraint could be satisfied by attacker by putting hash of is_modified
            // (while it should be is_at_first_nibble), but then the attacker
            // would need to use is_modified node for leaf_key_in_added_branch
            // (hash of it is in keccak at is_at_first_nibble), but then the
            // constraint of leaf_in_added_branch having the same key (TODO this
            // constraint in leaf_key_in_added_branch) except for
            // the first nibble will fail.
            let mod_node_hash_rlc_cur = meta.query_advice(mod_node_hash_rlc, Rotation::cur());
            // Needs to correspond when is_modified or is_at_first_nibble.
            constraints.push((
                "mod_node_hash_rlc correspond to advices at the modified index",
                q_not_first.clone()
                        * is_branch_child_cur.clone()
                        * is_at_first_nibble.clone() // is_at_first_nibble = is_modified when NOT placeholder
                        * is_modified.clone()
                        * (hash_rlc.clone() - mod_node_hash_rlc_cur),
            ));

            // sel1 - denoting whether leaf is empty at modified_node.
            // When sel1 = 1, s_advices need to be [128, 0, ..., 0].
            // If sel1 = 1, there is no leaf at this position (value is being added or
            // deleted) and we don't check the hash of it in leaf_value.

            // sel2 - denoting whether leaf is empty at modified_node.
            // When sel2 = 1, c_advices need to be [128, 0, ..., 0].
            // If sel2 = 1, there is no leaf at this position (value is being added or
            // deleted) and we don't check the hash of it in leaf_value.

            let c128 = Expression::Constant(F::from(128));
            let sel_cur = meta.query_advice(sel, Rotation::cur());

            // advices[0] = 128
            let advices0 = meta.query_advice(advices[0], Rotation::cur());
            constraints.push((
                "branch child sel1 s_advices0",
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
                    "branch child sel1 s_advices",
                    q_not_first.clone()
                        * is_branch_child_cur.clone()
                        * is_modified.clone()
                        * s
                        * sel_cur.clone(),
                ));
            }

            // TODO: constraint for is_modified = is_at_first_nibble, to do this
            // we can check modified_node = first_nibble in branch init and then check
            // in each branch node: modified_node_prev = modified_node_cur and
            // first_nibble_prev = first_nibble_cur, this way we can use only Rotation(-1).

            // TODO: sel1 and sel2 - need to be the same in all branch children

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
