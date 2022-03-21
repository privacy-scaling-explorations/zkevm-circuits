use halo2_proofs::{
    circuit::Chip,
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed},
    poly::Rotation,
};
use pairing::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::param::{
    HASH_WIDTH, IS_EXT_LONG_EVEN_C16_POS, IS_EXT_LONG_EVEN_C1_POS, IS_EXT_LONG_ODD_C16_POS,
    IS_EXT_LONG_ODD_C1_POS, IS_EXT_SHORT_C16_POS, IS_EXT_SHORT_C1_POS, LAYOUT_OFFSET,
};

#[derive(Clone, Debug)]
pub(crate) struct BranchKeyConfig {}

// Checks whether the key is being properly build using modified_node -
// modified_node presents a nibble in a key. Storage key is composed of
// (modified_node_prev * 16 + modified_node) bytes and key bytes in a leaf.
pub(crate) struct BranchKeyChip<F> {
    config: BranchKeyConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> BranchKeyChip<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_not_first: Column<Fixed>,
        not_first_level: Column<Fixed>, /* to avoid rotating back when in the first branch (for
                                         * key rlc) */
        is_branch_init: Column<Advice>,
        is_account_leaf_storage_codehash_c: Column<Advice>,
        s_advices: [Column<Advice>; HASH_WIDTH],
        modified_node: Column<Advice>, // index of the modified node
        c16_col: Column<Advice>,
        c1_col: Column<Advice>,
        key_rlc: Column<Advice>, // used first for account address, then for storage key
        key_rlc_mult: Column<Advice>,
        acc_r: F,
    ) -> BranchKeyConfig {
        let config = BranchKeyConfig {};
        let one = Expression::Constant(F::one());

        meta.create_gate("branch key", |meta| {
            // For the first branch node (node_index = 0), the key rlc needs to be:
            // key_rlc = key_rlc::Rotation(-19) + modified_node * key_rlc_mult
            // Note: we check this in the first branch node (after branch init),
            // Rotation(-19) lands into the previous first branch node, that's because
            // branch has 1 (init) + 16 (children) + 2 (extension nodes for S and C) rows

            // We need to check whether we are in the first storage level, we can do this
            // by checking whether is_account_leaf_storage_codehash_c is true in the
            // previous row.

            let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
            let not_first_level = meta.query_fixed(not_first_level, Rotation::cur());

            let mut constraints = vec![];

            let is_branch_init_prev = meta.query_advice(is_branch_init, Rotation::prev());
            let modified_node_cur = meta.query_advice(modified_node, Rotation::cur());

            let is_ext_short_c16 = meta.query_advice(
                s_advices[IS_EXT_SHORT_C16_POS - LAYOUT_OFFSET],
                Rotation(-1),
            );
            let is_ext_short_c1 =
                meta.query_advice(s_advices[IS_EXT_SHORT_C1_POS - LAYOUT_OFFSET], Rotation(-1));
            let is_ext_long_even_c16 = meta.query_advice(
                s_advices[IS_EXT_LONG_EVEN_C16_POS - LAYOUT_OFFSET],
                Rotation(-1),
            );
            let is_ext_long_even_c1 = meta.query_advice(
                s_advices[IS_EXT_LONG_EVEN_C1_POS - LAYOUT_OFFSET],
                Rotation(-1),
            );
            let is_ext_long_odd_c16 = meta.query_advice(
                s_advices[IS_EXT_LONG_ODD_C16_POS - LAYOUT_OFFSET],
                Rotation(-1),
            );
            let is_ext_long_odd_c1 = meta.query_advice(
                s_advices[IS_EXT_LONG_ODD_C1_POS - LAYOUT_OFFSET],
                Rotation(-1),
            );

            let is_extension_key_even = is_ext_long_even_c16.clone() + is_ext_long_even_c1.clone();
            let is_extension_key_odd = is_ext_long_odd_c16.clone()
                + is_ext_long_odd_c1.clone()
                + is_ext_short_c16.clone()
                + is_ext_short_c1.clone();

            let is_extension_node = is_extension_key_even.clone() + is_extension_key_odd.clone();

            // -2 because we are in the first branch child and -1 is branch init row, -2 is
            // account leaf storage codehash when we are in the first storage proof level
            let is_account_leaf_storage_codehash_prev =
                meta.query_advice(is_account_leaf_storage_codehash_c, Rotation(-2));

            let c16 = Expression::Constant(F::from(16));
            // If sel1 = 1, then modified_node is multiplied by 16.
            // If sel2 = 1, then modified_node is multiplied by 1.
            // NOTE: modified_node presents nibbles: n0, n1, ...
            // key_rlc = (n0 * 16 + n1) + (n2 * 16 + n3) * r + (n4 * 16 + n5) * r^2 + ...
            let sel1_prev = meta.query_advice(c16_col, Rotation(-20));
            // Rotation(-20) lands into previous branch init.
            let sel1_cur = meta.query_advice(c16_col, Rotation::prev());
            let sel2_cur = meta.query_advice(c1_col, Rotation::prev());

            let key_rlc_prev = meta.query_advice(key_rlc, Rotation(-19));
            let key_rlc_cur = meta.query_advice(key_rlc, Rotation::cur());
            let key_rlc_mult_prev = meta.query_advice(key_rlc_mult, Rotation(-19));
            let key_rlc_mult_cur = meta.query_advice(key_rlc_mult, Rotation::cur());
            constraints.push((
                "key_rlc sel1",
                not_first_level.clone()
                    * is_branch_init_prev.clone()
                    * (one.clone() - is_account_leaf_storage_codehash_prev.clone()) // When this is 0, we check as for the first level key rlc.
                    * (one.clone() - is_extension_node.clone())
                    * sel1_cur.clone()
                    * (key_rlc_cur.clone()
                        - key_rlc_prev.clone()
                        - modified_node_cur.clone() * c16.clone()
                            * key_rlc_mult_prev.clone()),
            ));
            constraints.push((
                "key_rlc sel2",
                not_first_level.clone()
                    * is_branch_init_prev.clone()
                    * (one.clone() - is_account_leaf_storage_codehash_prev.clone()) // When this is 0, we check as for the first level key rlc.
                    * (one.clone() - is_extension_node.clone())
                    * sel2_cur.clone()
                    * (key_rlc_cur.clone()
                        - key_rlc_prev
                        - modified_node_cur.clone()
                            * key_rlc_mult_prev.clone()),
            ));

            constraints.push((
                "key_rlc_mult sel1",
                not_first_level.clone()
                    * is_branch_init_prev.clone()
                    * (one.clone() - is_account_leaf_storage_codehash_prev.clone()) // When this is 0, we check as for the first level key rlc.
                    * (one.clone() - is_extension_node.clone())
                    * sel1_cur.clone()
                    * (key_rlc_mult_cur.clone() - key_rlc_mult_prev.clone()),
            ));
            constraints.push((
                "key_rlc_mult sel2",
                not_first_level.clone()
                    * is_branch_init_prev.clone()
                    * (one.clone() - is_account_leaf_storage_codehash_prev.clone()) // When this is 0, we check as for the first level key rlc.
                    * (one.clone() - is_extension_node.clone())
                    * sel2_cur.clone()
                    * (key_rlc_mult_cur.clone() - key_rlc_mult_prev * acc_r),
            ));

            // Key (which actually means account address) in first level in account proof.
            constraints.push((
                "account first level key_rlc",
                q_not_first.clone()
                    * (one.clone() - not_first_level.clone())
                    * (one.clone() - is_extension_node.clone())
                    * is_branch_init_prev.clone()
                    * (key_rlc_cur.clone() - modified_node_cur.clone() * c16.clone()),
            ));
            constraints.push((
                "account first level key_rlc_mult",
                q_not_first.clone()
                    * (one.clone() - not_first_level.clone())
                    * (one.clone() - is_extension_node.clone())
                    * is_branch_init_prev.clone()
                    * (key_rlc_mult_cur.clone() - one.clone()),
            ));

            // First storage level.
            constraints.push((
                "storage first level key_rlc",
                q_not_first.clone()
                    * is_account_leaf_storage_codehash_prev.clone()
                    * (one.clone() - is_extension_node.clone())
                    * is_branch_init_prev.clone()
                    * (key_rlc_cur - modified_node_cur * c16),
            ));
            constraints.push((
                "storage first level key_rlc_mult",
                q_not_first.clone()
                    * is_account_leaf_storage_codehash_prev.clone()
                    * (one.clone() - is_extension_node.clone())
                    * is_branch_init_prev.clone()
                    * (key_rlc_mult_cur - one.clone()),
            ));

            // Selector constraints (sel1, sel2)

            constraints.push((
                "sel1 is bool",
                q_not_first.clone()
                    * is_branch_init_prev.clone()
                    * sel1_cur.clone()
                    * (sel1_cur.clone() - one.clone()),
            ));
            constraints.push((
                "sel2 is bool",
                q_not_first.clone()
                    * is_branch_init_prev.clone()
                    * sel2_cur.clone()
                    * (sel2_cur.clone() - one.clone()),
            ));
            constraints.push((
                "sel1 + sel2 = 1",
                q_not_first.clone()
                    * is_branch_init_prev.clone()
                    * (sel1_cur.clone() + sel2_cur.clone() - one.clone()),
            ));

            // Key RLC for extension node is checked in extension_node,
            // however, sel1 & sel2 are checked here (to avoid additional rotations).

            // First sel1 in account proof (implicitly constrains sel2 because of the
            // bool & sum constraints above).
            constraints.push((
                "account first level key_rlc sel1",
                q_not_first.clone()
                    * (one.clone() - not_first_level.clone())
                    * (one.clone() - is_extension_node.clone())
                    * is_branch_init_prev.clone()
                    * (sel1_cur.clone() - one.clone()),
            ));
            // If extension node, sel1 and sel2 in first level depend on the extension key
            // (even/odd). If key is even, the constraints stay the same. If key
            // is odd, the constraints get turned around. Note that even/odd
            // means for key nibbles (what we actually need here) and
            // not for key length in RLP (how many bytes key occupies in RLP).
            constraints.push((
                "account first level key_rlc sel1 = 1 (extension node even key)",
                q_not_first.clone()
                    * (one.clone() - not_first_level.clone())
                    * is_branch_init_prev.clone()
                    * is_extension_key_even.clone()
                    * (sel1_cur.clone() - one.clone()),
            ));
            constraints.push((
                "account first level key_rlc sel1 = 0 (extension node odd key)",
                q_not_first.clone()
                    * (one.clone() - not_first_level.clone())
                    * is_branch_init_prev.clone()
                    * is_extension_key_odd.clone()
                    * sel1_cur.clone(),
            ));

            // First sel1 in storage proof (sel2 implicitly)
            constraints.push((
                "storage first level key_rlc sel1 = 1",
                q_not_first.clone()
                    * is_account_leaf_storage_codehash_prev.clone()
                    * (one.clone() - is_extension_node.clone())
                    * is_branch_init_prev.clone()
                    * (sel1_cur.clone() - one.clone()),
            ));
            constraints.push((
                "storage first level key_rlc sel1 = 1 (extension node even key)",
                q_not_first.clone()
                    * is_account_leaf_storage_codehash_prev.clone()
                    * is_branch_init_prev.clone()
                    * is_extension_key_even.clone()
                    * (sel1_cur.clone() - one.clone()),
            ));
            constraints.push((
                "storage first level key_rlc sel1 = 0 (extension node odd key)",
                q_not_first.clone()
                    * is_account_leaf_storage_codehash_prev.clone()
                    * is_branch_init_prev.clone()
                    * is_extension_key_odd.clone()
                    * sel1_cur.clone(),
            ));

            // sel1 alernates between 0 and 1 (sel2 alternates implicitly)
            constraints.push((
                "sel1 0->1->0->...",
                not_first_level.clone()
                    * is_branch_init_prev.clone()
                    * (one.clone() - is_account_leaf_storage_codehash_prev.clone()) // When this is 0, we check as for the first level key rlc.
                    * (one.clone() - is_extension_node.clone())
                    * (sel1_cur.clone() + sel1_prev.clone() - one.clone()),
            ));
            constraints.push((
                "sel1 0->1->0->... (extension node even key)",
                not_first_level.clone()
                    * is_branch_init_prev.clone()
                    * (one.clone() - is_account_leaf_storage_codehash_prev.clone()) // When this is 0, we check as for the first level key rlc.
                    * is_extension_key_even.clone()
                    * (sel1_cur.clone() + sel1_prev.clone() - one.clone()),
            ));
            constraints.push((
                "extension node odd key stays the same",
                not_first_level.clone()
                    * is_branch_init_prev.clone()
                    * (one.clone() - is_account_leaf_storage_codehash_prev.clone()) // When this is 0, we check as for the first level key rlc.
                    * is_extension_key_odd.clone()
                    * (sel1_cur.clone() - sel1_prev.clone()),
            ));

            constraints
        });

        config
    }

    pub fn construct(config: BranchKeyConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }
}

impl<F: FieldExt> Chip<F> for BranchKeyChip<F> {
    type Config = BranchKeyConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}
