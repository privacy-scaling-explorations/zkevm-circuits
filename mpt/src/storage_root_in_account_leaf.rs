use halo2_proofs::{
    circuit::Chip,
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed},
    poly::Rotation,
};
use pairing::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::{
    helpers::{get_is_extension_node, bytes_expr_into_rlc, into_words_expr},
    param::{
        HASH_WIDTH, IS_BRANCH_C_PLACEHOLDER_POS, IS_BRANCH_S_PLACEHOLDER_POS, KECCAK_INPUT_WIDTH,
        KECCAK_OUTPUT_WIDTH, LAYOUT_OFFSET,
    },
};

#[derive(Clone, Debug)]
pub(crate) struct StorageRootConfig {}

pub(crate) struct StorageRootChip<F> {
    config: StorageRootConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> StorageRootChip<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        not_first_level: Column<Advice>,
        is_leaf_s_value: Column<Advice>,
        is_leaf_c_value: Column<Advice>,
        is_account_leaf_in_added_branch: Column<Advice>,
        is_last_branch_child: Column<Advice>,
        s_advices: [Column<Advice>; HASH_WIDTH],
        acc_s: Column<Advice>,
        acc_mult_s: Column<Advice>,
        acc_c: Column<Advice>,
        acc_mult_c: Column<Advice>,
        sel: Column<Advice>,
        keccak_table: [Column<Fixed>; KECCAK_INPUT_WIDTH + KECCAK_OUTPUT_WIDTH],
        acc_r: F,
        is_s: bool,
    ) -> StorageRootConfig {
        let config = StorageRootConfig {};
        let one = Expression::Constant(F::one());

        // Storage first level branch hash - root in last account leaf (ordinary branch,
        // not extension node).
        meta.lookup_any(
            "storage_root_in_account_leaf 1: root of the first level branch in account leaf",
            |meta| {
                // Note: we are in the same row (last branch child) for S and C.
                let not_first_level = meta.query_advice(not_first_level, Rotation::cur());
                let mut rot_into_branch_init = -16;

                let is_account_leaf_in_added_branch = meta.query_advice(
                    is_account_leaf_in_added_branch,
                    Rotation(rot_into_branch_init - 1),
                );

                let is_extension_node =
                    get_is_extension_node(meta, s_advices, rot_into_branch_init);

                // We need to do the lookup only if we are in the last branch child.
                let is_last_branch_child = meta.query_advice(is_last_branch_child, Rotation::cur());

                let mut acc = meta.query_advice(acc_s, Rotation::cur());
                if !is_s {
                    acc = meta.query_advice(acc_c, Rotation::cur());
                }

                // TODO: acc currently doesn't have branch ValueNode info (which 128 if nil)
                let c128 = Expression::Constant(F::from(128));
                let mut mult = meta.query_advice(acc_mult_s, Rotation::cur());
                if !is_s {
                    mult = meta.query_advice(acc_mult_c, Rotation::cur());
                }
                let branch_acc = acc + c128 * mult;

                let mut sc_hash = vec![];
                // Note: storage root is always in s_advices!
                for column in s_advices.iter() {
                    if is_s {
                        sc_hash
                            .push(meta.query_advice(*column, Rotation(rot_into_branch_init - 3)));
                    } else {
                        sc_hash
                            .push(meta.query_advice(*column, Rotation(rot_into_branch_init - 2)));
                    }
                }
                let hash_rlc = bytes_expr_into_rlc(&sc_hash, acc_r);
                let mut constraints = vec![];
                constraints.push((
                    not_first_level.clone()
                        * (one.clone() - is_extension_node.clone())
                        * is_last_branch_child.clone()
                        * is_account_leaf_in_added_branch.clone()
                        * branch_acc, // TODO: replace with acc once ValueNode is added
                    meta.query_fixed(keccak_table[0], Rotation::cur()),
                ));
                constraints.push((
                    not_first_level.clone()
                        * (one.clone() - is_extension_node.clone())
                        * is_last_branch_child.clone()
                        * is_account_leaf_in_added_branch.clone()
                        * hash_rlc,
                    meta.query_fixed(keccak_table[1], Rotation::cur()),
                ));

                constraints
            },
        );

        // Storage first level extension hash - root in last account leaf (extension
        // node).
        meta.lookup_any(
            "storage_root_in_account_leaf 2: root of the first level extension node in account leaf",
            |meta| {
                let not_first_level = meta.query_advice(not_first_level, Rotation::cur());

                let mut rot_into_branch_init = -17;
                let mut rot_into_last_branch_child = -1;
                if !is_s {
                    rot_into_branch_init = -18;
                    rot_into_last_branch_child = -2;
                }

                let mut is_branch_placeholder = meta.query_advice(
                    s_advices[IS_BRANCH_S_PLACEHOLDER_POS - LAYOUT_OFFSET],
                    Rotation(rot_into_branch_init),
                );
                if !is_s {
                    is_branch_placeholder = meta.query_advice(
                        s_advices[IS_BRANCH_C_PLACEHOLDER_POS - LAYOUT_OFFSET],
                        Rotation(rot_into_branch_init),
                    );
                }

                let is_account_leaf_in_added_branch = meta.query_advice(
                    is_account_leaf_in_added_branch,
                    Rotation(rot_into_branch_init - 1),
                );

                let is_extension_node =
                    get_is_extension_node(meta, s_advices, rot_into_branch_init);

                // We need to do the lookup only if we are in the last branch child.
                let is_after_last_branch_child =
                    meta.query_advice(is_last_branch_child, Rotation(rot_into_last_branch_child));

                // Note: acc_c in both cases.
                let acc = meta.query_advice(acc_c, Rotation::cur());

                let mut sc_hash = vec![];
                // Note: storage root is always in s_advices!
                for column in s_advices.iter() {
                    if is_s {
                        sc_hash
                            .push(meta.query_advice(*column, Rotation(rot_into_branch_init - 3)));
                    } else {
                        sc_hash
                            .push(meta.query_advice(*column, Rotation(rot_into_branch_init - 2)));
                    }
                }
                let hash_rlc = bytes_expr_into_rlc(&sc_hash, acc_r);

                let mut constraints = vec![];
                constraints.push((
                    not_first_level.clone()
                        * is_extension_node.clone()
                        * is_after_last_branch_child.clone()
                        * is_account_leaf_in_added_branch.clone()
                        * (one.clone() - is_branch_placeholder.clone())
                        * acc,
                    meta.query_fixed(keccak_table[0], Rotation::cur()),
                ));
                constraints.push((
                    not_first_level.clone()
                        * is_extension_node.clone()
                        * is_after_last_branch_child.clone()
                        * is_account_leaf_in_added_branch.clone()
                        * (one.clone() - is_branch_placeholder.clone())
                        * hash_rlc.clone(),
                    meta.query_fixed(keccak_table[1], Rotation::cur()),
                ));

                constraints
            },
        );

        // If there is no branch, just a leaf.
        meta.lookup_any(
            "storage_root_in_account_leaf 3: root of the first level storage leaf in account leaf",
            |meta| {
                let not_first_level = meta.query_advice(not_first_level, Rotation::cur());

                // Check in leaf value row.
                let mut rot_into_last_account_row = -2;
                let mut is_leaf = meta.query_advice(is_leaf_s_value, Rotation::cur());
                if !is_s {
                    rot_into_last_account_row = -4;
                    is_leaf = meta.query_advice(is_leaf_c_value, Rotation::cur());
                }
                let is_placeholder = meta.query_advice(sel, Rotation::cur());

                let is_account_leaf_in_added_branch = meta.query_advice(
                    is_account_leaf_in_added_branch,
                    Rotation(rot_into_last_account_row),
                );

                let acc = meta.query_advice(acc_s, Rotation::cur());

                let mut sc_hash = vec![];
                // Note: storage root is always in s_advices!
                for column in s_advices.iter() {
                    if is_s {
                        sc_hash.push(
                            meta.query_advice(*column, Rotation(rot_into_last_account_row - 2)),
                        );
                    } else {
                        sc_hash.push(
                            meta.query_advice(*column, Rotation(rot_into_last_account_row - 1)),
                        );
                    }
                }
                let hash_rlc = bytes_expr_into_rlc(&sc_hash, acc_r);

                let mut constraints = vec![];
                constraints.push((
                    not_first_level.clone()
                        * is_leaf.clone()
                        * (one.clone() - is_placeholder.clone())
                        * is_account_leaf_in_added_branch.clone()
                        * acc,
                    meta.query_fixed(keccak_table[0], Rotation::cur()),
                ));
                constraints.push((
                    not_first_level.clone()
                        * is_leaf.clone()
                        * (one.clone() - is_placeholder)
                        * is_account_leaf_in_added_branch.clone()
                        * hash_rlc.clone(),
                    meta.query_fixed(keccak_table[1], Rotation::cur()),
                ));

                constraints
            },
        );

        // If there is no branch, just a leaf, but after a placeholder.
        meta.lookup_any("storage_root_in_account_leaf 4: root of the first level storage leaf (after placeholder) in account leaf", |meta| {
            let not_first_level = meta.query_advice(not_first_level, Rotation::cur());

            // Check in leaf value row.
            let mut rot = -2 - 19;
            let mut is_leaf = meta.query_advice(is_leaf_s_value, Rotation::cur());
            if !is_s {
                rot = -4 - 19;
                is_leaf = meta.query_advice(is_leaf_c_value, Rotation::cur());
            }

            let mut is_branch_placeholder = meta.query_advice(
                s_advices[IS_BRANCH_S_PLACEHOLDER_POS - LAYOUT_OFFSET],
                Rotation(rot + 1),
            );
            if !is_s {
                is_branch_placeholder = meta.query_advice(
                    s_advices[IS_BRANCH_C_PLACEHOLDER_POS - LAYOUT_OFFSET],
                    Rotation(rot + 1),
                );
            }

            let is_account_leaf_in_added_branch =
                meta.query_advice(is_account_leaf_in_added_branch, Rotation(rot));

            let acc = meta.query_advice(acc_s, Rotation::cur());

            let mut sc_hash = vec![];
            // Note: storage root is always in s_advices!
            for column in s_advices.iter() {
                if is_s {
                    sc_hash.push(meta.query_advice(*column, Rotation(rot - 2)));
                } else {
                    sc_hash.push(meta.query_advice(*column, Rotation(rot - 1)));
                }
            }
            let hash_rlc = bytes_expr_into_rlc(&sc_hash, acc_r);

            let mut constraints = vec![];
            constraints.push((
                not_first_level.clone()
                    * is_leaf.clone()
                    * is_account_leaf_in_added_branch.clone()
                    * is_branch_placeholder.clone()
                    * acc,
                meta.query_fixed(keccak_table[0], Rotation::cur()),
            ));
            constraints.push((
                not_first_level.clone()
                    * is_leaf.clone()
                    * is_account_leaf_in_added_branch.clone()
                    * is_branch_placeholder.clone()
                    * hash_rlc.clone(),
                meta.query_fixed(keccak_table[1], Rotation::cur()),
            ));

            constraints
        });

        config
    }

    pub fn construct(config: StorageRootConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }
}

impl<F: FieldExt> Chip<F> for StorageRootChip<F> {
    type Config = StorageRootConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}
