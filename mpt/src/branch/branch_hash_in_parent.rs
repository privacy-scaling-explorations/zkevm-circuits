use halo2_proofs::{
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed},
    poly::Rotation,
};
use pairing::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::{
    helpers::get_is_extension_node,
    param::{KECCAK_INPUT_WIDTH, KECCAK_OUTPUT_WIDTH, IS_BRANCH_S_PLACEHOLDER_POS, RLP_NUM, IS_BRANCH_C_PLACEHOLDER_POS, IS_S_BRANCH_NON_HASHED_POS, IS_C_BRANCH_NON_HASHED_POS}, mpt::{AccumulatorPair}, columns::MainCols,
};

#[derive(Clone, Debug)]
pub(crate) struct BranchHashInParentConfig<F> {
    _marker: PhantomData<F>,
}

impl<F: FieldExt> BranchHashInParentConfig<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        inter_root: Column<Advice>,
        not_first_level: Column<Advice>,
        q_not_first: Column<Fixed>,
        is_account_leaf_in_added_branch: Column<Advice>,
        is_last_branch_child: Column<Advice>,
        s_main: MainCols<F>,
        mod_node_hash_rlc: Column<Advice>,
        acc_pair: AccumulatorPair,
        keccak_table: [Column<Fixed>; KECCAK_INPUT_WIDTH + KECCAK_OUTPUT_WIDTH],
        is_s: bool,
    ) -> Self {
        let config = BranchHashInParentConfig { _marker: PhantomData };
        let one = Expression::Constant(F::from(1_u64));

        // Note: branch in the first level cannot be shorter than 32 bytes (it is always hashed).
        meta.lookup_any(
            "branch in first level - hash compared to root",
            |meta| {
                let mut constraints = vec![];
                let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
                let not_first_level = meta.query_advice(not_first_level, Rotation::cur());

                let is_last_branch_child = meta.query_advice(is_last_branch_child, Rotation::cur());

                let mut is_branch_placeholder = meta.query_advice(
                    s_main.bytes[IS_BRANCH_S_PLACEHOLDER_POS - RLP_NUM],
                    Rotation(-16),
                );
                if !is_s {
                    is_branch_placeholder = meta.query_advice(
                    s_main.bytes[IS_BRANCH_C_PLACEHOLDER_POS - RLP_NUM],
                    Rotation(-16),
                    );
                }

                let is_extension_node = get_is_extension_node(meta, s_main.bytes, -16);

                // TODO: acc currently doesn't have branch ValueNode info (which 128 if nil)
                let acc = meta.query_advice(acc_pair.rlc, Rotation::cur());
                let c128 = Expression::Constant(F::from(128));
                let mult = meta.query_advice(acc_pair.mult, Rotation::cur());
                let branch_acc = acc + c128 * mult;

                let root = meta.query_advice(inter_root, Rotation::cur());

                constraints.push((
                    q_not_first.clone()
                        * is_last_branch_child.clone()
                        * (one.clone() - is_extension_node.clone())
                        * (one.clone() - not_first_level.clone())
                        * (one.clone() - is_branch_placeholder.clone())
                        * branch_acc, // TODO: replace with acc once ValueNode is added
                    meta.query_fixed(keccak_table[0], Rotation::cur()),
                ));
                let keccak_table_i = meta.query_fixed(keccak_table[1], Rotation::cur());
                constraints.push((
                    q_not_first
                        * is_last_branch_child 
                        * (one.clone() - is_extension_node.clone())
                        * (one.clone() - is_branch_placeholder.clone())
                        * (one.clone() - not_first_level)
                        * root,
                    keccak_table_i,
                ));

                constraints
            },
        );

        /*
        Check whether hash of a branch is in parent branch:
        (branch RLC, mod_node_hash_rlc retrieved from the previous branch) needs to be in keccak tabel
        */
        meta.lookup_any("Branch hash in parent", |meta| {
            let not_first_level = meta.query_advice(not_first_level, Rotation::cur());

            // -17 because we are in the last branch child (-16 takes us to branch init)
            let is_account_leaf_in_added_branch_prev =
                meta.query_advice(is_account_leaf_in_added_branch, Rotation(-17));

            // We need to do the lookup only if we are in the last branch child.
            let is_last_branch_child = meta.query_advice(is_last_branch_child, Rotation::cur());

            // When placeholder branch, we don't check its hash in a parent.
            let mut is_branch_placeholder = meta.query_advice(
                s_main.bytes[IS_BRANCH_S_PLACEHOLDER_POS - RLP_NUM],
                Rotation(-16),
            );
            if !is_s {
                is_branch_placeholder = meta.query_advice(
                s_main.bytes[IS_BRANCH_C_PLACEHOLDER_POS - RLP_NUM],
                Rotation(-16),
                );
            }

            let mut is_branch_non_hashed = meta.query_advice(
                s_main.bytes[IS_S_BRANCH_NON_HASHED_POS - RLP_NUM],
                Rotation(-16),
            );
            if !is_s {
                is_branch_non_hashed = meta.query_advice(
                s_main.bytes[IS_C_BRANCH_NON_HASHED_POS - RLP_NUM],
                Rotation(-16),
                );
            }

            let is_extension_node = get_is_extension_node(meta, s_main.bytes, -16);

            // TODO: acc currently doesn't have branch ValueNode info (which 128 if nil)
            let acc = meta.query_advice(acc_pair.rlc, Rotation::cur());
            let c128 = Expression::Constant(F::from(128));
            let mult = meta.query_advice(acc_pair.mult, Rotation::cur());
            let branch_acc = acc + c128 * mult;

            let mut constraints = vec![];
            constraints.push((
                not_first_level.clone()
                    * is_last_branch_child.clone()
                    * (one.clone() - is_account_leaf_in_added_branch_prev.clone()) // we don't check this in the first storage level
                    * (one.clone() - is_branch_placeholder.clone())
                    * (one.clone() - is_branch_non_hashed.clone())
                    * (one.clone() - is_extension_node.clone())
                    * branch_acc, // TODO: replace with acc once ValueNode is added
                meta.query_fixed(keccak_table[0], Rotation::cur()),
            ));
            // Any rotation that lands into branch can be used instead of -19.
            let mod_node_hash_rlc_cur = meta.query_advice(mod_node_hash_rlc, Rotation(-19));
            let keccak_table_i = meta.query_fixed(keccak_table[1], Rotation::cur());
            constraints.push((
                not_first_level.clone()
                        * is_last_branch_child.clone()
                        * (one.clone()
                            - is_account_leaf_in_added_branch_prev.clone()) // we don't check this in the first storage level
                        * (one.clone() - is_branch_placeholder.clone())
                        * (one.clone() - is_branch_non_hashed.clone())
                        * (one.clone() - is_extension_node.clone())
                        * mod_node_hash_rlc_cur,
                keccak_table_i,
            ));

            constraints
        });

        /*
        Similar as the gate above, but here the branch is not hashed. That means its RLC needs to
        be the same as RLC of the node in the parent branch at `modified_node` position.
        */
        meta.create_gate("NON-HASHED branch hash in parent", |meta| {
            let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
            let not_first_level = meta.query_advice(not_first_level, Rotation::cur());

            // -17 because we are in the last branch child (-16 takes us to branch init)
            let is_account_leaf_in_added_branch_prev =
                meta.query_advice(is_account_leaf_in_added_branch, Rotation(-17));

            // We need to do the lookup only if we are in the last branch child.
            let is_last_branch_child = meta.query_advice(is_last_branch_child, Rotation::cur());

            // When placeholder branch, we don't check its hash in a parent.
            let mut is_branch_placeholder = meta.query_advice(
                s_main.bytes[IS_BRANCH_S_PLACEHOLDER_POS - RLP_NUM],
                Rotation(-16),
            );
            if !is_s {
                is_branch_placeholder = meta.query_advice(
                s_main.bytes[IS_BRANCH_C_PLACEHOLDER_POS - RLP_NUM],
                Rotation(-16),
                );
            }

            let mut is_branch_non_hashed = meta.query_advice(
                s_main.bytes[IS_S_BRANCH_NON_HASHED_POS - RLP_NUM],
                Rotation(-16),
            );
            if !is_s {
                is_branch_non_hashed = meta.query_advice(
                s_main.bytes[IS_C_BRANCH_NON_HASHED_POS - RLP_NUM],
                Rotation(-16),
                );
            }

            let is_extension_node = get_is_extension_node(meta, s_main.bytes, -16);

            // TODO: acc currently doesn't have branch ValueNode info (which 128 if nil)
            let acc = meta.query_advice(acc_pair.rlc, Rotation::cur());
            let c128 = Expression::Constant(F::from(128));
            let mult = meta.query_advice(acc_pair.mult, Rotation::cur());
            let branch_acc = acc + c128 * mult;

            let mut constraints = vec![];

            let mod_node_hash_rlc_cur = meta.query_advice(mod_node_hash_rlc, Rotation(-19));
            constraints.push((
                "Non-hashed branch in branch",
                q_not_first
                    * not_first_level.clone()
                    * is_last_branch_child.clone()
                    * (one.clone()
                        - is_account_leaf_in_added_branch_prev.clone()) // we don't check this in the first storage level
                    * (one.clone() - is_branch_placeholder.clone())
                    * is_branch_non_hashed.clone()
                    * (one.clone() - is_extension_node.clone())
                    * (mod_node_hash_rlc_cur - branch_acc),
                ));

            constraints
        });

        config
    }
}
