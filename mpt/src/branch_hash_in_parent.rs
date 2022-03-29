use halo2_proofs::{
    circuit::Chip,
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, Instance},
    poly::Rotation,
};
use pairing::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::{
    helpers::get_is_extension_node,
    param::{HASH_WIDTH, KECCAK_INPUT_WIDTH, KECCAK_OUTPUT_WIDTH},
};

#[derive(Clone, Debug)]
pub(crate) struct BranchHashInParentConfig {}

pub(crate) struct BranchHashInParentChip<F> {
    config: BranchHashInParentConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> BranchHashInParentChip<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        inter_root: Column<Advice>,
        not_first_level: Column<Advice>,
        q_not_first: Column<Fixed>,
        is_account_leaf_storage_codehash_c: Column<Advice>,
        is_last_branch_child: Column<Advice>,
        is_branch_placeholder: Column<Advice>,
        s_advices: [Column<Advice>; HASH_WIDTH],
        mod_node_hash_rlc: Column<Advice>,
        acc: Column<Advice>,
        acc_mult: Column<Advice>,
        keccak_table: [Column<Fixed>; KECCAK_INPUT_WIDTH + KECCAK_OUTPUT_WIDTH],
    ) -> BranchHashInParentConfig {
        let config = BranchHashInParentConfig {};
        let one = Expression::Constant(F::from(1_u64));

        meta.lookup_any(
            "account first level branch hash - compared to root",
            |meta| {
                let mut constraints = vec![];
                let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
                let not_first_level = meta.query_advice(not_first_level, Rotation::cur());

                let is_last_branch_child = meta.query_advice(is_last_branch_child, Rotation::cur());

                // TODO: acc currently doesn't have branch ValueNode info (which 128 if nil)
                let acc = meta.query_advice(acc, Rotation::cur());
                let c128 = Expression::Constant(F::from(128));
                let mult = meta.query_advice(acc_mult, Rotation::cur());
                let branch_acc = acc + c128 * mult;

                let root = meta.query_advice(inter_root, Rotation::cur());

                constraints.push((
                    q_not_first.clone()
                        * is_last_branch_child.clone()
                        * (one.clone() - not_first_level.clone())
                        * branch_acc, // TODO: replace with acc once ValueNode is added
                    meta.query_fixed(keccak_table[0], Rotation::cur()),
                ));
                let keccak_table_i = meta.query_fixed(keccak_table[1], Rotation::cur());
                constraints.push((
                    q_not_first * is_last_branch_child * (one.clone() - not_first_level) * root,
                    keccak_table_i,
                ));

                constraints
            },
        );

        // Check whether hash of a branch is in parent branch.
        // Check if (accumulated_s(c)_rlc, hash1, hash2, hash3, hash4) is in keccak
        // table, where hash1, hash2, hash3, hash4 are stored in the previous
        // branch and accumulated_s(c)_rlc presents the branch RLC.
        meta.lookup_any("branch_hash_in_parent", |meta| {
            let not_first_level = meta.query_advice(not_first_level, Rotation::cur());

            // -17 because we are in the last branch child (-16 takes us to branch init)
            let is_account_leaf_storage_codehash_prev =
                meta.query_advice(is_account_leaf_storage_codehash_c, Rotation(-17));

            // We need to do the lookup only if we are in the last branch child.
            let is_last_branch_child = meta.query_advice(is_last_branch_child, Rotation::cur());

            // When placeholder branch, we don't check its hash in a parent.
            let is_branch_placeholder = meta.query_advice(is_branch_placeholder, Rotation(-16));

            let is_extension_node = get_is_extension_node(meta, s_advices, -16);

            // TODO: acc currently doesn't have branch ValueNode info (which 128 if nil)
            let acc = meta.query_advice(acc, Rotation::cur());
            let c128 = Expression::Constant(F::from(128));
            let mult = meta.query_advice(acc_mult, Rotation::cur());
            let branch_acc = acc + c128 * mult;

            let mut constraints = vec![];
            constraints.push((
                not_first_level.clone()
                    * is_last_branch_child.clone()
                    * (one.clone() - is_account_leaf_storage_codehash_prev.clone()) // we don't check this in the first storage level
                    * (one.clone() - is_branch_placeholder.clone())
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
                            - is_account_leaf_storage_codehash_prev.clone()) // we don't check this in the first storage level
                        * (one.clone() - is_branch_placeholder.clone())
                        * (one.clone() - is_extension_node.clone())
                        * mod_node_hash_rlc_cur,
                keccak_table_i,
            ));

            constraints
        });

        config
    }

    pub fn construct(config: BranchHashInParentConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }
}

impl<F: FieldExt> Chip<F> for BranchHashInParentChip<F> {
    type Config = BranchHashInParentConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}
