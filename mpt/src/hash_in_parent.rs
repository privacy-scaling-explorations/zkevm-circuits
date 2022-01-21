use halo2::{
    circuit::Chip,
    plonk::{
        Advice, Column, ConstraintSystem, Expression, Fixed, VirtualCells,
    },
    poly::Rotation,
};
use pairing::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::param::{
    HASH_WIDTH, IS_BRANCH_C_PLACEHOLDER_POS, IS_BRANCH_S_PLACEHOLDER_POS,
    KECCAK_INPUT_WIDTH, KECCAK_OUTPUT_WIDTH, LAYOUT_OFFSET,
};

#[derive(Clone, Debug)]
pub(crate) struct HashInParentConfig {}

pub(crate) struct HashInParentChip<F> {
    config: HashInParentConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> HashInParentChip<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        not_first_level: Column<Fixed>,
        is_account_leaf_storage_codehash_c: Column<Advice>,
        is_last_branch_child: Column<Advice>,
        s_keccak: [Column<Advice>; KECCAK_OUTPUT_WIDTH],
        c_keccak: [Column<Advice>; KECCAK_OUTPUT_WIDTH],
        s_advices: [Column<Advice>; HASH_WIDTH],
        acc_s: Column<Advice>,
        acc_mult_s: Column<Advice>,
        acc_c: Column<Advice>,
        acc_mult_c: Column<Advice>,
        keccak_table: [Column<Fixed>; KECCAK_INPUT_WIDTH + KECCAK_OUTPUT_WIDTH],
    ) -> HashInParentConfig {
        let config = HashInParentConfig {};
        let one = Expression::Constant(F::from(1_u64));

        // Check whether hash of a branch S is in parent branch S.
        // Check if (accumulated_s_rlc, hash1, hash2, hash3, hash4) is in keccak table,
        // where hash1, hash2, hash3, hash4 are stored in the previous branch and
        // accumulated_s_rlc presents the branch RLC.
        meta.lookup_any(|meta| {
            let not_first_level =
                meta.query_fixed(not_first_level, Rotation::cur());

            // -17 because we are in the last branch child (-16 takes us to branch init)
            let is_account_leaf_storage_codehash_prev = meta.query_advice(
                is_account_leaf_storage_codehash_c,
                Rotation(-17),
            );

            // We need to do the lookup only if we are in the last branch child.
            let is_last_branch_child =
                meta.query_advice(is_last_branch_child, Rotation::cur());

            // When placeholder branch, we don't check its hash in a parent.
            let is_branch_s_placeholder = meta.query_advice(
                s_advices[IS_BRANCH_S_PLACEHOLDER_POS - LAYOUT_OFFSET],
                Rotation(-16),
            );

            let acc_s = meta.query_advice(acc_s, Rotation::cur());

            // TODO: acc_s currently doesn't have branch ValueNode info (which 128 if nil)
            let c128 = Expression::Constant(F::from(128));
            let mult_s = meta.query_advice(acc_mult_s, Rotation::cur());
            let branch_acc_s1 = acc_s + c128 * mult_s;

            let mut constraints = vec![];
            constraints.push((
                not_first_level.clone()
                    * is_last_branch_child.clone()
                    * (one.clone() - is_account_leaf_storage_codehash_prev.clone()) // we don't check this in the first storage level
                    * (one.clone() - is_branch_s_placeholder.clone())
                    * branch_acc_s1, // TODO: replace with acc_s once ValueNode is added
                meta.query_fixed(keccak_table[0], Rotation::cur()),
            ));
            for (ind, column) in s_keccak.iter().enumerate() {
                // Any rotation that lands into branch can be used instead of -19.
                let s_keccak = meta.query_advice(*column, Rotation(-19));
                let keccak_table_i =
                    meta.query_fixed(keccak_table[ind + 1], Rotation::cur());
                constraints.push((
                    not_first_level.clone()
                        * is_last_branch_child.clone()
                        * (one.clone()
                            - is_account_leaf_storage_codehash_prev.clone()) // we don't check this in the first storage level
                        * (one.clone() - is_branch_s_placeholder.clone())
                        * s_keccak,
                    keccak_table_i,
                ));
            }

            constraints
        });

        // Check whether hash of a branch C is in parent branch C.
        // Check if (accumulated_c_rlc, hash1, hash2, hash3, hash4) is in keccak table,
        // where hash1, hash2, hash3, hash4 are stored in the previous branch and
        // accumulated_c_rlc presents the branch RLC.
        meta.lookup_any(|meta| {
            let not_first_level =
                meta.query_fixed(not_first_level, Rotation::cur());

            // -17 because we are in the last branch child (-16 takes us to branch init)
            let is_account_leaf_storage_codehash_prev = meta.query_advice(
                is_account_leaf_storage_codehash_c,
                Rotation(-17),
            );

            // We need to do the lookup only if we are in the last branch child.
            let is_last_branch_child =
                meta.query_advice(is_last_branch_child, Rotation::cur());

            // When placeholder branch, we don't check its hash in a parent.
            let is_branch_c_placeholder = meta.query_advice(
                s_advices[IS_BRANCH_C_PLACEHOLDER_POS - LAYOUT_OFFSET],
                Rotation(-16),
            );

            let acc_c = meta.query_advice(acc_c, Rotation::cur());

            // TODO: acc_c currently doesn't have branch ValueNode info (which 128 if nil)
            let c128 = Expression::Constant(F::from(128));
            let mult_c = meta.query_advice(acc_mult_c, Rotation::cur());
            let branch_acc_c1 = acc_c + c128 * mult_c;

            let mut constraints = vec![];
            constraints.push((
                not_first_level.clone()
                    * is_last_branch_child.clone()
                    * (one.clone() - is_account_leaf_storage_codehash_prev.clone()) // we don't check this in the first storage level
                    * (one.clone() - is_branch_c_placeholder.clone())
                    * branch_acc_c1, // TODO: replace with acc_c once ValueNode is added
                meta.query_fixed(keccak_table[0], Rotation::cur()),
            ));
            for (ind, column) in c_keccak.iter().enumerate() {
                // Any rotation that lands into branch can be used instead of -19.
                let c_keccak = meta.query_advice(*column, Rotation(-19));
                let keccak_table_i =
                    meta.query_fixed(keccak_table[ind + 1], Rotation::cur());
                constraints.push((
                    not_first_level.clone()
                        * is_last_branch_child.clone()
                        * (one.clone() - is_account_leaf_storage_codehash_prev.clone()) // we don't check this in the first storage level
                        * (one.clone() - is_branch_c_placeholder.clone())
                        * c_keccak,
                    keccak_table_i,
                ));
            }

            constraints
        });

        config
    }

    pub fn construct(config: HashInParentConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }
}

impl<F: FieldExt> Chip<F> for HashInParentChip<F> {
    type Config = HashInParentConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}
