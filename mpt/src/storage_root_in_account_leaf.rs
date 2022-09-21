use halo2_proofs::{
    circuit::Chip,
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed},
    poly::Rotation,
};
use pairing::arithmetic::FieldExt;
use std::marker::PhantomData;

// TODO: split across account_leaf, branch, storage_leaf folders

use crate::{
    helpers::{get_is_extension_node, bytes_expr_into_rlc},
    param::{
        IS_BRANCH_C_PLACEHOLDER_POS, IS_BRANCH_S_PLACEHOLDER_POS, KECCAK_INPUT_WIDTH,
        KECCAK_OUTPUT_WIDTH, RLP_NUM, ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND, ACCOUNT_LEAF_ROWS, ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND, LEAF_VALUE_S_IND, LEAF_VALUE_C_IND, BRANCH_ROWS_NUM,
    }, storage_leaf::StorageLeafCols, columns::{MainCols, AccumulatorCols},
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
        q_enable: Column<Fixed>,
        not_first_level: Column<Advice>,
        is_account_leaf_in_added_branch: Column<Advice>,
        storage_leaf: StorageLeafCols<F>,
        s_main: MainCols<F>,
        accs: AccumulatorCols<F>,
        sel: Column<Advice>,
        keccak_table: [Column<Fixed>; KECCAK_INPUT_WIDTH + KECCAK_OUTPUT_WIDTH],
        acc_r: F,
        is_s: bool,
    ) -> StorageRootConfig {
        let config = StorageRootConfig {};
        let one = Expression::Constant(F::one());  

        
        /*
        If there is no branch, just a leaf, but after a placeholder.
        If there is no branch or extension node in the storage trie (just a leaf)
        and the only leaf in the trie is after branch placeholder, it needs
        to be ensured that the hash of the (only) leaf is the storage root.
        This appears when there is only one leaf in the storage trie and we add another

        Note: Branch in the first level cannot be shorter than 32 bytes (it is always hashed).
        */
        meta.lookup_any(
            "Hash of the only storage leaf which is after a placeholder is storage trie root",
            |meta| {
            let not_first_level = meta.query_advice(not_first_level, Rotation::cur());

            // Check in leaf value row.
            let mut rot_into_storage_root = -LEAF_VALUE_S_IND - (ACCOUNT_LEAF_ROWS - ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND) - BRANCH_ROWS_NUM;
            let mut rot_into_last_account_row = -LEAF_VALUE_S_IND - 1;
            let mut rot_into_last_account_row_placeholder = -LEAF_VALUE_S_IND - 1 - BRANCH_ROWS_NUM;
            let mut is_leaf = meta.query_advice(storage_leaf.is_s_value, Rotation::cur());
            let mut rot_into_branch_init = -LEAF_VALUE_S_IND - BRANCH_ROWS_NUM;
            let mut is_branch_placeholder = meta.query_advice(
                s_main.bytes[IS_BRANCH_S_PLACEHOLDER_POS - RLP_NUM],
                Rotation(rot_into_branch_init),
            );
            if !is_s {
                rot_into_storage_root = -LEAF_VALUE_C_IND - (ACCOUNT_LEAF_ROWS - ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND) - BRANCH_ROWS_NUM;
                rot_into_last_account_row = -LEAF_VALUE_C_IND - 1;
                rot_into_last_account_row_placeholder = -LEAF_VALUE_C_IND - 1 - BRANCH_ROWS_NUM;
                is_leaf = meta.query_advice(storage_leaf.is_c_value, Rotation::cur());
                rot_into_branch_init = -LEAF_VALUE_C_IND - BRANCH_ROWS_NUM;
                is_branch_placeholder = meta.query_advice(
                    s_main.bytes[IS_BRANCH_C_PLACEHOLDER_POS - RLP_NUM],
                    Rotation(rot_into_branch_init),
                );
            }

            // Only check if there is an account above the leaf.
            let is_account_leaf_in_added_branch_placeholder =
                meta.query_advice(is_account_leaf_in_added_branch, Rotation(rot_into_last_account_row_placeholder));
            let is_account_leaf_in_added_branch =
                meta.query_advice(is_account_leaf_in_added_branch, Rotation(rot_into_last_account_row));

            let acc = meta.query_advice(accs.acc_s.rlc, Rotation::cur());

            let mut sc_hash = vec![];
            // Note: storage root is always in s_main.bytes!
            for column in s_main.bytes.iter() {
                sc_hash.push(meta.query_advice(*column, Rotation(rot_into_storage_root)));
            }
            let hash_rlc = bytes_expr_into_rlc(&sc_hash, acc_r);

            let mut constraints = vec![];
            constraints.push((
                not_first_level.clone()
                    * is_leaf.clone()
                    * (one.clone() - is_account_leaf_in_added_branch.clone()) // if account is directly above storage leaf, there is no placeholder branch
                    * is_account_leaf_in_added_branch_placeholder.clone()
                    * is_branch_placeholder.clone()
                    * acc,
                meta.query_fixed(keccak_table[0], Rotation::cur()),
            ));
            constraints.push((
                not_first_level.clone()
                    * is_leaf.clone()
                    * (one.clone() - is_account_leaf_in_added_branch.clone()) // if account is directly above storage leaf, there is no placeholder branch
                    * is_account_leaf_in_added_branch_placeholder.clone()
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
