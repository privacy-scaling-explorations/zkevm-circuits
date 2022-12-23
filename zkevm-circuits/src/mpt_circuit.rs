//! The MPT circuit implementation.
use eth_types::Field;
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Layouter, Region, SimpleFloorPlanner, Value},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, VirtualCells},
    poly::Rotation,
};

use std::convert::TryInto;

mod account_leaf;
mod branch;
mod columns;
mod helpers;
mod param;
mod proof_chain;
mod selectors;
mod storage_leaf;
mod witness_row;

use account_leaf::{
    account_leaf_key::AccountLeafKeyConfig,
    account_leaf_key_in_added_branch::AccountLeafKeyInAddedBranchConfig,
    account_leaf_nonce_balance::AccountLeafNonceBalanceConfig,
    account_leaf_storage_codehash::AccountLeafStorageCodehashConfig,
    account_non_existing::AccountNonExistingConfig, AccountLeaf, AccountLeafCols,
};
use branch::{
    branch_hash_in_parent::BranchHashInParentConfig, branch_init::BranchInitConfig,
    branch_key::BranchKeyConfig, branch_parallel::BranchParallelConfig,
    branch_rlc::BranchRLCConfig, extension_node::ExtensionNodeConfig,
    extension_node_inserted::ExtensionNodeInsertedConfig,
    extension_node_key::ExtensionNodeKeyConfig, Branch, BranchCols, BranchConfig,
};
use columns::{AccumulatorCols, DenoteCols, MainCols, PositionCols, ProofTypeCols};
use helpers::{get_is_extension_node, range256_check};
use proof_chain::ProofChainConfig;
use storage_leaf::{
    leaf_key::LeafKeyConfig, leaf_key_in_added_branch::LeafKeyInAddedBranchConfig,
    leaf_value::LeafValueConfig, StorageLeaf, StorageLeafCols,
};
use witness_row::{MptWitnessRow, MptWitnessRowType};

use param::HASH_WIDTH;
use selectors::SelectorsConfig;

use crate::{
    table::KeccakTable,
    util::{power_of_randomness_from_instance, Challenges},
};

use self::{columns::MPTTable, storage_leaf::leaf_non_existing::StorageNonExistingConfig};

/*
    MPT circuit contains S and C columns (other columns are mostly selectors).

    With S columns the prover proves the knowledge of key1/val1 that is in the
    trie with rootS.

    With C columns the prover proves the knowledge of key1/val2 that is in the
    trie with rootC. Note that key is the same for both S and C, whereas value
    is different. The prover thus proves the knowledge how to change value at key
    key1 from val1 to val2 that results the root being changed from rootS to rootC.

    The branch contains 16 nodes which are stored in 16 rows.
    A row looks like:
    [0,        160,      123,    ...,  148,     0,        160,    232,    ..., 92     ]
    [rlp1 (S), rlp2 (S), b0 (S), ...,  b31 (S), rlp1 (C), rlp2 C, b0 (C), ..., b31 (C)]

    Values bi (S) and bi(C) present hash of a node. Thus, the first half of a row
    is a S node:
    [rlp1, rlp2, b0, ..., b31]

    The second half of the row is a C node (same structure):
    [rlp1, rlp2, b0, ..., b31]

    We start with top level branch and then we follow branches (could be also extension
    nodes) down to the leaf.
*/

/// Merkle Patricia Trie config.
#[derive(Clone, Debug)]
pub struct MPTConfig<F> {
    pub(crate) proof_type: ProofTypeCols<F>,
    pub(crate) position_cols: PositionCols<F>,
    pub(crate) inter_start_root: Column<Advice>,
    pub(crate) inter_final_root: Column<Advice>,
    pub(crate) value_prev: Column<Advice>,
    pub(crate) value: Column<Advice>,
    pub(crate) accumulators: AccumulatorCols<F>,
    pub(crate) branch: BranchCols<F>,
    pub(crate) s_main: MainCols<F>,
    pub(crate) c_main: MainCols<F>,
    pub(crate) account_leaf: AccountLeafCols<F>,
    pub(crate) storage_leaf: StorageLeafCols<F>,
    pub(crate) denoter: DenoteCols<F>,
    keccak_table: KeccakTable,
    fixed_table: [Column<Fixed>; 3],
    pub(crate) address_rlc: Column<Advice>, /* The same in all rows of a modification. The same
                                             * as
                                             * address_rlc computed in the account leaf key row.
                                             * Needed to
                                             * enable lookup for storage key/value (to have
                                             * address RLC in
                                             * the same row as storage key/value). */
    account_leaf_key_s: AccountLeafKeyConfig<F>,
    account_leaf_key_c: AccountLeafKeyConfig<F>,
    account_leaf_nonce_balance_s: AccountLeafNonceBalanceConfig<F>,
    account_leaf_nonce_balance_c: AccountLeafNonceBalanceConfig<F>,
    account_leaf_storage_codehash_s: AccountLeafStorageCodehashConfig<F>,
    account_leaf_storage_codehash_c: AccountLeafStorageCodehashConfig<F>,
    account_leaf_key_in_added_branch: AccountLeafKeyInAddedBranchConfig<F>,
    account_non_existing: AccountNonExistingConfig<F>,
    branch_config: BranchConfig<F>,
    ext_node_config_s: ExtensionNodeConfig<F>,
    ext_node_config_c: ExtensionNodeConfig<F>,
    storage_leaf_key_s: LeafKeyConfig<F>,
    storage_leaf_key_c: LeafKeyConfig<F>,
    storage_leaf_value_s: LeafValueConfig<F>,
    storage_leaf_value_c: LeafValueConfig<F>,
    storage_leaf_key_in_added_branch: LeafKeyInAddedBranchConfig<F>,
    storage_non_existing: StorageNonExistingConfig<F>,
    ext_node_s_before_mod_config: ExtensionNodeInsertedConfig<F>,
    ext_node_s_after_mod_config: ExtensionNodeInsertedConfig<F>,
    pub(crate) randomness: F,
    pub(crate) check_zeros: bool,
    pub(crate) mpt_table: MPTTable,
}

/// Enumerator to determine the type of row in the fixed table.
#[derive(Clone, Copy, Debug)]
pub enum FixedTableTag {
    /// Power of randomness: [1, r], [2, r^2],...
    RMult,
    /// 0 - 15
    Range16,
    /// 0 - 255
    Range256,
    /// For checking there are 0s after the RLP stream ends
    RangeKeyLen256,
}

#[derive(Default)]
/*
Some values are accumulating through the rows (or block of rows) and we need to access the previous value
to continue the calculation, for this reason the previous values are stored in `ProofValues` struct.
Such accumulated value is for example `key_rlc` which stores the intermediate key RLC (in each branch
and extension node block a new intermediate key RLC is computed).
Also, for example, `modified_node` is given in branch init but needed to be set in every branch children row.
*/
pub(crate) struct ProofValues<F> {
    pub(crate) modified_node: u8, /* branch child that is being changed, it is the same in all
                                   * branch children rows */
    pub(crate) s_mod_node_hash_rlc: F, /* hash rlc of the modified_node for S proof, it is the
                                        * same in all branch children rows */
    pub(crate) c_mod_node_hash_rlc: F, /* hash rlc of the modified_node for C proof, it is the
                                        * same in all branch children rows */
    pub(crate) node_index: u8, // branch child index
    pub(crate) acc_s: F,       /* RLC accumulator for the whole node (taking into account all
                                * RLP bytes of the node) */
    pub(crate) acc_mult_s: F, // multiplier for acc_s
    pub(crate) acc_account_s: F,
    pub(crate) acc_mult_account_s: F,
    pub(crate) acc_account_c: F,
    pub(crate) acc_mult_account_c: F,
    pub(crate) acc_nonce_balance_s: F,
    pub(crate) acc_mult_nonce_balance_s: F,
    pub(crate) acc_nonce_balance_c: F,
    pub(crate) acc_mult_nonce_balance_c: F,
    pub(crate) acc_c: F, /* RLC accumulator for the whole node (taking into account all RLP
                          * bytes of the node) */
    pub(crate) acc_mult_c: F,         // multiplier for acc_c
    pub(crate) key_rlc: F,            /* used first for account address, then for storage key */
    pub(crate) key_rlc_mult: F,       // multiplier for key_rlc
    pub(crate) extension_node_rlc: F, // RLC accumulator for extension node
    pub(crate) key_rlc_prev: F,       /* for leaf after placeholder extension/branch, we need to
                                       * go one level back
                                       * to get previous key_rlc */
    pub(crate) key_rlc_mult_prev: F,
    pub(crate) mult_diff: F, /* power of randomness r: multiplier_curr = multiplier_prev *
                              * mult_diff */
    pub(crate) key_rlc_sel: bool, /* If true, nibble is multiplied by 16, otherwise by 1. */
    pub(crate) is_branch_s_placeholder: bool, // whether S branch is just a placeholder
    pub(crate) is_branch_c_placeholder: bool, // whether C branch is just a placeholder
    pub(crate) drifted_pos: u8,   /* needed when leaf turned into branch and leaf moves into a
                                   * branch where
                                   * it's at drifted_pos position */
    pub(crate) rlp_len_rem_s: i32, /* branch RLP length remainder, in each branch children row
                                    * this value
                                    * is subtracted by the number of RLP bytes in
                                    * this row (1 or 33) */
    pub(crate) rlp_len_rem_c: i32,
    pub(crate) is_extension_node: bool,
    pub(crate) is_even: bool,
    pub(crate) is_odd: bool,
    pub(crate) is_short: bool,
    pub(crate) is_long: bool,
    pub(crate) rlc1: F,
    pub(crate) rlc2: F,
    pub(crate) nonce_value_s: F,
    pub(crate) balance_value_s: F,
    pub(crate) before_account_leaf: bool,
    pub(crate) nibbles_num: usize,
}

impl<F: FieldExt> ProofValues<F> {
    fn new() -> Self {
        Self {
            key_rlc_mult: F::one(),
            key_rlc_mult_prev: F::one(),
            mult_diff: F::one(),
            key_rlc_sel: true,
            before_account_leaf: true,
            ..Default::default()
        }
    }
}

impl<F: FieldExt> MPTConfig<F> {
    /// Configure MPT Circuit
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        power_of_randomness: [Expression<F>; HASH_WIDTH],
        keccak_table: KeccakTable,
        check_zeros: bool,
    ) -> Self {
        // let _pub_root = meta.instance_column();
        let inter_start_root = meta.advice_column(); // state root before modification - first level S hash needs to be the same as
                                                     // start_root (works also if only storage proof, without account proof, but if
                                                     // this is to be allowed LeafKeyChip needs to be changed - careful with q_enable
                                                     // and q_not_first; not_first_level
                                                     // constraints would need to be added there too)
        let inter_final_root = meta.advice_column(); // state root after modification - first level C hash needs to be the same as
                                                     // end_root (works also if only storage proof, without account proof, but if
                                                     // this is to be allowed LeafKeyChip needs to be changed - careful with q_enable
                                                     // and q_not_first; not_first_level
                                                     // constraints would need to be added there too)

        let value_prev = meta.advice_column();
        let value = meta.advice_column();

        let position_cols = PositionCols::new(meta);

        let proof_type = ProofTypeCols::new(meta);
        let account_leaf = AccountLeafCols::new(meta);
        let storage_leaf = StorageLeafCols::new(meta);
        let branch = BranchCols::new(meta);

        let s_main = MainCols::new(meta);
        let c_main = MainCols::new(meta);

        let fixed_table: [Column<Fixed>; 3] = (0..3)
            .map(|_| meta.fixed_column())
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        /*
        Note: `key_rlc_mult` would not be needed if we would have
        big endian instead of little endian. However, then it would be much more
        difficult to handle the accumulator when we iterate over the key.
        At some point (but we do not know this point at compile time), the key ends
        and from there on the values in the row need to be 0s.
        However, if we are computing the RLC using little endian:
        `rlc = rlc + row[i] * r`,
        `rlc` will stay the same once r[i] = 0.
        If big endian would be used:
        `rlc = rlc * r + row[i]`,
        `rlc` would be multiplied by `r` when `row[i] = 0`.

        However, we need to ensure there are truly 0s after the RLP stream ends, this is done
        by `key_len_lookup` calls.
        */

        let accumulators = AccumulatorCols::new(meta);

        /*
        Note: `acc_s.mult` and `acc_c.mult` would not be needed if we would have
        big endian instead of little endian. However, then it would be much more
        difficult to handle the accumulator when we iterate over the row.
        For example, big endian would mean to compute `acc = acc * mult_r + row[i]`,
        but we do not want `acc` to be multiplied by `mult_r` when `row[i] = 0` where
        the stream already ended and 0s are only to fulfill the row.
        */

        let denoter = DenoteCols::new(meta);

        let address_rlc = meta.advice_column();

        SelectorsConfig::<F>::configure(
            meta,
            proof_type.clone(),
            position_cols.clone(),
            branch.clone(),
            account_leaf.clone(),
            storage_leaf.clone(),
            denoter.clone(),
        );

        ProofChainConfig::<F>::configure(
            meta,
            proof_type.clone(),
            position_cols.clone(),
            branch.is_init,
            account_leaf.clone(),
            storage_leaf.clone(),
            inter_start_root,
            inter_final_root,
            address_rlc,
        );

        let branch_config = BranchConfig::<F>::configure(
            meta,
            position_cols.clone(),
            account_leaf.is_in_added_branch,
            s_main.clone(),
            c_main.clone(),
            accumulators.clone(),
            branch.clone(),
            denoter.clone(),
            fixed_table,
            power_of_randomness[0].clone(),
        );

        BranchKeyConfig::<F>::configure(
            meta,
            position_cols.clone(),
            branch.clone(),
            account_leaf.is_in_added_branch,
            s_main.clone(),
            accumulators.key.clone(),
            power_of_randomness[0].clone(),
        );

        BranchParallelConfig::<F>::configure(
            meta,
            position_cols.clone(),
            branch.clone(),
            accumulators.s_mod_node_rlc,
            s_main.clone(),
            denoter.sel1,
            denoter.is_node_hashed_s,
            fixed_table,
            check_zeros,
        );

        BranchParallelConfig::<F>::configure(
            meta,
            position_cols.clone(),
            branch.clone(),
            accumulators.c_mod_node_rlc,
            c_main.clone(),
            denoter.sel2,
            denoter.is_node_hashed_c,
            fixed_table,
            check_zeros,
        );

        BranchHashInParentConfig::<F>::configure(
            meta,
            inter_start_root,
            position_cols.clone(),
            account_leaf.is_in_added_branch,
            branch.is_last_child,
            s_main.clone(),
            accumulators.clone(),
            keccak_table.clone(),
            power_of_randomness[0].clone(),
            true,
        );

        BranchHashInParentConfig::<F>::configure(
            meta,
            inter_final_root,
            position_cols.clone(),
            account_leaf.is_in_added_branch,
            branch.is_last_child,
            s_main.clone(),
            accumulators.clone(),
            keccak_table.clone(),
            power_of_randomness[0].clone(),
            false,
        );

        let ext_node_config_s = ExtensionNodeConfig::<F>::configure(
            meta,
            |meta| {
                let is_extension_node_s =
                    meta.query_advice(branch.is_extension_node_s, Rotation::cur());
                // is_extension_node is in branch init row
                let is_extension_node = get_is_extension_node(meta, s_main.bytes, -17);

                is_extension_node_s * is_extension_node
            },
            inter_start_root,
            position_cols.clone(),
            account_leaf.is_in_added_branch,
            branch.clone(),
            s_main.clone(),
            c_main.clone(),
            accumulators.clone(),
            keccak_table.clone(),
            power_of_randomness.clone(),
            fixed_table,
            true,
            check_zeros,
        );

        let ext_node_config_c = ExtensionNodeConfig::<F>::configure(
            meta,
            |meta| {
                let is_extension_node_c =
                    meta.query_advice(branch.is_extension_node_c, Rotation::cur());
                // is_extension_node is in branch init row
                let is_extension_node = get_is_extension_node(meta, s_main.bytes, -18);

                is_extension_node_c * is_extension_node
            },
            inter_final_root,
            position_cols.clone(),
            account_leaf.is_in_added_branch,
            branch.clone(),
            s_main.clone(),
            c_main.clone(),
            accumulators.clone(),
            keccak_table.clone(),
            power_of_randomness.clone(),
            fixed_table,
            false,
            check_zeros,
        );

        ExtensionNodeKeyConfig::<F>::configure(
            meta,
            position_cols.clone(),
            branch.clone(),
            account_leaf.is_in_added_branch,
            s_main.clone(),
            c_main.clone(),
            accumulators.clone(),
            fixed_table,
            power_of_randomness.clone(),
            check_zeros,
        );

        BranchInitConfig::<F>::configure(
            meta,
            |meta| {
                meta.query_advice(branch.is_init, Rotation::cur())
                    * meta.query_fixed(position_cols.q_enable, Rotation::cur())
            },
            s_main.clone(),
            accumulators.clone(),
            power_of_randomness[0].clone(),
            fixed_table,
        );

        BranchRLCConfig::<F>::configure(
            meta,
            |meta| {
                let q_not_first = meta.query_fixed(position_cols.q_not_first, Rotation::cur());
                let is_branch_child = meta.query_advice(branch.is_child, Rotation::cur());

                q_not_first * is_branch_child
            },
            s_main.clone(),
            accumulators.acc_s.clone(),
            denoter.is_node_hashed_s,
            accumulators.node_mult_diff_s,
            power_of_randomness.clone(),
            fixed_table,
        );

        BranchRLCConfig::<F>::configure(
            meta,
            |meta| {
                let q_not_first = meta.query_fixed(position_cols.q_not_first, Rotation::cur());
                let is_branch_child = meta.query_advice(branch.is_child, Rotation::cur());

                q_not_first * is_branch_child
            },
            c_main.clone(),
            accumulators.acc_c.clone(),
            denoter.is_node_hashed_c,
            accumulators.node_mult_diff_c,
            power_of_randomness.clone(),
            fixed_table,
        );

        let storage_leaf_key_s = LeafKeyConfig::<F>::configure(
            meta,
            |meta| {
                let q_not_first = meta.query_fixed(position_cols.q_not_first, Rotation::cur());
                let not_first_level =
                    meta.query_advice(position_cols.not_first_level, Rotation::cur());
                let is_leaf_s = meta.query_advice(storage_leaf.is_s_key, Rotation::cur());

                // NOTE/TODO: If having only storage proof is to be allowed, then this needs to
                // be changed as currently the first row is not checked (and
                // leaf key can appear in the first row if there is no account
                // proof). See how it is done for account_leaf_key.rs which can appear in the
                // first row. q_not_first is needed to avoid PoisenedConstraint.
                q_not_first * not_first_level * is_leaf_s
            },
            s_main.clone(),
            c_main.clone(),
            accumulators.clone(),
            account_leaf.is_in_added_branch,
            denoter.clone(),
            power_of_randomness.clone(),
            fixed_table,
            true,
            check_zeros,
        );

        let storage_leaf_key_c = LeafKeyConfig::<F>::configure(
            meta,
            |meta| {
                let q_not_first = meta.query_fixed(position_cols.q_not_first, Rotation::cur());
                let not_first_level =
                    meta.query_advice(position_cols.not_first_level, Rotation::cur());
                let is_leaf_c = meta.query_advice(storage_leaf.is_c_key, Rotation::cur());

                // NOTE/TODO: If having only storage proof is to be allowed, then this needs to
                // be changed as currently the first row is not checked (and
                // leaf key can appear in the first row if there is no account
                // proof). See how it is done for account_leaf_key.rs which can appear in the
                // first row. q_not_first is needed to avoid PoisenedConstraint.
                q_not_first * not_first_level * is_leaf_c
            },
            s_main.clone(),
            c_main.clone(),
            accumulators.clone(),
            account_leaf.is_in_added_branch,
            denoter.clone(),
            power_of_randomness.clone(),
            fixed_table,
            false,
            check_zeros,
        );

        let storage_leaf_key_in_added_branch = LeafKeyInAddedBranchConfig::<F>::configure(
            meta,
            |meta| {
                let q_not_first = meta.query_fixed(position_cols.q_not_first, Rotation::cur());
                let not_first_level =
                    meta.query_advice(position_cols.not_first_level, Rotation::cur());
                let is_leaf = meta.query_advice(storage_leaf.is_in_added_branch, Rotation::cur());

                q_not_first * not_first_level * is_leaf
            },
            s_main.clone(),
            c_main.clone(),
            branch.clone(),
            accumulators.clone(),
            branch.drifted_pos,
            account_leaf.is_in_added_branch,
            power_of_randomness.clone(),
            fixed_table,
            keccak_table.clone(),
            check_zeros,
        );

        let storage_leaf_value_s = LeafValueConfig::<F>::configure(
            meta,
            proof_type.clone(),
            position_cols.clone(),
            storage_leaf.is_s_value,
            s_main.clone(),
            c_main.clone(),
            keccak_table.clone(),
            accumulators.clone(),
            denoter.clone(),
            account_leaf.is_in_added_branch,
            value_prev,
            value,
            true,
            power_of_randomness[0].clone(),
            fixed_table,
            check_zeros,
        );

        let storage_leaf_value_c = LeafValueConfig::<F>::configure(
            meta,
            proof_type.clone(),
            position_cols.clone(),
            storage_leaf.is_c_value,
            s_main.clone(),
            c_main.clone(),
            keccak_table.clone(),
            accumulators.clone(),
            denoter.clone(),
            account_leaf.is_in_added_branch,
            value_prev,
            value,
            false,
            power_of_randomness[0].clone(),
            fixed_table,
            check_zeros,
        );

        let storage_non_existing = StorageNonExistingConfig::<F>::configure(
            meta,
            |meta| {
                let q_enable = meta.query_fixed(position_cols.q_enable, Rotation::cur());
                let is_leaf_non_existing_row =
                    meta.query_advice(storage_leaf.is_non_existing, Rotation::cur());
                let is_storage_non_existing_proof =
                    meta.query_advice(proof_type.is_non_existing_storage_proof, Rotation::cur());

                q_enable * is_leaf_non_existing_row * is_storage_non_existing_proof
            },
            s_main.clone(),
            c_main.clone(),
            accumulators.clone(),
            denoter.sel2,
            account_leaf.is_in_added_branch,
            power_of_randomness.clone(),
            fixed_table,
            check_zeros,
        );

        let account_leaf_key_s = AccountLeafKeyConfig::<F>::configure(
            meta,
            proof_type.clone(),
            |meta| {
                let q_enable = meta.query_fixed(position_cols.q_enable, Rotation::cur());
                let is_account_leaf_key_s =
                    meta.query_advice(account_leaf.is_key_s, Rotation::cur());

                q_enable * is_account_leaf_key_s
            },
            position_cols.clone(),
            s_main.clone(),
            c_main.clone(),
            accumulators.clone(),
            power_of_randomness.clone(),
            fixed_table,
            address_rlc,
            denoter.sel2,
            true,
            check_zeros,
        );

        let account_leaf_key_c = AccountLeafKeyConfig::<F>::configure(
            meta,
            proof_type.clone(),
            |meta| {
                let q_enable = meta.query_fixed(position_cols.q_enable, Rotation::cur());
                let is_account_leaf_key_c =
                    meta.query_advice(account_leaf.is_key_c, Rotation::cur());

                q_enable * is_account_leaf_key_c
            },
            position_cols.clone(),
            s_main.clone(),
            c_main.clone(),
            accumulators.clone(),
            power_of_randomness.clone(),
            fixed_table,
            address_rlc,
            denoter.sel2,
            false,
            check_zeros,
        );

        let account_non_existing = AccountNonExistingConfig::<F>::configure(
            meta,
            |meta| {
                let q_enable = meta.query_fixed(position_cols.q_enable, Rotation::cur());
                let is_account_non_existing_row =
                    meta.query_advice(account_leaf.is_non_existing_account_row, Rotation::cur());
                let is_account_non_existing_proof =
                    meta.query_advice(proof_type.is_non_existing_account_proof, Rotation::cur());

                q_enable * is_account_non_existing_row * is_account_non_existing_proof
            },
            position_cols.not_first_level,
            s_main.clone(),
            c_main.clone(),
            accumulators.clone(),
            denoter.sel1,
            power_of_randomness.clone(),
            fixed_table,
            address_rlc,
            check_zeros,
        );

        let account_leaf_nonce_balance_s = AccountLeafNonceBalanceConfig::<F>::configure(
            meta,
            proof_type.clone(),
            |meta| {
                let q_not_first = meta.query_fixed(position_cols.q_not_first, Rotation::cur());
                let is_account_leaf_nonce_balance_s =
                    meta.query_advice(account_leaf.is_nonce_balance_s, Rotation::cur());
                q_not_first * is_account_leaf_nonce_balance_s
            },
            s_main.clone(),
            c_main.clone(),
            accumulators.clone(),
            value_prev,
            value,
            power_of_randomness.clone(),
            denoter.clone(),
            fixed_table,
            true,
            check_zeros,
        );

        let account_leaf_nonce_balance_c = AccountLeafNonceBalanceConfig::<F>::configure(
            meta,
            proof_type.clone(),
            |meta| {
                let q_not_first = meta.query_fixed(position_cols.q_not_first, Rotation::cur());
                let is_account_leaf_nonce_balance_c =
                    meta.query_advice(account_leaf.is_nonce_balance_c, Rotation::cur());
                q_not_first * is_account_leaf_nonce_balance_c
            },
            s_main.clone(),
            c_main.clone(),
            accumulators.clone(),
            value_prev,
            value,
            power_of_randomness.clone(),
            denoter.clone(),
            fixed_table,
            false,
            check_zeros,
        );

        let account_leaf_storage_codehash_s = AccountLeafStorageCodehashConfig::<F>::configure(
            meta,
            proof_type.clone(),
            inter_start_root,
            position_cols.clone(),
            account_leaf.is_storage_codehash_s,
            s_main.clone(),
            c_main.clone(),
            power_of_randomness[0].clone(),
            accumulators.clone(),
            value_prev,
            value,
            fixed_table,
            denoter.clone(),
            keccak_table.clone(),
            true,
        );

        let account_leaf_storage_codehash_c = AccountLeafStorageCodehashConfig::<F>::configure(
            meta,
            proof_type.clone(),
            inter_final_root,
            position_cols.clone(),
            account_leaf.is_storage_codehash_c,
            s_main.clone(),
            c_main.clone(),
            power_of_randomness[0].clone(),
            accumulators.clone(),
            value_prev,
            value,
            fixed_table,
            denoter.clone(),
            keccak_table.clone(),
            false,
        );

        let account_leaf_key_in_added_branch = AccountLeafKeyInAddedBranchConfig::<F>::configure(
            meta,
            |meta| {
                let q_not_first = meta.query_fixed(position_cols.q_not_first, Rotation::cur());
                let not_first_level =
                    meta.query_advice(position_cols.not_first_level, Rotation::cur());
                let is_account_leaf_in_added_branch =
                    meta.query_advice(account_leaf.is_in_added_branch, Rotation::cur());

                q_not_first * not_first_level * is_account_leaf_in_added_branch
            },
            position_cols.not_first_level,
            s_main.clone(),
            c_main.clone(),
            branch.clone(),
            accumulators.clone(),
            branch.drifted_pos,
            denoter.clone(),
            power_of_randomness.clone(),
            fixed_table,
            keccak_table.clone(),
            check_zeros,
        );

        let ext_node_s_before_mod_config = ExtensionNodeInsertedConfig::<F>::configure(
            meta,
            |meta| {
                meta.query_advice(branch.is_mod_ext_node_s_before_mod, Rotation::cur())
            },
            inter_start_root,
            inter_final_root,
            position_cols.clone(),
            account_leaf.is_in_added_branch,
            branch.clone(),
            s_main.clone(),
            c_main.clone(),
            accumulators.clone(),
            keccak_table.clone(),
            power_of_randomness.clone(),
            fixed_table,
            true,
            check_zeros,
        );

        /*
        Note: we do not need any constraints (except for the correspondence of first/second
        nibbles) for `ext_node_c_before_mode_config` and `ext_node_c_before_mode_config`
        because `S` and `C` rows are the same (except for the second nibbles) for before and after
        - `C` is used only the second nibbles.
        */

        let ext_node_s_after_mod_config = ExtensionNodeInsertedConfig::<F>::configure(
            meta,
            |meta| {
                meta.query_advice(branch.is_mod_ext_node_s_after_mod, Rotation::cur())
            },
            inter_start_root,
            inter_final_root,
            position_cols.clone(),
            account_leaf.is_in_added_branch,
            branch.clone(),
            s_main.clone(),
            c_main.clone(),
            accumulators.clone(),
            keccak_table.clone(),
            power_of_randomness.clone(),
            fixed_table,
            false,
            check_zeros,
        );

        let mpt_table = MPTTable {
            address_rlc,
            proof_type: proof_type.proof_type,
            key_rlc: accumulators.key.mult,
            value_prev,
            value,
            root_prev: inter_start_root,
            root: inter_final_root,
        }; 

        let randomness = F::zero();
        MPTConfig {
            proof_type,
            position_cols,
            inter_start_root,
            inter_final_root,
            value_prev,
            value,
            branch,
            s_main,
            c_main,
            account_leaf,
            storage_leaf,
            accumulators,
            denoter,
            keccak_table,
            fixed_table,
            address_rlc,
            account_leaf_key_s,
            account_leaf_key_c,
            account_leaf_nonce_balance_s,
            account_leaf_nonce_balance_c,
            account_leaf_storage_codehash_s,
            account_leaf_storage_codehash_c,
            account_leaf_key_in_added_branch,
            account_non_existing,
            branch_config,
            ext_node_config_s,
            ext_node_config_c,
            storage_leaf_key_s,
            storage_leaf_key_c,
            storage_leaf_value_s,
            storage_leaf_value_c,
            storage_leaf_key_in_added_branch,
            storage_non_existing,
            ext_node_s_before_mod_config,
            ext_node_s_after_mod_config,
            randomness,
            check_zeros,
            mpt_table,
        }
    }

    pub(crate) fn compute_key_rlc(
        &self,
        row: &[u8],
        key_rlc: &mut F,
        key_rlc_mult: &mut F,
        start: usize,
    ) {
        let even_num_of_nibbles = row[start + 1] == 32;
        // If odd number of nibbles, we have nibble+48 in s_advices[0].
        if !even_num_of_nibbles {
            *key_rlc += F::from((row[start + 1] - 48) as u64) * *key_rlc_mult;
            *key_rlc_mult *= self.randomness;

            let len = row[start] as usize - 128;
            self.compute_acc_and_mult(
                row,
                key_rlc,
                key_rlc_mult,
                start + 2,
                len - 1, // -1 because one byte was already considered
            );
        } else {
            let len = row[start] as usize - 128;
            self.compute_acc_and_mult(
                row,
                key_rlc,
                key_rlc_mult,
                start + 2,
                len - 1, /* -1 because the first byte doesn't
                          * contain any key byte (it's just 32) */
            );
        }
    }

    pub(crate) fn compute_acc_and_mult(
        &self,
        row: &[u8],
        acc: &mut F,
        mult: &mut F,
        start: usize,
        len: usize,
    ) {
        for i in 0..len {
            *acc += F::from(row[start + i] as u64) * *mult;
            *mult *= self.randomness;
        }
    }

    pub(crate) fn compute_rlc_and_assign(
        &self,
        region: &mut Region<'_, F>,
        row: &[u8],
        pv: &mut ProofValues<F>,
        offset: usize,
        s_start_len: (usize, usize),
        c_start_len: (usize, usize),
    ) -> Result<(), Error> {
        self.compute_acc_and_mult(
            row,
            &mut pv.rlc1,
            &mut F::one(),
            s_start_len.0,
            s_start_len.1,
        );
        region.assign_advice(
            || "assign s_mod_node_hash_rlc".to_string(),
            self.accumulators.s_mod_node_rlc,
            offset,
            || Value::known(pv.rlc1),
        )?;

        self.compute_acc_and_mult(
            row,
            &mut pv.rlc2,
            &mut F::one(),
            c_start_len.0,
            c_start_len.1,
        );
        region.assign_advice(
            || "assign c_mod_node_hash_rlc".to_string(),
            self.accumulators.c_mod_node_rlc,
            offset,
            || Value::known(pv.rlc2),
        )?;

        Ok(())
    }

    pub(crate) fn assign_acc(
        &self,
        region: &mut Region<'_, F>,
        acc_s: F,
        acc_mult_s: F,
        acc_c: F,
        acc_mult_c: F,
        offset: usize,
    ) -> Result<(), Error> {
        region.assign_advice(
            || "assign acc_s".to_string(),
            self.accumulators.acc_s.rlc,
            offset,
            || Value::known(acc_s),
        )?;

        region.assign_advice(
            || "assign acc_mult_s".to_string(),
            self.accumulators.acc_s.mult,
            offset,
            || Value::known(acc_mult_s),
        )?;

        region.assign_advice(
            || "assign acc_c".to_string(),
            self.accumulators.acc_c.rlc,
            offset,
            || Value::known(acc_c),
        )?;

        region.assign_advice(
            || "assign acc_mult_c".to_string(),
            self.accumulators.acc_c.mult,
            offset,
            || Value::known(acc_mult_c),
        )?;

        Ok(())
    }

    /*
    assign_long_short is used for setting flags for storage leaf and storage value.
    For storage leaf, it sets whether it is short (one RLP byte) or long (two RLP bytes)
    or last level (no nibbles in leaf, all nibbles in the path above the leaf) or one nibble.
    Note that last_level and one_nibble imply having only one RLP byte.

    For storage value, it sets whether it is short or long (value having more than one byte).
    */
    pub(crate) fn assign_long_short(
        &self,
        region: &mut Region<'_, F>,
        typ: &str,
        offset: usize,
    ) -> Result<(), Error> {
        let mut flag1 = false;
        let mut flag2 = false;
        // for one_nibble, it is both 0
        if typ == "long" {
            flag1 = true;
        } else if typ == "short" {
            flag2 = true;
        } else if typ == "last_level" {
            flag1 = true;
            flag2 = true;
        }
        region
            .assign_advice(
                || "assign s_modified_node_rlc".to_string(),
                self.accumulators.s_mod_node_rlc,
                offset,
                || Value::known(F::from(flag1 as u64)),
            )
            .ok();
        region
            .assign_advice(
                || "assign c_modified_node_rlc".to_string(),
                self.accumulators.c_mod_node_rlc,
                offset,
                || Value::known(F::from(flag2 as u64)),
            )
            .ok();

        Ok(())
    }

    /// Make the assignments to the MPTCircuit
    pub fn assign(
        &mut self,
        mut layouter: impl Layouter<F>,
        witness: &[MptWitnessRow<F>],
        randomness: F,
    ) {
        self.randomness = randomness;

        layouter
            .assign_region(
                || "MPT",
                |mut region| {
                    let mut offset = 0;
                    let mut pv = ProofValues::new();

                    for (ind, row) in witness
                        .iter()
                        .filter(|r| r.get_type() != MptWitnessRowType::HashToBeComputed)
                        .enumerate()
                    {
                        if offset > 0 {
                            let row_prev = &witness[offset - 1];
                            let not_first_level_prev = row_prev.not_first_level();
                            let not_first_level_cur = row.not_first_level();
                            if not_first_level_cur == 0 && not_first_level_prev == 1 {
                                pv = ProofValues::new();
                            }
                        }

                        region.assign_fixed(
                            || "q_enable",
                            self.position_cols.q_enable,
                            offset,
                            || Value::known(F::one()),
                        )?;
                        
                        if row.get_type() == MptWitnessRowType::AccountLeafKeyS {
                            // account leaf key
                            pv.before_account_leaf = false;
                        }

                        let q_not_first = if ind == 0 { F::zero() } else { F::one() };
                        region.assign_fixed(
                            || "not first",
                            self.position_cols.q_not_first,
                            offset,
                            || Value::known(q_not_first),
                        )?;

                        region.assign_advice(
                            || "not first level",
                            self.position_cols.not_first_level,
                            offset,
                            || Value::known(F::from(row.not_first_level() as u64)),
                        )?;

                        row.assign_lookup_columns(&mut region, self, &pv, offset)?;

                        if row.get_type() == MptWitnessRowType::InitBranch {
                            self.branch_config
                                .assign_branch_init(&mut region, witness, self, &mut pv, offset)
                                .ok();

                            offset += 1;
                        } else if row.get_type() == MptWitnessRowType::BranchChild {
                            self.branch_config
                                .assign_branch_child(&mut region, witness, self, &mut pv, offset)
                                .ok();

                            offset += 1;
                        } else {
                            // leaf s or leaf c or leaf key s or leaf key c
                            let mut account_leaf = AccountLeaf::default();
                            let mut storage_leaf = StorageLeaf::default();
                            let mut branch = Branch::default();

                            if row.get_type() == MptWitnessRowType::StorageLeafSKey {
                                storage_leaf.is_s_key = true;
                            } else if row.get_type() == MptWitnessRowType::StorageLeafCKey {
                                storage_leaf.is_c_key = true;
                            } else if row.get_type() == MptWitnessRowType::AccountLeafKeyS {
                                account_leaf.is_key_s = true;
                            } else if row.get_type() == MptWitnessRowType::AccountLeafKeyC {
                                account_leaf.is_key_c = true;
                            } else if row.get_type() == MptWitnessRowType::AccountLeafNonceBalanceS
                            {
                                account_leaf.is_nonce_balance_s = true;
                            } else if row.get_type() == MptWitnessRowType::AccountLeafNonceBalanceC
                            {
                                account_leaf.is_nonce_balance_c = true;
                            } else if row.get_type() == MptWitnessRowType::AccountLeafRootCodehashS
                            {
                                account_leaf.is_storage_codehash_s = true;
                            } else if row.get_type() == MptWitnessRowType::AccountLeafRootCodehashC
                            {
                                account_leaf.is_storage_codehash_c = true;
                            } else if row.get_type()
                                == MptWitnessRowType::AccountLeafNeighbouringLeaf
                            {
                                account_leaf.is_in_added_branch = true;
                                pv.key_rlc = F::zero(); // account address until here, storage key from here on
                                pv.key_rlc_mult = F::one();
                                pv.key_rlc_prev = F::zero();
                                pv.key_rlc_mult_prev = F::one();
                                pv.key_rlc_sel = true;
                                pv.nibbles_num = 0;
                                /*
                                Note: The constraints for ensuring that in the first account and first storage level
                                the key RLC is 0 and the key RLC mult is 1 are in:
                                 - `account_leaf_key.rs` for when the node in the first level is an account leaf
                                 - `branch_key.rs` for when the node in the first level is a branch
                                 - `extension_node_key.rs` for when the node in the first level is an extension node.

                                Similarly for `sel`. For `key_rlc_prev` and `key_rlc_mult_prev` there are no
                                columns, these values are used for internal computation, like for `key_rlc`
                                after the branch placeholder (when we need to reach back to the branch above
                                the placeholder).

                                The constraints for ensuring that in the first account and first storage level
                                `nibbles_num` is 0 are in:
                                 - `account_leaf_key.rs` for when the node in the first level is an account leaf
                                 - `branch.rs` for when the node in the first level is a branch
                                 - `extension_node.rs` for when the node in the first level is an extension node.
                                */
                            } else if row.get_type() == MptWitnessRowType::StorageLeafSValue {
                                storage_leaf.is_s_value = true;
                            } else if row.get_type() == MptWitnessRowType::StorageLeafCValue {
                                storage_leaf.is_c_value = true;
                            } else if row.get_type() == MptWitnessRowType::NeighbouringStorageLeaf {
                                storage_leaf.is_in_added_branch = true;
                            } else if row.get_type() == MptWitnessRowType::StorageNonExisting {
                                storage_leaf.is_non_existing = true;
                            } else if row.get_type() == MptWitnessRowType::ExtensionNodeS {
                                branch.is_extension_node_s = true;
                            } else if row.get_type() == MptWitnessRowType::ExtensionNodeC {
                                branch.is_extension_node_c = true;
                            } else if row.get_type() == MptWitnessRowType::AccountNonExisting {
                                account_leaf.is_non_existing_account_row = true;
                            } else if row.get_type() == MptWitnessRowType::ModExtNodeSBeforeMod {
                                branch.is_mod_ext_node_s_before_mod = true;
                            } else if row.get_type() == MptWitnessRowType::ModExtNodeCBeforeMod {
                                branch.is_mod_ext_node_c_before_mod = true;
                            } else if row.get_type() == MptWitnessRowType::ModExtNodeSAfterMod {
                                branch.is_mod_ext_node_s_after_mod = true;
                            } else if row.get_type() == MptWitnessRowType::ModExtNodeCAfterMod {
                                branch.is_mod_ext_node_c_after_mod = true;
                            } else if row.get_type() == MptWitnessRowType::ModExtNodeBeforeModSelectors {
                                branch.is_mod_ext_node_before_mod_selectors = true;
                            } else if row.get_type() == MptWitnessRowType::ModExtNodeAfterModSelectors {
                                branch.is_mod_ext_node_after_mod_selectors = true;
                            }

                            row.assign(
                                &mut region,
                                self,
                                account_leaf,
                                storage_leaf,
                                branch,
                                offset,
                            )?;

                            // Storage leaf key
                            if row.get_type() == MptWitnessRowType::StorageLeafSKey {
                                self.storage_leaf_key_s.assign(
                                    &mut region,
                                    self,
                                    &mut pv,
                                    row,
                                    offset,
                                );
                            } else if row.get_type() == MptWitnessRowType::StorageLeafCKey {
                                self.storage_leaf_key_c.assign(
                                    &mut region,
                                    self,
                                    &mut pv,
                                    row,
                                    offset,
                                );
                            } else if row.get_type() == MptWitnessRowType::StorageLeafSValue {
                                self.storage_leaf_value_s.assign(
                                    &mut region,
                                    self,
                                    witness,
                                    &mut pv,
                                    offset,
                                    true,
                                );
                            } else if row.get_type() == MptWitnessRowType::StorageLeafCValue {
                                self.storage_leaf_value_c.assign(
                                    &mut region,
                                    self,
                                    witness,
                                    &mut pv,
                                    offset,
                                    false,
                                );
                            } else if row.get_type() == MptWitnessRowType::StorageNonExisting {
                                self.storage_non_existing.assign(
                                    &mut region,
                                    self,
                                    &mut pv,
                                    witness,
                                    offset,
                                );
                            } else if row.get_type() == MptWitnessRowType::AccountLeafKeyS {
                                self.account_leaf_key_s.assign(
                                    &mut region,
                                    self,
                                    &mut pv,
                                    row,
                                    offset,
                                );
                            } else if row.get_type() == MptWitnessRowType::AccountLeafKeyC {
                                self.account_leaf_key_c.assign(
                                    &mut region,
                                    self,
                                    &mut pv,
                                    row,
                                    offset,
                                );
                            } else if row.get_type() == MptWitnessRowType::AccountLeafNonceBalanceS
                            {
                                self.account_leaf_nonce_balance_s.assign(
                                    &mut region,
                                    self,
                                    &mut pv,
                                    row,
                                    offset,
                                );
                            } else if row.get_type() == MptWitnessRowType::AccountLeafNonceBalanceC
                            {
                                self.account_leaf_nonce_balance_c.assign(
                                    &mut region,
                                    self,
                                    &mut pv,
                                    row,
                                    offset,
                                );
                            } else if row.get_type() == MptWitnessRowType::AccountLeafRootCodehashS
                            {
                                self.account_leaf_storage_codehash_s.assign(
                                    &mut region,
                                    self,
                                    &mut pv,
                                    row,
                                    offset,
                                );
                            } else if row.get_type() == MptWitnessRowType::AccountLeafRootCodehashC
                            {
                                self.account_leaf_storage_codehash_c.assign(
                                    &mut region,
                                    self,
                                    &mut pv,
                                    row,
                                    offset,
                                );
                            } else if row.get_type() == MptWitnessRowType::NeighbouringStorageLeaf
                                && row.get_byte(1) != 0
                            {
                                self.storage_leaf_key_in_added_branch.assign(
                                    &mut region,
                                    self,
                                    &mut pv,
                                    row,
                                    offset,
                                );
                            } else if row.get_type() == MptWitnessRowType::ExtensionNodeS {
                                self.ext_node_config_s.assign(
                                    &mut region,
                                    self,
                                    &mut pv,
                                    row,
                                    offset,
                                    true,
                                );
                            } else if row.get_type() == MptWitnessRowType::ExtensionNodeC {
                                self.ext_node_config_c.assign(
                                    &mut region,
                                    self,
                                    &mut pv,
                                    row,
                                    offset,
                                    false,
                                );
                            } else if row.get_type()
                                == MptWitnessRowType::AccountLeafNeighbouringLeaf
                                && row.get_byte(1) != 0
                            {
                                // row[1] != 0 just to avoid usize problems below (when row doesn't
                                // need to be assigned).
                                self.account_leaf_key_in_added_branch.assign(
                                    &mut region,
                                    self,
                                    &mut pv,
                                    &row.bytes,
                                    offset,
                                );
                            } else if row.get_type() == MptWitnessRowType::AccountNonExisting {
                                self.account_non_existing.assign(
                                    &mut region,
                                    self,
                                    witness,
                                    offset,
                                );
                            } else if row.get_type() == MptWitnessRowType::ModExtNodeSBeforeMod {
                                self.ext_node_s_before_mod_config.assign(
                                    &mut region,
                                    self,
                                    &mut pv,
                                    row,
                                    offset,
                                );
                            } else if row.get_type() == MptWitnessRowType::ModExtNodeSAfterMod {
                                self.ext_node_s_after_mod_config.assign(
                                    &mut region,
                                    self,
                                    &mut pv,
                                    row,
                                    offset,
                                );
                            }

                            offset += 1;
                        }
                    }

                    Ok(())
                },
            )
            .ok();
    }

    fn load_fixed_table(
        &self,
        layouter: &mut impl Layouter<F>,
        randomness: F,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "fixed table",
            |mut region| {
                let mut offset = 0;
                let mut mult = F::one();
                for ind in 0..(2 * HASH_WIDTH + 1) {
                    region.assign_fixed(
                        || "fixed table",
                        self.fixed_table[0],
                        offset,
                        || Value::known(F::from(FixedTableTag::RMult as u64)),
                    )?;

                    region.assign_fixed(
                        || "fixed table",
                        self.fixed_table[1],
                        offset,
                        || Value::known(F::from(ind as u64)),
                    )?;

                    region.assign_fixed(
                        || "fixed table",
                        self.fixed_table[2],
                        offset,
                        || Value::known(mult),
                    )?;
                    mult *= randomness;

                    offset += 1;
                }

                for ind in 0..256 {
                    region.assign_fixed(
                        || "fixed table",
                        self.fixed_table[0],
                        offset,
                        || Value::known(F::from(FixedTableTag::Range256 as u64)),
                    )?;

                    region.assign_fixed(
                        || "fixed table",
                        self.fixed_table[1],
                        offset,
                        || Value::known(F::from(ind as u64)),
                    )?;

                    offset += 1;
                }

                if self.check_zeros {
                    for ind in 0..(33 * 255) {
                        region.assign_fixed(
                            || "fixed table",
                            self.fixed_table[0],
                            offset,
                            || Value::known(F::from(FixedTableTag::RangeKeyLen256 as u64)),
                        )?;

                        region.assign_fixed(
                            || "fixed table",
                            self.fixed_table[1],
                            offset,
                            || Value::known(F::from(ind as u64)),
                        )?;

                        offset += 1;
                    }
                }

                for ind in 0..16 {
                    region.assign_fixed(
                        || "fixed table",
                        self.fixed_table[0],
                        offset,
                        || Value::known(F::from(FixedTableTag::Range16 as u64)),
                    )?;

                    region.assign_fixed(
                        || "fixed table",
                        self.fixed_table[1],
                        offset,
                        || Value::known(F::from(ind as u64)),
                    )?;

                    offset += 1;
                }

                Ok(())
            },
        )
    }
}

#[derive(Default)]
struct MPTCircuit<F> {
    witness: Vec<Vec<u8>>,
    randomness: F,
}

impl<F: Field> Circuit<F> for MPTCircuit<F> {
    type Config = MPTConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let keccak_table = KeccakTable::construct(meta);
        let power_of_randomness: [Expression<F>; HASH_WIDTH] =
            power_of_randomness_from_instance(meta);

        // Some constraints require 2^13 table, for testing purposes these constraints
        // can be disabled by setting check_zeros to false.
        // TODO: check_zeros is to be removed once the development is finished
        let check_zeros = false;

        MPTConfig::configure(meta, power_of_randomness, keccak_table, check_zeros)
    }

    fn synthesize(
        &self,
        mut config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let mut to_be_hashed = vec![];

        let mut witness_rows = vec![];
        for row in self.witness.iter() {
            if row[row.len() - 1] == 5 {
                to_be_hashed.push(row[0..row.len() - 1].to_vec());
            } else {
                let row = MptWitnessRow::new(row[0..row.len()].to_vec());
                witness_rows.push(row);
            }
        }

        let challenges = Challenges::mock(Value::known(self.randomness));
        config
            .keccak_table
            .dev_load(&mut layouter, &to_be_hashed, &challenges, false)
            .ok();

        config.load_fixed_table(&mut layouter, self.randomness).ok();
        config.assign(layouter, &witness_rows, self.randomness);

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use param::IS_NON_EXISTING_STORAGE_POS;

    use crate::mpt_circuit::helpers::bytes_into_rlc;

    use super::*;

    use halo2_proofs::{dev::MockProver, halo2curves::bn256::Fr};

    use std::fs;

    #[test]
    fn test_mpt() {
        // for debugging:
        let path = "src/mpt_circuit/tests";
        // let path = "tests";
        let files = fs::read_dir(path).unwrap();
        files
            .filter_map(Result::ok)
            .filter(|d| {
                if let Some(e) = d.path().extension() {
                    e == "json"
                } else {
                    false
                }
            })
            .for_each(|f| {
                let path = f.path();
                let mut parts = path.to_str().unwrap().split('-');
                parts.next();
                let file = std::fs::File::open(path.clone());
                let reader = std::io::BufReader::new(file.unwrap());
                let w: Vec<Vec<u8>> = serde_json::from_reader(reader).unwrap();

                let mut pub_root = vec![];
                let acc_r = Fr::one() + Fr::one();
                let mut count = 0;
                for row in w.iter().filter(|r| r[r.len() - 1] != 5) {
                    let l = row.len();
                    let pub_root_rlc = bytes_into_rlc(
                        &row[l - HASH_WIDTH - IS_NON_EXISTING_STORAGE_POS
                            ..l - HASH_WIDTH - IS_NON_EXISTING_STORAGE_POS + HASH_WIDTH],
                        acc_r,
                    );

                    pub_root.push(pub_root_rlc);
                    count += 1;
                }
                // TODO: add pub_root to instances

                let randomness = Fr::one() + Fr::one();
                let instance: Vec<Vec<Fr>> = (1..HASH_WIDTH + 1)
                    .map(|exp| vec![randomness.pow(&[exp as u64, 0, 0, 0]); count])
                    .collect();

                let circuit = MPTCircuit::<Fr> {
                    witness: w,
                    randomness,
                };

                println!("{:?}", path);
                // let prover = MockProver::run(9, &circuit, vec![pub_root]).unwrap();
                let prover = MockProver::run(9, &circuit, instance).unwrap();
                assert_eq!(prover.verify(), Ok(()));
            });
    }
}
