//! The MPT circuit implementation.
use eth_types::Field;
use gadgets::{
    impl_expr,
    util::{sum, Expr},
};
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Layouter, Region, SimpleFloorPlanner, Value},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, VirtualCells},
    poly::Rotation,
};

use std::{convert::TryInto, env::var, ops::Range};

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
    branch_key::BranchKeyConfig, branch_rlc::BranchRLCConfig, extension_node::ExtensionNodeConfig,
    Branch, BranchCols, BranchConfig,
};
use columns::{AccumulatorCols, DenoteCols, MainCols, PositionCols, ProofTypeCols};
use proof_chain::ProofChainConfig;
use storage_leaf::{
    leaf_key::LeafKeyConfig, leaf_key_in_added_branch::LeafKeyInAddedBranchConfig,
    leaf_value::LeafValueConfig, StorageLeaf, StorageLeafCols,
};
use witness_row::{MptWitnessRow, MptWitnessRowType};

use param::HASH_WIDTH;
use selectors::SelectorsConfig;

use crate::{
    circuit,
    evm_circuit::util::rlc,
    mpt_circuit::helpers::{extend_rand, BranchNodeInfo, MPTConstraintBuilder},
    table::{DynamicTableColumns, KeccakTable},
    util::{power_of_randomness_from_instance, Challenges},
};

use self::{
    columns::MPTTable, param::BRANCH_ROWS_NUM,
    storage_leaf::leaf_non_existing::StorageNonExistingConfig,
};

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
#[derive(Clone, Debug, Default)]
pub struct RowConfig<F> {
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
}

/// Merkle Patricia Trie context
#[derive(Clone, Debug)]
pub struct MPTContext<F> {
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
    pub(crate) address_rlc: Column<Advice>,
    pub(crate) r: Vec<Expression<F>>,
}

impl<F: FieldExt> MPTContext<F> {
    pub(crate) fn main(&self, is_s: bool) -> MainCols<F> {
        if is_s {
            self.s_main
        } else {
            self.c_main
        }
    }

    pub(crate) fn inter_root(&self, is_s: bool) -> Column<Advice> {
        if is_s {
            self.inter_start_root
        } else {
            self.inter_final_root
        }
    }

    pub(crate) fn rlp_bytes(&self) -> Vec<Column<Advice>> {
        [self.s_main.rlp_bytes(), self.c_main.rlp_bytes()]
            .concat()
            .to_vec()
    }

    pub(crate) fn rlc(
        &self,
        meta: &mut VirtualCells<F>,
        range: Range<usize>,
        rot: i32,
    ) -> Expression<F> {
        rlc::expr(
            &self.rlp_bytes()[range]
                .iter()
                .map(|&byte| meta.query_advice(byte, Rotation(rot)))
                .collect::<Vec<_>>(),
            &self.r,
        )
    }

    pub(crate) fn rlc_chain(
        &self,
        meta: &mut VirtualCells<F>,
        range: Range<usize>,
        rot: i32,
        mult: Expression<F>,
    ) -> Expression<F> {
        rlc::expr(
            &self.rlp_bytes()[range]
                .iter()
                .map(|&byte| mult.expr() * meta.query_advice(byte, Rotation(rot)))
                .collect::<Vec<_>>(),
            &self.r,
        )
    }
}

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
    pub(crate) randomness: F,
    pub(crate) mpt_table: MPTTable,
}

/// Enumerator to determine the type of row in the fixed table.
#[derive(Clone, Copy, Debug)]
pub enum FixedTableTag {
    /// All zero lookup data
    Disabled,
    /// Power of randomness: [1, r], [2, r^2],...
    RMult,
    /// 0 - 15
    Range16,
    /// 0 - 255
    Range256,
    /// For checking there are 0s after the RLP stream ends
    RangeKeyLen256,
    /// For checking there are 0s after the RLP stream ends
    RangeKeyLen16,
}

impl_expr!(FixedTableTag);

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
    pub(crate) is_short_c1: bool,
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

        let ctx = MPTContext {
            proof_type: proof_type.clone(),
            position_cols: position_cols.clone(),
            inter_start_root: inter_start_root.clone(),
            inter_final_root: inter_final_root.clone(),
            value_prev: value_prev.clone(),
            value: value.clone(),
            branch: branch.clone(),
            s_main: s_main.clone(),
            c_main: c_main.clone(),
            account_leaf: account_leaf.clone(),
            storage_leaf: storage_leaf.clone(),
            accumulators: accumulators.clone(),
            denoter: denoter.clone(),
            address_rlc: address_rlc.clone(),
            r: extend_rand(&power_of_randomness),
        };

        let mut row_config: RowConfig<F> = RowConfig::default();

        let mut cb = MPTConstraintBuilder::new(17);
        meta.create_gate("MPT", |meta| {
            circuit!([meta, cb.base], {
                /* General */
                SelectorsConfig::configure(meta, &mut cb, ctx.clone());
                ProofChainConfig::configure(meta, &mut cb, ctx.clone());

                /* Branch node */
                let branch_config = BranchConfig::configure(meta, &mut cb, ctx.clone());
                // BRANCH.IS_INIT
                ifx!{f!(position_cols.q_enable), a!(branch.is_init) => {
                    BranchInitConfig::configure(meta, &mut cb, ctx.clone());
                }}
                // BRANCH.IS_CHILD
                ifx!{f!(position_cols.q_not_first), a!(branch.is_child) => {
                    BranchRLCConfig::configure(meta, &mut cb, ctx.clone(), true);
                    BranchRLCConfig::configure(meta, &mut cb, ctx.clone(), false);
                }}
                // - Last child
                ifx!{f!(position_cols.q_not_first), a!(branch.is_last_child) => {
                    BranchHashInParentConfig::configure(meta, &mut cb, ctx.clone(), true);
                    BranchHashInParentConfig::configure(meta, &mut cb, ctx.clone(), false);
                }}
                // BRANCH.IS_EXTENSION_NODE_S
                let ext_node_config_s;
                let is_extension_node = BranchNodeInfo::new(meta, s_main, true, -BRANCH_ROWS_NUM + 2).is_extension();
                let is_extension_node_s = a!(branch.is_extension_node_s);
                ifx!{f!(position_cols.q_not_first_ext_s), is_extension_node, is_extension_node_s => {
                    ext_node_config_s = ExtensionNodeConfig::configure(meta, &mut cb, ctx.clone(), true);
                }}
                // BRANCH.IS_EXTENSION_NODE_C
                let ext_node_config_c;
                let is_extension_node = BranchNodeInfo::new(meta, s_main, false, -BRANCH_ROWS_NUM + 1).is_extension();
                let is_extension_node_c = a!(branch.is_extension_node_c);
                ifx!{f!(position_cols.q_not_first_ext_c), is_extension_node, is_extension_node_c => {
                    ext_node_config_c = ExtensionNodeConfig::configure(meta, &mut cb, ctx.clone(), false);
                }}
                // BRANCH.IS_EXTENSION_NODE_S + BRANCH.IS_EXTENSION_NODE_C
                BranchKeyConfig::configure(meta, &mut cb, ctx.clone());

                /* Storage Leaf */
                // LEAF_KEY_S
                // LEAF_KEY_C
                let storage_leaf_key_s;
                let storage_leaf_key_c;
                ifx!{f!(position_cols.q_not_first), a!(position_cols.not_first_level) => {
                    ifx!{a!(storage_leaf.is_s_key) => {
                        storage_leaf_key_s = LeafKeyConfig::configure(meta, &mut cb, ctx.clone(), true);
                    }}
                    ifx!{a!(storage_leaf.is_c_key) => {
                        storage_leaf_key_c = LeafKeyConfig::configure(meta, &mut cb, ctx.clone(), false);
                    }}
                }}
                // LEAF_VALUE_S
                // LEAF_VALUE_C
                let storage_leaf_value_s;
                let storage_leaf_value_c;
                ifx!{f!(position_cols.q_not_first) => {
                    ifx!{a!(ctx.storage_leaf.is_s_value) => {
                        storage_leaf_value_s = LeafValueConfig::configure(meta, &mut cb, ctx.clone(), true);
                    }}
                    ifx!{a!(ctx.storage_leaf.is_c_value) => {
                        storage_leaf_value_c = LeafValueConfig::configure(meta, &mut cb, ctx.clone(), false);
                    }}
                }}
                // LEAF_DRIFTED
                let storage_leaf_key_in_added_branch;
                ifx!{f!(position_cols.q_not_first), a!(position_cols.not_first_level), a!(storage_leaf.is_in_added_branch) => {
                    storage_leaf_key_in_added_branch = LeafKeyInAddedBranchConfig::configure(meta, &mut cb, ctx.clone());
                }}
                // LEAF_NON_EXISTING
                let storage_non_existing;
                ifx!{f!(position_cols.q_enable), a!(storage_leaf.is_non_existing) => {
                    storage_non_existing = StorageNonExistingConfig::<F>::configure(meta, &mut cb, ctx.clone());
                }}

                /* Account Leaf */
                // ACCOUNT_LEAF_KEY_S
                // ACCOUNT_LEAF_KEY_C
                let account_leaf_key_s;
                let account_leaf_key_c;
                ifx!{f!(position_cols.q_enable) => {
                    ifx!{a!(account_leaf.is_key_s) => {
                        account_leaf_key_s = AccountLeafKeyConfig::configure(meta, &mut cb, ctx.clone(), true);
                    }}
                    ifx!{a!(account_leaf.is_key_c) => {
                        account_leaf_key_c = AccountLeafKeyConfig::configure(meta, &mut cb, ctx.clone(), false);
                    }}
                }}
                // ACCOUNT_NON_EXISTING
                let account_non_existing;
                ifx!{f!(position_cols.q_enable), a!(account_leaf.is_non_existing) => {
                    account_non_existing = AccountNonExistingConfig::configure(meta, &mut cb, ctx.clone());
                }}
                // ACCOUNT_LEAF_NONCE_BALANCE_S
                // ACCOUNT_LEAF_NONCE_BALANCE_C
                let account_leaf_nonce_balance_s;
                let account_leaf_nonce_balance_c;
                ifx!{f!(position_cols.q_not_first) => {
                    ifx!{a!(account_leaf.is_nonce_balance_s) => {
                        account_leaf_nonce_balance_s = AccountLeafNonceBalanceConfig::configure(meta, &mut cb, ctx.clone(), true);
                    }}
                    ifx!{a!(account_leaf.is_nonce_balance_c) => {
                        account_leaf_nonce_balance_c = AccountLeafNonceBalanceConfig::configure(meta, &mut cb, ctx.clone(), false);
                    }}
                }}
                // ACCOUNT_LEAF_STORAGE_CODEHASH_S
                // ACCOUNT_LEAF_STORAGE_CODEHASH_C
                let account_leaf_storage_codehash_s = AccountLeafStorageCodehashConfig::configure(meta, &mut cb, ctx.clone(), true);
                let account_leaf_storage_codehash_c = AccountLeafStorageCodehashConfig::configure(meta, &mut cb, ctx.clone(), false);
                // ACCOUNT_DRIFTED_LEAF
                let account_leaf_key_in_added_branch;
                ifx!{f!(position_cols.q_not_first), a!(position_cols.not_first_level), a!(account_leaf.is_in_added_branch) => {
                    account_leaf_key_in_added_branch = AccountLeafKeyInAddedBranchConfig::configure(meta, &mut cb, ctx.clone());
                }}

                /* Range checks */
                // These range checks ensure that the value in the RLP columns are all bytes
                // (between 0 - 255).
                // TODO(Brecht): would be safer/cleaner if this can be enabled everywhere even for branch child rlp1
                // TODO(Brecht): do 2 bytes/lookup when circuit height >= 2**21
                ifx!{f!(position_cols.q_enable) => {
                    // Sanity checks (can be removed, here for safety)
                    require!(cb.length_s.sum_conditions() => bool);
                    require!(cb.length_c.sum_conditions() => bool);
                    // Range checks
                    ifx!{not!(a!(branch.is_child)) => {
                        for &byte in ctx.rlp_bytes()[0..1].into_iter() {
                            require!((FixedTableTag::RangeKeyLen256, a!(byte), 0.expr()) => @"fixed");
                        }
                    }}
                    for &byte in ctx.rlp_bytes()[1..2].into_iter() {
                        require!((FixedTableTag::RangeKeyLen256, a!(byte), 0.expr()) => @"fixed");
                    }
                    for (idx, &byte) in ctx.rlp_bytes()[2..34].into_iter().enumerate() {
                        require!((cb.get_range_s(), a!(byte), cb.get_length_s() - (idx + 1).expr()) => @"fixed");
                    }
                    ifx!{cb.length_sc => {
                        ifx!{not!(a!(branch.is_child)) => {
                            for (idx, &byte) in ctx.rlp_bytes()[34..35].into_iter().enumerate() {
                                require!((FixedTableTag::RangeKeyLen256, a!(byte), cb.get_length_s() - 32.expr() - (idx + 1).expr()) => @"fixed");
                            }
                        }}
                        for (idx, &byte) in ctx.rlp_bytes()[35..36].into_iter().enumerate() {
                            require!((FixedTableTag::RangeKeyLen256, a!(byte), cb.get_length_s() - 32.expr() - (idx + 1).expr()) => @"fixed");
                        }
                    }}
                    for (idx, &byte) in ctx.rlp_bytes()[36..68].into_iter().enumerate() {
                        require!((FixedTableTag::RangeKeyLen256, a!(byte), cb.get_length_c() - (idx + 1).expr()) => @"fixed");
                    }
                }}

                /* Mult checks */
                for tag in ["mult", "mult2"] {
                    let lookups = cb.base.lookups.iter().cloned().filter(|lookup| lookup.tag == tag).collect::<Vec<_>>();
                    let optimize = true;
                    if optimize {
                        let selector = sum::expr(lookups.iter().map(|lookup| lookup.condition.expr()));
                        // Sanity checks (can be removed, here for safety)
                        require!(selector => bool);
                        // Merge
                        let max_length = lookups.iter().map(|lookup| lookup.values.len()).max().unwrap();
                        let mut values = vec![0.expr(); max_length];
                        for (idx, value) in values.iter_mut().enumerate() {
                            *value = sum::expr(
                                lookups
                                    .iter()
                                    .map(|lookup| lookup.condition.expr() * lookup.values[idx].expr()));
                        }
                        require!(values => @"fixed");
                    } else {
                        for lookup in lookups.iter() {
                            ifx!{lookup.condition => {
                                require!(lookup.description.to_string(), lookup.values => @"fixed");
                            }}
                        }
                    }
                }

                /* Populate lookup tables */
                require!(@"keccak" => keccak_table.columns().iter().map(|table| a!(table)).collect());
                require!(@"fixed" => fixed_table.iter().map(|table| f!(table)).collect());

                row_config = RowConfig {
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
                };
            });

            cb.base.generate_constraints()
        });

        let disable_lookups: usize = var("DISABLE_LOOKUPS")
            .unwrap_or_else(|_| "0".to_string())
            .parse()
            .expect("Cannot parse DISABLE_LOOKUPS env var as usize");
        if disable_lookups == 0 {
            cb.base.generate_lookups(meta, &["fixed", "keccak"]);
        }

        println!("num lookups: {}", meta.lookups().len());
        println!("num advices: {}", meta.num_advice_columns());
        println!("num fixed: {}", meta.num_fixed_columns());

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
            account_leaf_key_s: row_config.account_leaf_key_s,
            account_leaf_key_c: row_config.account_leaf_key_c,
            account_leaf_nonce_balance_s: row_config.account_leaf_nonce_balance_s,
            account_leaf_nonce_balance_c: row_config.account_leaf_nonce_balance_c,
            account_leaf_storage_codehash_s: row_config.account_leaf_storage_codehash_s,
            account_leaf_storage_codehash_c: row_config.account_leaf_storage_codehash_c,
            account_leaf_key_in_added_branch: row_config.account_leaf_key_in_added_branch,
            account_non_existing: row_config.account_non_existing,
            branch_config: row_config.branch_config,
            ext_node_config_s: row_config.ext_node_config_s,
            ext_node_config_c: row_config.ext_node_config_c,
            storage_leaf_key_s: row_config.storage_leaf_key_s,
            storage_leaf_key_c: row_config.storage_leaf_key_c,
            storage_leaf_value_s: row_config.storage_leaf_value_s,
            storage_leaf_value_c: row_config.storage_leaf_value_c,
            storage_leaf_key_in_added_branch: row_config.storage_leaf_key_in_added_branch,
            storage_non_existing: row_config.storage_non_existing,
            randomness,
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

                        //println!("{} -> {:?}", offset, row.get_type());

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

                        let q_not_first_ext_s = if offset < (BRANCH_ROWS_NUM as usize) - 1 {
                            F::zero()
                        } else {
                            F::one()
                        };
                        region.assign_fixed(
                            || "not first ext s",
                            self.position_cols.q_not_first_ext_s,
                            offset,
                            || Value::known(q_not_first_ext_s),
                        )?;

                        let q_not_first_ext_c = if offset < (BRANCH_ROWS_NUM as usize) - 0 {
                            F::zero()
                        } else {
                            F::one()
                        };
                        region.assign_fixed(
                            || "not first ext c",
                            self.position_cols.q_not_first_ext_c,
                            offset,
                            || Value::known(q_not_first_ext_c),
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

                // Zero lookup
                for fixed_table in self.fixed_table.iter() {
                    region.assign_fixed(
                        || "fixed table zero",
                        *fixed_table,
                        offset,
                        || Value::known(F::zero()),
                    )?;
                }
                offset += 1;

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

                let max_length = 34i32 + 1;
                for (tag, range) in [
                    (FixedTableTag::RangeKeyLen256, 256),
                    (FixedTableTag::RangeKeyLen16, 16),
                ] {
                    for n in /* -192-max_length */ -512..max_length {
                        let range = if n < 0 { 1 } else { range };
                        for idx in 0..range {
                            region.assign_fixed(
                                || "fixed table[0]",
                                self.fixed_table[0],
                                offset,
                                || Value::known(F::from(tag as u64)),
                            )?;

                            region.assign_fixed(
                                || "fixed table[1]",
                                self.fixed_table[1],
                                offset,
                                || Value::known(F::from(idx as u64)),
                            )?;

                            let v = F::from(n.unsigned_abs() as u64)
                                * if n.is_negative() { -F::one() } else { F::one() };
                            region.assign_fixed(
                                || "fixed table[2]",
                                self.fixed_table[2],
                                offset,
                                || Value::known(v),
                            )?;

                            offset += 1;
                        }
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
        MPTConfig::configure(meta, power_of_randomness, keccak_table)
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
            .enumerate()
            .for_each(|(idx, f)| {
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
                    witness: w.clone(),
                    randomness,
                };

                println!("{} {:?}", idx, path);
                // let prover = MockProver::run(9, &circuit, vec![pub_root]).unwrap();
                let num_rows = w.len();
                let prover = MockProver::run(14 /* 9 */, &circuit, instance).unwrap();
                assert_eq!(prover.verify_at_rows(0..num_rows, 0..num_rows,), Ok(()));
                //assert_eq!(prover.verify_par(), Ok(()));
                //prover.assert_satisfied();
            });
    }
}
