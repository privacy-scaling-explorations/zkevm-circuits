use halo2_proofs::{
    circuit::{Layouter, Region},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed},
    poly::Rotation,
};
use keccak256::plain::Keccak;
use pairing::arithmetic::FieldExt;

use std::convert::{TryInto};

use crate::{
    branch::{BranchConfig, branch_hash_in_parent::BranchHashInParentConfig, branch_parallel::BranchParallelChip, branch_key::BranchKeyConfig, branch_rlc::BranchRLCConfig, branch_init::BranchInitConfig, extension_node::ExtensionNodeChip, extension_node_key::ExtensionNodeKeyChip, Branch, BranchCols},
    helpers::{get_is_extension_node, bytes_into_rlc},
    param::{
        RLP_NUM,
    },
    roots::RootsChip,
    storage_root_in_account_leaf::StorageRootChip, account_leaf::{AccountLeafCols, AccountLeaf, account_leaf_key_in_added_branch::AccountLeafKeyInAddedBranchConfig, account_leaf_key::AccountLeafKeyConfig, account_leaf_nonce_balance::AccountLeafNonceBalanceConfig, account_leaf_storage_codehash::AccountLeafStorageCodehashConfig, account_non_existing::AccountNonExistingConfig}, storage_leaf::{StorageLeafCols, StorageLeaf, leaf_key_in_added_branch::LeafKeyInAddedBranchChip, leaf_key::LeafKeyChip, leaf_value::LeafValueChip}, witness_row::{MptWitnessRow, MptWitnessRowType}, columns::{ProofTypeCols, MainCols, AccumulatorCols, DenoteCols},
};
use crate::{
    param::{
        C_RLP_START, C_START,
        HASH_WIDTH, IS_BRANCH_C_PLACEHOLDER_POS, IS_BRANCH_S_PLACEHOLDER_POS, KECCAK_INPUT_WIDTH,
        KECCAK_OUTPUT_WIDTH, S_START,
    },
    selectors::SelectorsChip,
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

#[derive(Clone, Debug)]
pub struct MPTConfig<F> {
    pub(crate) proof_type: ProofTypeCols<F>,
    pub(crate) q_enable: Column<Fixed>,
    pub(crate) q_not_first: Column<Fixed>, // not first row
    pub(crate) not_first_level: Column<Advice>,
    pub(crate) inter_start_root: Column<Advice>,
    pub(crate) inter_final_root: Column<Advice>,
    pub(crate) accumulators: AccumulatorCols<F>,
    pub(crate) branch: BranchCols<F>,
    pub(crate) s_main: MainCols<F>,
    pub(crate) c_main: MainCols<F>,
    pub(crate) account_leaf: AccountLeafCols<F>,
    pub(crate) storage_leaf: StorageLeafCols<F>,
    pub(crate) denoter: DenoteCols<F>,
    pub(crate) acc_r: F,
    r_table: Vec<Expression<F>>,
    keccak_table: [Column<Fixed>; KECCAK_INPUT_WIDTH + KECCAK_OUTPUT_WIDTH],
    fixed_table: [Column<Fixed>; 3],
    pub(crate) address_rlc: Column<Advice>, /* The same in all rows of a modification. The same as
                                  * address_rlc computed in the account leaf key row. Needed to
                                  * enable lookup for storage key/value (to have address RLC in
                                  * the same row as storage key/value). */
    pub(crate) counter: Column<Advice>,
    account_leaf_key_s: AccountLeafKeyConfig<F>,
    account_leaf_key_c: AccountLeafKeyConfig<F>,
    account_leaf_nonce_balance_s: AccountLeafNonceBalanceConfig<F>,
    account_leaf_nonce_balance_c: AccountLeafNonceBalanceConfig<F>,
    account_leaf_storage_codehash_s: AccountLeafStorageCodehashConfig<F>,
    account_leaf_storage_codehash_c: AccountLeafStorageCodehashConfig<F>,
    account_leaf_key_in_added_branch: AccountLeafKeyInAddedBranchConfig<F>,
    account_non_existing: AccountNonExistingConfig<F>,
    branch_config: BranchConfig<F>,
}

#[derive(Clone, Copy, Debug)]
pub enum FixedTableTag {
    RMult,
    Range16,
    Range256,
    RangeKeyLen256,
}

#[derive(Default)]
/*
Some values are accumulating through the rows (or block of rows) and we need to access the previous value
to continue the calculation, for this reason the previous values are stored in ProofVariables struct.
Such accumulated value is for example key_rlc which stores the intermediate key RLC (in each branch
and extension node block a new intermediate key RLC is computed).
Also, for example, modified_node is given in branch init but needed to be set in every branch children row.
*/
pub(crate) struct ProofVariables<F> {
    pub(crate) modified_node: u8, // branch child that is being changed, it is the same in all branch children rows
    pub(crate) s_mod_node_hash_rlc: F, // hash rlc of the modified_node for S proof, it is the same in all branch children rows
    pub(crate) c_mod_node_hash_rlc: F, // hash rlc of the modified_node for C proof, it is the same in all branch children rows
    pub(crate) node_index: u8, // branch child index
    pub(crate) acc_s: F, // RLC accumulator for the whole node (taking into account all RLP bytes of the node)
    pub(crate) acc_mult_s: F, // multiplier for acc_s
    pub(crate) acc_account_s: F,
    pub(crate) acc_mult_account_s: F,
    pub(crate) acc_account_c: F,
    pub(crate) acc_mult_account_c: F,
    pub(crate) acc_nonce_balance_s: F,
    pub(crate) acc_mult_nonce_balance_s: F,
    pub(crate) acc_nonce_balance_c: F,
    pub(crate) acc_mult_nonce_balance_c: F,
    pub(crate) acc_c: F, // RLC accumulator for the whole node (taking into account all RLP bytes of the node)
    pub(crate) acc_mult_c: F, // multiplier for acc_c
    pub(crate) key_rlc: F, /* used first for account address, then for storage key */
    pub(crate) key_rlc_mult: F, // multiplier for key_rlc
    pub(crate) extension_node_rlc: F, // RLC accumulator for extension node
    pub(crate) key_rlc_prev: F, /* for leaf after placeholder extension/branch, we need to go one level
                      * back to get previous key_rlc */
    pub(crate) key_rlc_mult_prev: F,
    pub(crate) mult_diff: F, // power of randomness r: multiplier_curr = multiplier_prev * mult_diff
    pub(crate) key_rlc_sel: bool, /* If true, nibble is multiplied by 16, otherwise by 1. */
    pub(crate) is_branch_s_placeholder: bool, // whether S branch is just a placeholder
    pub(crate) is_branch_c_placeholder: bool, // whether C branch is just a placeholder
    pub(crate) drifted_pos: u8, /* needed when leaf turned into branch and leaf moves into a branch where
                      * it's at drifted_pos position */
    pub(crate) rlp_len_rem_s: i32, /* branch RLP length remainder, in each branch children row this value
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

impl<F: FieldExt> ProofVariables<F> {
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
    pub(crate) fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let pub_root = meta.instance_column();
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

        let q_enable = meta.fixed_column();
        let q_not_first = meta.fixed_column();
        let not_first_level = meta.advice_column();

        // having 2 to enable key RLC check (not using 1 to enable proper checks of mult
        // too) TODO: generate from commitments
        let acc_r = F::one() + F::one(); // Note: it needs to be set to the same value in test

        let one = Expression::Constant(F::one());
        let mut r_table = vec![];
        let mut r = one.clone();
        for _ in 0..HASH_WIDTH {
            r = r * acc_r;
            r_table.push(r.clone());
        }

        // TODO: r_table constraints

        // TODO: in many cases different rotations can be used - for example, when
        // getting back into s_mod_node_hash_rlc or c_mod_node_hash_rlc to get
        // the hash (all 16 branch children contain the same hash in
        // s_mod_node_hash_rlc and c_mod_node_hash_rlc), so we can choose the
        // rotations smartly to have at least as possible of them

        let proof_type = ProofTypeCols::new(meta);
        let account_leaf = AccountLeafCols::new(meta);
        let storage_leaf = StorageLeafCols::new(meta);
        let branch = BranchCols::new(meta);
            
        let s_main = MainCols::new(meta);
        let c_main = MainCols::new(meta);

        let keccak_table: [Column<Fixed>; KECCAK_INPUT_WIDTH + KECCAK_OUTPUT_WIDTH] = (0
            ..KECCAK_INPUT_WIDTH + KECCAK_OUTPUT_WIDTH)
            .map(|_| meta.fixed_column())
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let fixed_table: [Column<Fixed>; 3] = (0..3)
            .map(|_| meta.fixed_column())
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        // NOTE: key_rlc_mult wouldn't be needed if we would have
        // big endian instead of little endian. However, then it would be much more
        // difficult to handle the accumulator when we iterate over the key.
        // At some point (but we don't know this point at compile time), key ends
        // and from there on the values in the row need to be 0s.
        // However, if we are computing rlc using little endian:
        // rlc = rlc + row[i] * acc_r,
        // rlc will stay the same once r[i] = 0.
        // If big endian would be used:
        // rlc = rlc * acc_r + row[i],
        // the rlc would be multiplied by acc_r when row[i] = 0.

        let accumulators = AccumulatorCols::new(meta);

        // NOTE: acc_s.mult and acc_c.mult wouldn't be needed if we would have
        // big endian instead of little endian. However, then it would be much more
        // difficult to handle the accumulator when we iterate over the row.
        // For example, big endian would mean to compute acc = acc * mult_r + row[i],
        // but we don't want acc to be multiplied by mult_r when row[i] = 0 where
        // the stream already ended and 0s are only to fulfill the row.

        let denoter = DenoteCols::new(meta);
 
        let address_rlc = meta.advice_column();
        let counter = meta.advice_column();

        SelectorsChip::<F>::configure(
            meta,
            proof_type.clone(),
            q_enable,
            q_not_first,
            not_first_level,
            branch.clone(),
            account_leaf.clone(),
            storage_leaf.clone(),
            denoter.clone(),
        );

        RootsChip::<F>::configure(
            meta,
            q_enable,
            q_not_first,
            not_first_level,
            branch.is_init,
            account_leaf.is_key_s,
            storage_leaf.clone(),
            inter_start_root,
            inter_final_root,
            address_rlc,
            counter,
        );

        let branch_config = BranchConfig::<F>::configure(
            meta,
            q_enable,
            q_not_first,
            not_first_level,
            account_leaf.is_in_added_branch,
            s_main.clone(),
            c_main.clone(),
            accumulators.clone(),
            branch.clone(),
            denoter.clone(),
            fixed_table.clone(),
            acc_r,
        );

        BranchKeyConfig::<F>::configure(
            meta,
            q_not_first,
            not_first_level,
            branch.clone(),
            account_leaf.is_in_added_branch,
            s_main.clone(),
            accumulators.key.clone(),
            acc_r,
        );

        BranchParallelChip::<F>::configure(
            meta,
            q_enable,
            q_not_first,
            branch.clone(),
            accumulators.clone(),
            s_main.clone(),
            denoter.sel1,
            denoter.is_node_hashed_s,
            true,
        );

        BranchParallelChip::<F>::configure(
            meta,
            q_enable,
            q_not_first,
            branch.clone(),
            accumulators.clone(),
            c_main.clone(),
            denoter.sel2,
            denoter.is_node_hashed_c,
            false,
        );

        BranchHashInParentConfig::<F>::configure(
            meta,
            inter_start_root,
            not_first_level,
            q_not_first,
            account_leaf.is_in_added_branch,
            branch.is_last_child,
            s_main.clone(),
            accumulators.s_mod_node_rlc,
            accumulators.acc_s.clone(),
            keccak_table,
            true,
        );

        BranchHashInParentConfig::<F>::configure(
            meta,
            inter_final_root,
            not_first_level,
            q_not_first,
            account_leaf.is_in_added_branch,
            branch.is_last_child,
            s_main.clone(),
            accumulators.c_mod_node_rlc,
            accumulators.acc_c.clone(),
            keccak_table,
            false,
        );

        ExtensionNodeChip::<F>::configure(
            meta,
            |meta| {
                let is_extension_node_s = meta.query_advice(branch.is_extension_node_s, Rotation::cur());
                // is_extension_node is in branch init row
                let is_extension_node = get_is_extension_node(meta, s_main.bytes, -17);

                is_extension_node_s * is_extension_node
            },
            inter_start_root,
            not_first_level,
            q_not_first,
            account_leaf.is_in_added_branch,
            branch.is_init,
            s_main.clone(),
            c_main.clone(),
            accumulators.clone(),
            keccak_table,
            r_table.clone(),
            true,
            acc_r,
        );

        ExtensionNodeChip::<F>::configure(
            meta,
            |meta| {
                let is_extension_node_c = meta.query_advice(branch.is_extension_node_c, Rotation::cur());
                // is_extension_node is in branch init row
                let is_extension_node = get_is_extension_node(meta, s_main.bytes, -18);

                is_extension_node_c * is_extension_node
            },
            inter_final_root,
            not_first_level,
            q_not_first,
            account_leaf.is_in_added_branch,
            branch.is_init,
            s_main.clone(),
            c_main.clone(),
            accumulators.clone(),
            keccak_table,
            r_table.clone(),
            false,
            acc_r,
        );

        ExtensionNodeKeyChip::<F>::configure(
            meta,
            q_not_first,
            not_first_level,
            branch.clone(),
            account_leaf.is_in_added_branch,
            s_main.clone(),
            c_main.clone(),
            accumulators.clone(),
            fixed_table.clone(),
            r_table.clone(),
        );

        StorageRootChip::<F>::configure(
            meta,
            q_enable,
            not_first_level,
            account_leaf.is_in_added_branch,
            storage_leaf.clone(),
            branch.is_last_child,
            s_main.clone(),
            accumulators.clone(),
            denoter.sel1,
            keccak_table,
            acc_r,
            true,
        );

        StorageRootChip::<F>::configure(
            meta,
            q_enable,
            not_first_level,
            account_leaf.is_in_added_branch,
            storage_leaf.clone(),
            branch.is_last_child,
            s_main.clone(), // s_main (and not c_main) is correct
            accumulators.clone(),
            denoter.sel2,
            keccak_table,
            acc_r,
            false,
        );

        BranchInitConfig::<F>::configure(
            meta,
            |meta| {
                meta.query_advice(branch.is_init, Rotation::cur())
                    * meta.query_fixed(q_enable, Rotation::cur())
            },
            s_main.clone(),
            accumulators.clone(),
            acc_r,
        );

        BranchRLCConfig::<F>::configure(
            meta,
            |meta| {
                let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
                let is_branch_child = meta.query_advice(branch.is_child, Rotation::cur());

                q_not_first * is_branch_child
            },
            s_main.clone(),
            accumulators.acc_s.clone(),
            denoter.is_node_hashed_s,
            accumulators.node_mult_diff_s,
            r_table.clone(),
            fixed_table,
        );

        BranchRLCConfig::<F>::configure(
            meta,
            |meta| {
                let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
                let is_branch_child = meta.query_advice(branch.is_child, Rotation::cur());

                q_not_first * is_branch_child
            },
            c_main.clone(),
            accumulators.acc_c.clone(),
            denoter.is_node_hashed_c,
            accumulators.node_mult_diff_c,
            r_table.clone(),
            fixed_table,
        );

        LeafKeyChip::<F>::configure(
            meta,
            |meta| {
                let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
                let not_first_level = meta.query_advice(not_first_level, Rotation::cur());
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
            denoter.clone(),
            account_leaf.is_in_added_branch,
            r_table.clone(),
            fixed_table.clone(),
            true,
        );

        LeafKeyChip::<F>::configure(
            meta,
            |meta| {
                let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
                let not_first_level = meta.query_advice(not_first_level, Rotation::cur());
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
            denoter.clone(),
            account_leaf.is_in_added_branch,
            r_table.clone(),
            fixed_table.clone(),
            false,
        );

        LeafKeyInAddedBranchChip::<F>::configure(
            meta,
            |meta| {
                let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
                let not_first_level = meta.query_advice(not_first_level, Rotation::cur());
                let is_leaf = meta.query_advice(storage_leaf.is_in_added_branch, Rotation::cur());

                q_not_first * not_first_level * is_leaf
            },
            s_main.clone(),
            c_main.clone(),
            accumulators.clone(),
            branch.drifted_pos,
            account_leaf.is_in_added_branch,
            r_table.clone(),
            fixed_table.clone(),
            keccak_table.clone(),
        );

        LeafValueChip::<F>::configure(
            meta,
            inter_start_root,
            q_not_first,
            not_first_level,
            storage_leaf.is_s_value,
            s_main.clone(),
            keccak_table,
            accumulators.clone(),
            denoter.clone(),
            account_leaf.is_in_added_branch,
            s_main.bytes[IS_BRANCH_S_PLACEHOLDER_POS - RLP_NUM],
            true,
            acc_r,
            fixed_table.clone(),
        );

        LeafValueChip::<F>::configure(
            meta,
            inter_final_root,
            q_not_first,
            not_first_level,
            storage_leaf.is_c_value,
            s_main.clone(),
            keccak_table,
            accumulators.clone(),
            denoter.clone(),
            account_leaf.is_in_added_branch,
            s_main.bytes[IS_BRANCH_C_PLACEHOLDER_POS - RLP_NUM],
            false,
            acc_r,
            fixed_table.clone(),
        );

        let account_leaf_key_s = AccountLeafKeyConfig::<F>::configure(
            meta,
            proof_type.clone(),
            |meta| {
                let q_enable = meta.query_fixed(q_enable, Rotation::cur());
                let is_account_leaf_key_s =
                    meta.query_advice(account_leaf.is_key_s, Rotation::cur());

                q_enable * is_account_leaf_key_s
            },
            not_first_level,
            s_main.clone(),
            c_main.clone(),
            accumulators.clone(),
            r_table.clone(),
            fixed_table.clone(),
            address_rlc,
            denoter.sel2,
            true,
        );

        let account_leaf_key_c = AccountLeafKeyConfig::<F>::configure(
            meta,
            proof_type.clone(),
            |meta| {
                let q_enable = meta.query_fixed(q_enable, Rotation::cur());
                let is_account_leaf_key_c =
                    meta.query_advice(account_leaf.is_key_c, Rotation::cur());

                q_enable * is_account_leaf_key_c
            },
            not_first_level,
            s_main.clone(),
            c_main.clone(),
            accumulators.clone(),
            r_table.clone(),
            fixed_table.clone(),
            address_rlc,
            denoter.sel2,
            false,
        );

        let account_non_existing = AccountNonExistingConfig::<F>::configure(
            meta,
            |meta| {
                let q_enable = meta.query_fixed(q_enable, Rotation::cur());
                let is_account_non_existing_row =
                    meta.query_advice(account_leaf.is_non_existing_account_row, Rotation::cur());
                let is_account_non_existing_proof =
                    meta.query_advice(proof_type.is_non_existing_account_proof, Rotation::cur());

                q_enable * is_account_non_existing_row * is_account_non_existing_proof
            },
            not_first_level,
            s_main.clone(),
            c_main.clone(),
            accumulators.clone(),
            denoter.sel1,
            r_table.clone(),
            fixed_table.clone(),
            address_rlc,
        );

        let account_leaf_nonce_balance_s = AccountLeafNonceBalanceConfig::<F>::configure(
            meta,
            proof_type.clone(),
            |meta| {
                let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
                let is_account_leaf_nonce_balance_s =
                    meta.query_advice(account_leaf.is_nonce_balance_s, Rotation::cur());
                q_not_first * is_account_leaf_nonce_balance_s
            },
            s_main.clone(),
            c_main.clone(),
            accumulators.clone(),
            r_table.clone(),
            denoter.clone(),
            fixed_table.clone(),
            true,
        );

        let account_leaf_nonce_balance_c = AccountLeafNonceBalanceConfig::<F>::configure(
            meta,
            proof_type.clone(),
            |meta| {
                let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
                let is_account_leaf_nonce_balance_c =
                    meta.query_advice(account_leaf.is_nonce_balance_c, Rotation::cur());
                q_not_first * is_account_leaf_nonce_balance_c
            },
            s_main.clone(),
            c_main.clone(),
            accumulators.clone(),
            r_table.clone(),
            denoter.clone(),
            fixed_table.clone(),
            false,
        );

        let account_leaf_storage_codehash_s = AccountLeafStorageCodehashConfig::<F>::configure(
            meta,
            proof_type.clone(),
            inter_start_root,
            q_not_first,
            not_first_level,
            account_leaf.is_storage_codehash_s,
            s_main.clone(),
            c_main.clone(),
            acc_r,
            accumulators.clone(),
            fixed_table.clone(),
            denoter.clone(),
            keccak_table,
            true,
        );

        let account_leaf_storage_codehash_c = AccountLeafStorageCodehashConfig::<F>::configure(
            meta,
            proof_type.clone(),
            inter_final_root,
            q_not_first,
            not_first_level,
            account_leaf.is_storage_codehash_c,
            s_main.clone(),
            c_main.clone(),
            acc_r,
            accumulators.clone(),
            fixed_table.clone(),
            denoter.clone(),
            keccak_table,
            false,
        );

        let account_leaf_key_in_added_branch = AccountLeafKeyInAddedBranchConfig::<F>::configure(
            meta,
            |meta| {
                let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
                let not_first_level = meta.query_advice(not_first_level, Rotation::cur());
                let is_account_leaf_in_added_branch =
                    meta.query_advice(account_leaf.is_in_added_branch, Rotation::cur());

                q_not_first * not_first_level * is_account_leaf_in_added_branch
            },
            not_first_level,
            s_main.clone(),
            c_main.clone(),
            accumulators.clone(),
            branch.drifted_pos,
            denoter.clone(),
            r_table.clone(),
            fixed_table.clone(),
            keccak_table.clone(),
        );

        MPTConfig {
            proof_type,
            q_enable,
            q_not_first,
            not_first_level,
            inter_start_root,
            inter_final_root,
            branch,
            s_main,
            c_main,
            account_leaf,
            storage_leaf,
            accumulators,
            acc_r,
            denoter,
            r_table,
            keccak_table,
            fixed_table,
            address_rlc,
            counter,
            account_leaf_key_s,
            account_leaf_key_c,
            account_leaf_nonce_balance_s,
            account_leaf_nonce_balance_c,
            account_leaf_storage_codehash_s,
            account_leaf_storage_codehash_c,
            account_leaf_key_in_added_branch,
            account_non_existing,
            branch_config,
        }
    } 
 
    pub(crate) fn compute_key_rlc(
        &self,
        row: &Vec<u8>, key_rlc: &mut F, key_rlc_mult: &mut F, start: usize) {
        let even_num_of_nibbles = row[start + 1] == 32;
        // If odd number of nibbles, we have nibble+48 in s_advices[0].
        if !even_num_of_nibbles {
            *key_rlc +=
                F::from((row[start + 1] - 48) as u64) * *key_rlc_mult;
            *key_rlc_mult *= self.acc_r;

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
        row: &Vec<u8>, acc: &mut F, mult: &mut F, start: usize, len: usize) {
        for i in 0..len {
            *acc += F::from(row[start + i] as u64) * *mult;
            *mult *= self.acc_r;
        }
    }

    pub(crate) fn compute_rlc_and_assign(
        &self,
        region: &mut Region<'_, F>,
        row: &Vec<u8>,
        pv: &mut ProofVariables<F>,
        offset: usize,
        s_start: usize, c_start: usize, len_s: usize, len_c: usize) -> Result<(), Error> {
        self.compute_acc_and_mult(
            row,
            &mut pv.rlc1,
            &mut F::one(),
            s_start,
            len_s,
        );
        region.assign_advice(
            || "assign s_mod_node_hash_rlc".to_string(),
            self.accumulators.s_mod_node_rlc,
            offset,
            || Ok(pv.rlc1),
        )?;

        self.compute_acc_and_mult(
            row,
            &mut pv.rlc2,
            &mut F::one(),
            c_start,
            len_c,
        );
        region.assign_advice(
            || "assign c_mod_node_hash_rlc".to_string(),
            self.accumulators.c_mod_node_rlc,
            offset,
            || Ok(pv.rlc2),
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
            || Ok(acc_s),
        )?;

        region.assign_advice(
            || "assign acc_mult_s".to_string(),
            self.accumulators.acc_s.mult,
            offset,
            || Ok(acc_mult_s),
        )?;

        region.assign_advice(
            || "assign acc_c".to_string(),
            self.accumulators.acc_c.rlc,
            offset,
            || Ok(acc_c),
        )?;

        region.assign_advice(
            || "assign acc_mult_c".to_string(),
            self.accumulators.acc_c.mult,
            offset,
            || Ok(acc_mult_c),
        )?;

        Ok(())
    }

    // TODO: split assign
    pub(crate) fn assign(&self, mut layouter: impl Layouter<F>, witness: &[MptWitnessRow<F>]) {
        layouter
            .assign_region(
                || "MPT",
                |mut region| {
                    let mut offset = 0;
                    let mut pv = ProofVariables::new();

                    // filter out rows that are just to be hashed
                    for (ind, row) in witness.iter().filter(|r| r.get_type() != MptWitnessRowType::HashToBeComputed).enumerate() {
                        if offset > 0 {
                            let row_prev = &witness[offset - 1];
                            let not_first_level_prev = row_prev.not_first_level();
                            let not_first_level_cur = row.not_first_level();
                            if not_first_level_cur == 0 && not_first_level_prev == 1 {
                                pv = ProofVariables::new();
                            }
                        }

                        region.assign_fixed(
                            || "q_enable",
                            self.q_enable,
                            offset,
                            || Ok(F::one()),
                        )?;

                        if row.get_type() == MptWitnessRowType::AccountLeafKeyS {
                            // account leaf key
                            pv.before_account_leaf = false;
                        }

                        let q_not_first = if ind == 0 { F::zero() } else { F::one() };
                         region.assign_fixed(
                             || "not first",
                             self.q_not_first,
                             offset,
                             || Ok(q_not_first),
                         )?;

                        region.assign_advice(
                            || "not first level",
                            self.not_first_level,
                            offset,
                            || Ok(F::from(row.not_first_level() as u64)),
                        )?; 

                        row.assign_lookup_columns(&mut region, self, &pv, offset)?;

                        if row.get_type() == MptWitnessRowType::InitBranch {
                            self.branch_config.assign_branch_init(
                                &mut region,
                                witness,
                                self,
                                &mut pv,
                                offset,
                            ).ok();
                            
                            offset += 1;
                        } else if row.get_type() == MptWitnessRowType::BranchChild {
                            self.branch_config.assign_branch_child(
                                &mut region,
                                witness,
                                self,
                                &mut pv,
                                offset,
                            ).ok();

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
                            } else if row.get_type() == MptWitnessRowType::AccountLeafNonceBalanceS {
                                account_leaf.is_nonce_balance_s = true;
                            } else if row.get_type() == MptWitnessRowType::AccountLeafNonceBalanceC {
                                account_leaf.is_nonce_balance_c = true;
                            } else if row.get_type() == MptWitnessRowType::AccountLeafRootCodehashS {
                                account_leaf.is_storage_codehash_s = true;
                            } else if row.get_type() == MptWitnessRowType::AccountLeafRootCodehashC {
                                account_leaf.is_storage_codehash_c = true;
                            } else if row.get_type() == MptWitnessRowType::AccountLeafNeighbouringLeaf {
                                account_leaf.is_in_added_branch = true;
                                pv.key_rlc = F::zero(); // account address until here, storage key from here on
                                pv.key_rlc_mult = F::one();
                                pv.key_rlc_prev = F::zero();
                                pv.key_rlc_mult_prev = F::one();
                                pv.key_rlc_sel = true;
                                pv.nibbles_num = 0;
                                // TODO: check whether all constraints are implemented (extension_node_rlc ...)
                            } else if row.get_type() == MptWitnessRowType::StorageLeafSValue {
                                storage_leaf.is_s_value = true;
                            } else if row.get_type() == MptWitnessRowType::StorageLeafCValue {
                                storage_leaf.is_c_value = true;
                            } else if row.get_type() == MptWitnessRowType::NeighbouringStorageLeaf {
                                storage_leaf.is_in_added_branch = true;
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

                            /*
                            assign_long_short is used for setting flags for storage leaf and storage value.
                            For storage leaf, it sets whether it is short (one RLP byte) or long (two RLP bytes)
                            or last level (no nibbles in leaf, all nibbles in the path above the leaf) or one nibble.
                            Note that last_level and one_nibble imply having only one RLP byte.

                            For storage value, it sets whether it is short or long (value having more than one byte).
                            */
                            let assign_long_short = |region: &mut Region<'_, F>, typ: &str| {
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
                                        || Ok(F::from(flag1 as u64)),
                                    )
                                    .ok();
                                region
                                    .assign_advice(
                                        || "assign c_modified_node_rlc".to_string(),
                                        self.accumulators.c_mod_node_rlc,
                                        offset,
                                        || Ok(F::from(flag2 as u64)),
                                    )
                                    .ok();
                            };

                            // Storage leaf key
                            if row.get_type() == MptWitnessRowType::StorageLeafSKey ||
                                row.get_type() == MptWitnessRowType::StorageLeafCKey {
                                /*
                                getProof storage leaf examples:
                                  short (one RLP byte > 128: 160):
                                  [226,160,59,138,106,70,105,186,37,13,38,205,122,69,158,202,157,33,95,131,7,227,58,235,229,3,121,188,90,54,23,236,52,68,1]

                                  long (two RLP bytes: 67, 160):
                                  [248,67,160,59,138,106,70,105,186,37,13,38,205,122,69,158,202,157,33,95,131,7,227,58,235,229,3,121,188,90,54,23,236,52,68,161,160,187,239,170,18,88,1,56,188,38,60,149,117,120,38,223,78,36,235,129,201,170,170,170,170,170,17

                                  last_level (one RLP byte: 32)
                                  32 at position 1 means there are no key nibbles (last level):
                                  [227,32,161,160,187,239,170,18,88,1,56,188,38,60,149,117,120,38,223,78,36,235,129,201,170,170,170,170,170,170,170,170,170,170,170,170]
                                  [194,32,1]

                                  this one falls into short again:
                                  [196,130,32,0,1]
                                */

                                // Info whether leaf rlp is long or short.
                                // Long means the key length is at position 2.
                                // Short means the key length is at position 1.
                                let mut typ = "short";
                                if row.get_byte(0) == 248 {
                                    typ = "long";
                                } else if row.get_byte(1) == 32 {
                                    typ = "last_level";
                                } else if row.get_byte(1) < 128 {
                                    typ = "one_nibble";
                                }
                                assign_long_short(&mut region, typ);

                                pv.acc_s = F::zero();
                                pv.acc_mult_s = F::one();
                                let len: usize;
                                if typ == "long" {
                                    len = (row.get_byte(2) - 128) as usize + 3;
                                } else if typ == "short" {
                                    len = (row.get_byte(1) - 128) as usize + 2;
                                } else {
                                    // last_level or one_nibble
                                    len = 2
                                }
                                self.compute_acc_and_mult(
                                    &row.bytes,
                                    &mut pv.acc_s,
                                    &mut pv.acc_mult_s,
                                    0,
                                    len,
                                );

                                self.assign_acc(
                                    &mut region,
                                    pv.acc_s,
                                    pv.acc_mult_s,
                                    F::zero(),
                                    F::zero(),
                                    offset,
                                )?;

                                // note that this assignment needs to be after assign_acc call
                                if row.get_byte(0) < 223 { // when shorter than 32 bytes, the node doesn't get hashed
                                    // not_hashed
                                    region.assign_advice(
                                        || "assign not_hashed".to_string(),
                                        self.accumulators.acc_c.rlc,
                                        offset,
                                        || Ok(F::one()),
                                    )?;
                                }

                                // TODO: handle if branch or extension node is added
                                let mut start = S_START - 1;
                                if row.get_byte(0) == 248 {
                                    // long RLP
                                    start = S_START;
                                }

                                // For leaf S and leaf C we need to start with the same rlc.
                                let mut key_rlc_new = pv.key_rlc;
                                let mut key_rlc_mult_new = pv.key_rlc_mult;
                                if (pv.is_branch_s_placeholder && row.get_type() == MptWitnessRowType::StorageLeafSKey)
                                    || (pv.is_branch_c_placeholder && row.get_type() == MptWitnessRowType::StorageLeafCKey)
                                {
                                    key_rlc_new = pv.key_rlc_prev;
                                    key_rlc_mult_new = pv.key_rlc_mult_prev;
                                }
                                if typ != "last_level" && typ != "one_nibble" {
                                    // If in last level or having only one nibble,
                                    // the key RLC is already computed using the first two bytes above.
                                    self.compute_key_rlc(&row.bytes, &mut key_rlc_new, &mut key_rlc_mult_new, start);
                                }
                                region.assign_advice(
                                    || "assign key_rlc".to_string(),
                                    self.accumulators.key.rlc,
                                    offset,
                                    || Ok(key_rlc_new),
                                )?;

                                // Store key_rlc into rlc2 to be later set in
                                // leaf value C row (to enable lookups):
                                pv.rlc2 = key_rlc_new;

                                // Assign previous key RLC -
                                // needed in case of placeholder branch/extension.
                                // Constraint for this is in leaf_key.
                                region.assign_advice(
                                    || "assign key_rlc".to_string(),
                                    self.denoter.sel1,
                                    offset,
                                    || Ok(pv.key_rlc_prev),
                                )?;
                                region.assign_advice(
                                    || "assign key_rlc_mult".to_string(),
                                    self.denoter.sel2,
                                    offset,
                                    || Ok(pv.key_rlc_mult_prev),
                                )?;
                            }

                            if row.get_type() == MptWitnessRowType::StorageLeafSValue
                                || row.get_type() == MptWitnessRowType::StorageLeafCValue {
                                // Info whether leaf value is 1 byte or more:
                                let mut is_long = false;
                                let row_prev = &witness[ind - 1];
                                if row_prev.get_byte(0) == 248 {
                                    // whole leaf is in long format (3 RLP meta bytes)
                                    let key_len = row_prev.get_byte(2) - 128;
                                    if row_prev.get_byte(1) - key_len - 1 > 1 {
                                        is_long = true;
                                    }
                                } else if row_prev.get_byte(1) < 128 {
                                    // last_level or one_nibble
                                    let leaf_len = row_prev.get_byte(0) - 192;
                                    if leaf_len - 1 > 1 {
                                        is_long = true;
                                    }
                                } else {
                                    let leaf_len = row_prev.get_byte(0) - 192;
                                    let key_len = row_prev.get_byte(1) - 128;
                                    if leaf_len - key_len - 1 > 1 {
                                        is_long = true;
                                    }
                                }
                                // Short means there is only one byte for value (no RLP specific bytes).
                                // Long means there is more than one byte for value which brings two
                                // RLP specific bytes, like: 161 160 ... for 32-long value.
                                let mut typ = "short";
                                if is_long {
                                    typ = "long";
                                } 
                                assign_long_short(&mut region, typ);

                                // Leaf RLC
                                self.compute_acc_and_mult(
                                    &row.bytes,
                                    &mut pv.acc_s,
                                    &mut pv.acc_mult_s,
                                    0,
                                    HASH_WIDTH + 2,
                                );

                                pv.acc_c = F::zero();
                                pv.acc_mult_c = F::one();
                                // Leaf value RLC
                                let mut start = 0;
                                if is_long {
                                    start = 2;
                                }
                                self.compute_acc_and_mult(
                                    &row.bytes,
                                    &mut pv.acc_c,
                                    &mut pv.acc_mult_c,
                                    start,
                                    HASH_WIDTH + 2,
                                );

                                let empty_trie_hash: Vec<u8> = vec![
                                    86, 232, 31, 23, 27, 204, 85, 166, 255, 131, 69, 230, 146, 192,
                                    248, 110, 91, 72, 224, 27, 153, 108, 173, 192, 1, 98, 47, 181,
                                    227, 99, 180, 33,
                                ];
                                if row.get_type() == MptWitnessRowType::StorageLeafSValue {
                                    // Store leaf value RLC into rlc1 to be later set in
                                    // leaf value C row (to enable lookups):
                                    pv.rlc1 = pv.acc_c;

                                    // account leaf storage codehash S <- rotate here
                                    // account leaf storage codehash C
                                    // account leaf in added branch
                                    // leaf key S
                                    // leaf value S <- we are here
                                    // leaf key C
                                    // leaf value C
                                    let row_prev = &witness[offset - 4];
                                    if row_prev.get_type() == MptWitnessRowType::AccountLeafRootCodehashS
                                        && row_prev.s_hash_bytes() == empty_trie_hash
                                    {
                                        // Leaf is without branch and it is just a placeholder.
                                        region.assign_advice(
                                            || "assign sel1".to_string(),
                                            self.denoter.sel1,
                                            offset,
                                            || Ok(F::one()),
                                        )?;
                                    }
                                } else if row.get_type() == MptWitnessRowType::StorageLeafCValue {
                                    region.assign_advice(
                                        || "assign key_rlc into key_rlc_mult".to_string(),
                                        self.accumulators.key.mult,
                                        offset,
                                        || Ok(pv.rlc2),
                                    )?;
                                    region.assign_advice(
                                        || "assign leaf value S into mult_diff".to_string(),
                                        self.accumulators.mult_diff,
                                        offset,
                                        || Ok(pv.rlc1),
                                    )?;

                                    // account leaf storage codehash S
                                    // account leaf storage codehash C <- rotate here
                                    // account leaf in added branch
                                    // leaf key S
                                    // leaf value S
                                    // leaf key C
                                    // leaf value C <- we are here
                                    let row_prev = &witness[offset - 5];
                                    if row_prev.get_type() == MptWitnessRowType::AccountLeafRootCodehashC
                                        && row_prev.s_hash_bytes() == empty_trie_hash
                                    {
                                        // Leaf is without branch and it is just a placeholder.
                                        region.assign_advice(
                                            || "assign sel2".to_string(),
                                            self.denoter.sel2,
                                            offset,
                                            || Ok(F::one()),
                                        )?;
                                    }
                                }

                                self.assign_acc(
                                    &mut region,
                                    pv.acc_s, // leaf RLC
                                    pv.acc_mult_s,
                                    pv.acc_c, // leaf value RLC
                                    F::zero(),
                                    offset,
                                )?;
                            }

                            if row.get_type() == MptWitnessRowType::AccountLeafKeyS {
                                self.account_leaf_key_s.assign(&mut region, self, &mut pv, &row.bytes, offset);
                            } else if row.get_type() == MptWitnessRowType::AccountLeafKeyC {
                                self.account_leaf_key_c.assign(&mut region, self, &mut pv, &row.bytes, offset);
                            } else if row.get_type() == MptWitnessRowType::AccountLeafNonceBalanceS {
                                self.account_leaf_nonce_balance_s.assign(&mut region, self, &mut pv, &row.bytes, offset);
                            } else if row.get_type() == MptWitnessRowType::AccountLeafNonceBalanceC {
                                self.account_leaf_nonce_balance_c.assign(&mut region, self, &mut pv, &row.bytes, offset);
                            } else if row.get_type() == MptWitnessRowType::AccountLeafRootCodehashS {
                                self.account_leaf_storage_codehash_s.assign(&mut region, self, &mut pv, &row.bytes, offset);
                            } else if row.get_type() == MptWitnessRowType::AccountLeafRootCodehashC {
                                self.account_leaf_storage_codehash_c.assign(&mut region, self, &mut pv, &row.bytes, offset);
                            } else if row.get_type() == MptWitnessRowType::NeighbouringStorageLeaf && row.get_byte(1) != 0 {
                                // row[1] != 0 just to avoid usize problems below (when row doesn't
                                // need to be assigned) Info whether
                                // leaf rlp is long or short.
                                let mut typ = "short";
                                if row.get_byte(0) == 248 {
                                    typ = "long";
                                } else if row.get_byte(1) == 32 {
                                    typ = "last_level";
                                }
                                assign_long_short(&mut region, typ);

                                pv.acc_s = F::zero();
                                pv.acc_mult_s = F::one();
                                let len: usize;
                                if row.get_byte(0) == 248 {
                                    len = (row.get_byte(2) - 128) as usize + 3;
                                } else {
                                    len = (row.get_byte(1) - 128) as usize + 2;
                                }
                                self.compute_acc_and_mult(
                                    &row.bytes,
                                    &mut pv.acc_s,
                                    &mut pv.acc_mult_s,
                                    0,
                                    len,
                                );

                                self.assign_acc(
                                    &mut region,
                                    pv.acc_s,
                                    pv.acc_mult_s,
                                    F::zero(),
                                    F::zero(),
                                    offset,
                                )?;
                            } else if row.get_type() == MptWitnessRowType::ExtensionNodeS {
                                if pv.is_extension_node {
                                  	// [228,130,0,149,160,114,253,150,133,18,192,156,19,241,162,51,210,24,1,151,16,48,7,177,42,60,49,34,230,254,242,79,132,165,90,75,249]

                                    // One nibble:
                                  	// [226,16,160,172,105,12...
                                    // Could also be non-hashed branch:
                                    // [223,16,221,198,132,32,0,0,0,1,198,132,32,0,0,0,1,128,128,128,128,128,128,128,128,128,128,128,128,128,128,128]

                                   	// [247,160,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,213,128,194,32,1,128,194,32,1,128,128,128,128,128,128,128,128,128,128,128,128,128]
                                   	// [248,58,159,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,217,128,196,130,32,0,1,128,196,130,32,0,1,128,128,128,128,128,128,128,128,128,128,128,128,128]

                                    // Intermediate RLC value and mult (after key)
                                    // to know which mult we need to use in c_advices.
                                    pv.acc_s = F::zero();
                                    pv.acc_mult_s = F::one();
                                    let len: usize;
                                    if row.get_byte(1) <= 32 {
                                        // key length is 1
                                        len = 2 // [length byte, key]
                                    } else if row.get_byte(0) < 248 {
                                        len = (row.get_byte(1) - 128) as usize + 2;
                                    } else {
                                        len = (row.get_byte(2) - 128) as usize + 3;
                                    }
                                    self.compute_acc_and_mult(
                                        &row.bytes,
                                        &mut pv.acc_s,
                                        &mut pv.acc_mult_s,
                                        0,
                                        len,
                                    );

                                    // Final RLC value.
                                    pv.acc_c = pv.acc_s;
                                    pv.acc_mult_c = pv.acc_mult_s;
                                    let mut start = C_RLP_START + 1;
                                    let mut len = HASH_WIDTH + 1;
                                    if row.get_byte(C_RLP_START + 1) == 0 {
                                        // non-hashed branch in extension node
                                        start = C_START;
                                        len = HASH_WIDTH;
                                    }
                                    self.compute_acc_and_mult(
                                        &row.bytes,
                                        &mut pv.acc_c,
                                        &mut pv.acc_mult_c,
                                        start,
                                        len,
                                    );

                                    self.assign_acc(
                                        &mut region,
                                        pv.acc_s,
                                        pv.acc_mult_s,
                                        pv.acc_c,
                                        F::zero(),
                                        offset,
                                    )?;
                                }
                                region.assign_advice(
                                    || "assign key_rlc".to_string(),
                                    self.accumulators.key.rlc,
                                    offset,
                                    || Ok(pv.extension_node_rlc),
                                )?;
                            } else if row.get_type() == MptWitnessRowType::ExtensionNodeC {
                                if pv.is_extension_node {
                                    // We use intermediate value from previous row (because
                                    // up to acc_s it's about key and this is the same
                                    // for both S and C).
                                    pv.acc_c = pv.acc_s;
                                    pv.acc_mult_c = pv.acc_mult_s;
                                    let mut start = C_RLP_START + 1;
                                    let mut len = HASH_WIDTH + 1;
                                    if row.get_byte(C_RLP_START + 1) == 0 {
                                        // non-hashed branch in extension node
                                        start = C_START;
                                        len = HASH_WIDTH;
                                    }
                                    self.compute_acc_and_mult(
                                        &row.bytes,
                                        &mut pv.acc_c,
                                        &mut pv.acc_mult_c,
                                        start,
                                        len,
                                    );

                                    self.assign_acc(
                                        &mut region,
                                        pv.acc_s,
                                        pv.acc_mult_s,
                                        pv.acc_c,
                                        F::zero(),
                                        offset,
                                    )?;
                                }

                                region.assign_advice(
                                    || "assign key_rlc".to_string(),
                                    self.accumulators.key.rlc,
                                    offset,
                                    || Ok(pv.extension_node_rlc),
                                )?;
                            } else if row.get_type() == MptWitnessRowType::AccountLeafNeighbouringLeaf && row.get_byte(1) != 0 {
                                // row[1] != 0 just to avoid usize problems below (when row doesn't
                                // need to be assigned).
                                self.account_leaf_key_in_added_branch.assign(&mut region, self, &mut pv, &row.bytes, offset);
                            } else if row.get_type() == MptWitnessRowType::AccountNonExisting { 
                               self.account_non_existing.assign(&mut region, self, &witness, offset);
                            }

                            offset += 1;
                        }
                    }

                    Ok(())
                },
            )
            .ok();
    }

    pub fn load(
        &self,
        _layouter: &mut impl Layouter<F>,
        to_be_hashed: Vec<Vec<u8>>,
    ) -> Result<(), Error> {
        self.load_keccak_table(_layouter, to_be_hashed).ok();
        self.load_fixed_table(_layouter).ok();

        Ok(())
    }

    fn compute_keccak(&self, msg: &[u8]) -> Vec<u8> {
        let mut keccak = Keccak::default();
        keccak.update(msg);
        keccak.digest()
    }

    fn load_keccak_table(
        &self,
        layouter: &mut impl Layouter<F>,
        to_be_hashed: Vec<Vec<u8>>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "keccak table",
            |mut region| {
                let mut offset = 0;

                for t in to_be_hashed.iter() {
                    let hash = self.compute_keccak(t);
                    let mut rlc = F::zero();
                    let mut mult = F::one();

                    for (ind, i) in t.iter().enumerate() {
                        rlc += F::from(*i as u64) * mult;
                        mult *= self.acc_r;
                    }

                    region.assign_fixed(
                        || "Keccak table",
                        self.keccak_table[0],
                        offset,
                        || Ok(rlc),
                    )?;

                    let hash_rlc = bytes_into_rlc(&hash, self.acc_r);
                    region.assign_fixed(
                        || "Keccak table",
                        self.keccak_table[1],
                        offset,
                        || Ok(hash_rlc),
                    )?;

                    offset += 1;
                }

                Ok(())
            },
        )
    }

    fn load_fixed_table(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
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
                        || Ok(F::from(FixedTableTag::RMult as u64)),
                    )?;

                    region.assign_fixed(
                        || "fixed table",
                        self.fixed_table[1],
                        offset,
                        || Ok(F::from(ind as u64)),
                    )?;

                    region.assign_fixed(
                        || "fixed table",
                        self.fixed_table[2],
                        offset,
                        || Ok(mult),
                    )?;
                    mult = mult * self.acc_r;

                    offset += 1;
                }

                for ind in 0..256 {
                    region.assign_fixed(
                        || "fixed table",
                        self.fixed_table[0],
                        offset,
                        || Ok(F::from(FixedTableTag::Range256 as u64)),
                    )?;

                    region.assign_fixed(
                        || "fixed table",
                        self.fixed_table[1],
                        offset,
                        || Ok(F::from(ind as u64)),
                    )?;

                    offset += 1;
                }

                /*
                for ind in 0..(33 * 255) {
                    region.assign_fixed(
                        || "fixed table",
                        self.fixed_table[0],
                        offset,
                        || Ok(F::from(FixedTableTag::RangeKeyLen256 as u64)),
                    )?;

                    region.assign_fixed(
                        || "fixed table",
                        self.fixed_table[1],
                        offset,
                        || Ok(F::from(ind as u64)),
                    )?;

                    offset += 1;
                }
                */

                for ind in 0..16 {
                    region.assign_fixed(
                        || "fixed table",
                        self.fixed_table[0],
                        offset,
                        || Ok(F::from(FixedTableTag::Range16 as u64)),
                    )?;

                    region.assign_fixed(
                        || "fixed table",
                        self.fixed_table[1],
                        offset,
                        || Ok(F::from(ind as u64)),
                    )?;

                    offset += 1;
                }

                Ok(())
            },
        )
    }
}

#[cfg(test)]
mod tests {
    use crate::param::IS_NON_EXISTING_ACCOUNT_POS;

    use super::*;

    use halo2_proofs::{
        circuit::{Layouter, SimpleFloorPlanner},
        dev::{MockProver, VerifyFailure},
        plonk::{
            create_proof, keygen_pk, keygen_vk, verify_proof, Advice, Circuit, Column,
            ConstraintSystem, Error,
        },
        poly::commitment::Params,
        transcript::{Blake2bRead, Blake2bWrite, Challenge255},
    };

    use ark_std::{end_timer, rand::SeedableRng, start_timer};
    use pairing::{
        arithmetic::FieldExt,
        bn256::{Bn256, Fr as Fp},
    };
    use rand_xorshift::XorShiftRng;
    use std::{fs, marker::PhantomData};

    #[test]
    fn test_mpt() {
        #[derive(Default)]
        struct MyCircuit<F> {
            _marker: PhantomData<F>,
            witness: Vec<Vec<u8>>,
        }

        impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
            type Config = MPTConfig<F>;
            type FloorPlanner = SimpleFloorPlanner;

            fn without_witnesses(&self) -> Self {
                Self::default()
            }

            fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                MPTConfig::configure(meta)
            }

            fn synthesize(
                &self,
                config: Self::Config,
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

                config.load(&mut layouter, to_be_hashed)?;
                config.assign(layouter, &witness_rows);

                Ok(())
            }
        }

        // for debugging:
        let path = "mpt/tests";
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
                let mut parts = path.to_str().unwrap().split("-");
                parts.next();
                let file = std::fs::File::open(path.clone());
                let reader = std::io::BufReader::new(file.unwrap());
                let w: Vec<Vec<u8>> = serde_json::from_reader(reader).unwrap();
                let circuit = MyCircuit::<Fp> {
                    _marker: PhantomData,
                    witness: w.clone(),
                };

                let mut pub_root = vec![];
                let acc_r = Fp::one() + Fp::one();
                for row in w.iter().filter(|r| r[r.len() - 1] != 5) {
                    let l = row.len();
                    let pub_root_rlc = bytes_into_rlc(
                        &row[l - HASH_WIDTH - IS_NON_EXISTING_ACCOUNT_POS
                            ..l - HASH_WIDTH - IS_NON_EXISTING_ACCOUNT_POS + HASH_WIDTH],
                        acc_r,
                    );

                    pub_root.push(pub_root_rlc);
                }

                println!("{:?}", path);
                let prover = MockProver::<Fp>::run(9, &circuit, vec![pub_root]).unwrap();
                assert_eq!(prover.verify(), Ok(()));

                /*
                let degree: u32 = 12;

                let rng = XorShiftRng::from_seed([
                    0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb,
                    0x37, 0x32, 0x54, 0x06, 0xbc, 0xe5,
                ]);

                // Bench setup generation
                let setup_message =
                    format!("Setup generation with degree = {}", degree);
                let start1 = start_timer!(|| setup_message);
                let general_params = Setup::<Bn256>::new(degree, rng);
                end_timer!(start1);

                let vk = keygen_vk(&general_params, &circuit).unwrap();
                let pk = keygen_pk(&general_params, vk, &circuit).unwrap();

                // Prove
                let mut transcript =
                    Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);

                // Bench proof generation time
                let proof_message =
                    format!("MPT Proof generation with 2^{} rows", degree);
                let start2 = start_timer!(|| proof_message);
                create_proof(
                    &general_params,
                    &pk,
                    &[circuit],
                    &[&[]],
                    &mut transcript,
                )
                .unwrap();
                let proof = transcript.finalize();
                end_timer!(start2);

                // Verify
                let verifier_params =
                    Setup::<Bn256>::verifier_params(&general_params, 0)
                        .unwrap();
                let mut verifier_transcript =
                    Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);

                // Bench verification time
                let start3 = start_timer!(|| "MPT Proof verification");
                verify_proof(
                    &verifier_params,
                    pk.get_vk(),
                    &[&[]],
                    &mut verifier_transcript,
                )
                .unwrap();
                end_timer!(start3);
                */
            });
    }
}
