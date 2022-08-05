use halo2_proofs::{
    circuit::{Layouter, Region},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed},
    poly::Rotation,
};
use keccak256::plain::Keccak;
use pairing::arithmetic::FieldExt;
use std::convert::TryInto;

use crate::{
    account_leaf_key::AccountLeafKeyChip,
    account_leaf_key_in_added_branch::AccountLeafKeyInAddedBranchChip,
    account_leaf_nonce_balance::AccountLeafNonceBalanceConfig,
    account_leaf_storage_codehash::AccountLeafStorageCodehashChip,
    branch::BranchChip,
    branch_hash_in_parent::BranchHashInParentChip,
    branch_parallel::BranchParallelChip,
    branch_rlc::BranchRLCChip,
    branch_rlc_init::BranchRLCInitChip,
    extension_node::ExtensionNodeChip,
    extension_node_key::ExtensionNodeKeyChip,
    helpers::{get_is_extension_node, bytes_into_rlc},
    leaf_key::LeafKeyChip,
    leaf_key_in_added_branch::LeafKeyInAddedBranchChip,
    leaf_value::LeafValueChip,
    param::{
        ACCOUNT_LEAF_KEY_C_IND, ACCOUNT_LEAF_KEY_S_IND, ACCOUNT_LEAF_NONCE_BALANCE_C_IND,
        ACCOUNT_LEAF_NONCE_BALANCE_S_IND, COUNTER_WITNESS_LEN, IS_BALANCE_MOD_POS,
        IS_BRANCH_C16_POS, IS_BRANCH_C1_POS, IS_EXT_LONG_EVEN_C16_POS,
        IS_EXT_LONG_EVEN_C1_POS, IS_EXT_LONG_ODD_C16_POS, IS_EXT_LONG_ODD_C1_POS,
        IS_EXT_SHORT_C16_POS, IS_EXT_SHORT_C1_POS, IS_NONCE_MOD_POS, IS_STORAGE_MOD_POS,
        RLP_NUM, NOT_FIRST_LEVEL_POS, IS_ACCOUNT_DELETE_MOD_POS, IS_NON_EXISTING_ACCOUNT_POS,
    },
    roots::RootsChip,
    storage_root_in_account_leaf::StorageRootChip, account_non_existing::AccountNonExistingChip,
};
use crate::{branch_key::BranchKeyChip, param::WITNESS_ROW_WIDTH};
use crate::{
    param::{
        BRANCH_0_C_START, BRANCH_0_KEY_POS, BRANCH_0_S_START, C_RLP_START, C_START, DRIFTED_POS,
        HASH_WIDTH, IS_BRANCH_C_PLACEHOLDER_POS, IS_BRANCH_S_PLACEHOLDER_POS, KECCAK_INPUT_WIDTH,
        KECCAK_OUTPUT_WIDTH, S_RLP_START, S_START,
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

// TODO: constraints for the length of key and address RLC to be 32 bytes long

#[derive(Clone, Debug)]
pub(crate) struct ProofTypeCols {
    pub(crate) is_storage_mod: Column<Advice>,
    pub(crate) is_nonce_mod: Column<Advice>,
    pub(crate) is_balance_mod: Column<Advice>,
    pub(crate) is_account_delete_mod: Column<Advice>,
    pub(crate) is_non_existing_account_proof: Column<Advice>,
}

#[derive(Clone, Debug)]
pub(crate) struct MainCols { // Main as opposed to other columns which are selectors and RLC accumulators.
    pub(crate) rlp1: Column<Advice>,
    pub(crate) rlp2: Column<Advice>,
    pub(crate) bytes: [Column<Advice>; HASH_WIDTH],
}

#[derive(Clone, Debug)]
pub(crate) struct AccountLeafCols {
    pub(crate) is_key_s: Column<Advice>,
    pub(crate) is_key_c: Column<Advice>,
    pub(crate) is_non_existing_account_row: Column<Advice>,
    pub(crate) is_nonce_balance_s: Column<Advice>,
    pub(crate) is_nonce_balance_c: Column<Advice>,
    pub(crate) is_storage_codehash_s: Column<Advice>,
    pub(crate) is_storage_codehash_c: Column<Advice>,
    pub(crate) is_in_added_branch: Column<Advice>,
}

#[derive(Default)]
struct AccountLeaf {
    is_key_s: bool,
    is_key_c: bool,
    is_non_existing_account_row: bool,
    is_nonce_balance_s: bool,
    is_nonce_balance_c: bool,
    is_storage_codehash_s: bool,
    is_storage_codehash_c: bool,
    is_in_added_branch: bool,
}

#[derive(Clone, Debug)]
pub(crate) struct StorageLeafCols {
    pub(crate) is_s_key: Column<Advice>,
    pub(crate) is_s_value: Column<Advice>,
    pub(crate) is_c_key: Column<Advice>,
    pub(crate) is__c_value: Column<Advice>,
    /** it is at drifted_pos position in added branch,
    * note that this row could be omitted when there
    * is no added branch but then it would open a
    * vulnerability because the attacker could omit
    * these row in cases when it is needed too (and
    * constraints happen in this row) */
    pub(crate) is_in_added_branch: Column<Advice>,
}

#[derive(Default)]
struct StorageLeaf {
    is_s_key: bool,
    is_s_value: bool,
    is_c_key: bool,
    is_c_value: bool,
    is_in_added_branch: bool,
}

#[derive(Clone, Debug)]
pub(crate) struct BranchCols {
    pub(crate) is_init: Column<Advice>,
    pub(crate) is_child: Column<Advice>,
    pub(crate) is_last_child: Column<Advice>,
    pub(crate) node_index: Column<Advice>,
    pub(crate) is_modified: Column<Advice>,   // whether this branch node is modified
    pub(crate) modified_node: Column<Advice>, // index of the modified node
    pub(crate) is_at_drifted_pos: Column<Advice>, // needed when leaf is turned into branch
    pub(crate) drifted_pos: Column<Advice>,   /* needed when leaf is turned into branch - first nibble of
                                    * the key stored in a leaf (because the existing leaf will
                                    * jump to this position in added branch) */
    pub(crate) is_extension_node_s: Column<Advice>, /* contains extension node key (s_advices) and hash of
                                          * the branch (c_advices) */
    pub(crate) is_extension_node_c: Column<Advice>,
}

#[derive(Clone, Debug)]
pub struct MPTConfig<F> {
    pub(crate) proof_type: ProofTypeCols,
    pub(crate) q_enable: Column<Fixed>,
    pub(crate) q_not_first: Column<Fixed>, // not first row
    pub(crate) not_first_level: Column<Advice>,
    pub(crate) inter_start_root: Column<Advice>,
    pub(crate) inter_final_root: Column<Advice>,
    pub(crate) branch: BranchCols,
    pub(crate) s_main: MainCols,
    pub(crate) c_main: MainCols,
    pub(crate) account_leaf: AccountLeafCols,
    pub(crate) storage_leaf: StorageLeafCols,
    pub(crate) s_mod_node_hash_rlc: Column<Advice>, /* modified node s_advices RLC when s_advices present
                                          * hash (used also for leaf long/short) */
    pub(crate) c_mod_node_hash_rlc: Column<Advice>, /* modified node c_advices RLC when c_advices present
                                          * hash (used also for leaf long/short) */
    pub(crate) acc_s: Column<Advice>,      // for branch s and account leaf
    pub(crate) acc_mult_s: Column<Advice>, // for branch s and account leaf
    pub(crate) acc_c: Column<Advice>,      // for branch c
    pub(crate) acc_mult_c: Column<Advice>, // for branch c
    pub(crate) acc_r: F,
    // sel1 and sel2 in branch children: denote whether there is no leaf at is_modified (when value
    // is added or deleted from trie - but no branch is added or turned into leaf)
    // sel1 and sel2 in storage leaf key: key_rlc_prev and key_rlc_mult_prev
    // sel1 and sel2 in storage leaf value (only when leaf without branch as otherwise this info is
    // in the branch above): whether leaf is just a placeholder
    // sel1 and sel2 in account leaf key specifies whether nonce / balance are short / long (check
    // nonce balance row: offset - 1)
    pub(crate) sel1: Column<Advice>,
    pub(crate) sel2: Column<Advice>,
    pub(crate) is_node_hashed_s: Column<Advice>,
    pub(crate) is_node_hashed_c: Column<Advice>,
    pub(crate) node_mult_diff_s: Column<Advice>,
    pub(crate) node_mult_diff_c: Column<Advice>,
    r_table: Vec<Expression<F>>,
    // key_rlc & key_rlc_mult used for account address, for storage key,
    // and for mult_diff_nonce/mult_diff_balance in account_leaf_nonce_balance
    pub(crate) key_rlc: Column<Advice>,
    pub(crate) key_rlc_mult: Column<Advice>,
    pub(crate) mult_diff: Column<Advice>,
    keccak_table: [Column<Fixed>; KECCAK_INPUT_WIDTH + KECCAK_OUTPUT_WIDTH],
    fixed_table: [Column<Fixed>; 3],
    pub(crate) address_rlc: Column<Advice>, /* The same in all rows of a modification. The same as
                                  * address_rlc computed in the account leaf key row. Needed to
                                  * enable lookup for storage key/value (to have address RLC in
                                  * the same row as storage key/value). */
    counter: Column<Advice>,
    account_leaf_nonce_balance_config_s: AccountLeafNonceBalanceConfig<F>,
    account_leaf_nonce_balance_config_c: AccountLeafNonceBalanceConfig<F>,
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

        let proof_type = ProofTypeCols {
            is_storage_mod: meta.advice_column(),
            is_nonce_mod: meta.advice_column(),
            is_balance_mod: meta.advice_column(),
            is_account_delete_mod: meta.advice_column(),
            is_non_existing_account_proof: meta.advice_column(),
        };

        let account_leaf = AccountLeafCols {
            is_key_s : meta.advice_column(),
            is_key_c : meta.advice_column(),
            is_non_existing_account_row : meta.advice_column(),
            is_nonce_balance_s : meta.advice_column(),
            is_nonce_balance_c : meta.advice_column(),
            is_storage_codehash_s : meta.advice_column(),
            is_storage_codehash_c : meta.advice_column(),
            is_in_added_branch : meta.advice_column(),
        };

        let storage_leaf = StorageLeafCols {
            is_s_key : meta.advice_column(),
            is_s_value : meta.advice_column(),
            is_c_key : meta.advice_column(),
            is__c_value : meta.advice_column(),
            is_in_added_branch : meta.advice_column(),
        };

        let branch = BranchCols {
            is_init: meta.advice_column(),
            is_child: meta.advice_column(),
            is_last_child: meta.advice_column(),
            node_index: meta.advice_column(),
            is_modified: meta.advice_column(),
            modified_node: meta.advice_column(),
            is_at_drifted_pos: meta.advice_column(),
            drifted_pos: meta.advice_column(),
            is_extension_node_s: meta.advice_column(),
            is_extension_node_c: meta.advice_column(),
        };

        let s_main = MainCols {
            rlp1: meta.advice_column(),
            rlp2: meta.advice_column(),
            bytes: (0..HASH_WIDTH)
                .map(|_| meta.advice_column())
                .collect::<Vec<_>>()
                .try_into()
                .unwrap(),
        };
        let c_main = MainCols {
            rlp1: meta.advice_column(),
            rlp2: meta.advice_column(),
            bytes: (0..HASH_WIDTH)
                .map(|_| meta.advice_column())
                .collect::<Vec<_>>()
                .try_into()
                .unwrap(),
        };

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

        let s_mod_node_hash_rlc = meta.advice_column();
        let c_mod_node_hash_rlc = meta.advice_column();

        let acc_s = meta.advice_column();
        let acc_mult_s = meta.advice_column();
        let acc_c = meta.advice_column();
        let acc_mult_c = meta.advice_column();

        let sel1 = meta.advice_column();
        let sel2 = meta.advice_column();

        let is_node_hashed_s = meta.advice_column();
        let is_node_hashed_c = meta.advice_column();

        let node_mult_diff_s = meta.advice_column();
        let node_mult_diff_c = meta.advice_column();

        // NOTE: acc_mult_s and acc_mult_c wouldn't be needed if we would have
        // big endian instead of little endian. However, then it would be much more
        // difficult to handle the accumulator when we iterate over the row.
        // For example, big endian would mean to compute acc = acc * mult_r + row[i],
        // but we don't want acc to be multiplied by mult_r when row[i] = 0 where
        // the stream already ended and 0s are only to fulfill the row.

        let key_rlc = meta.advice_column();
        let key_rlc_mult = meta.advice_column();
        let mult_diff = meta.advice_column();

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
            sel1,
            sel2,
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

        BranchChip::<F>::configure(
            meta,
            q_enable,
            q_not_first,
            s_main.clone(),
            c_main.clone(),
            branch.clone(),
            is_node_hashed_s,
            is_node_hashed_c,
            fixed_table.clone(),
        );

        BranchKeyChip::<F>::configure(
            meta,
            q_not_first,
            not_first_level,
            branch.clone(),
            account_leaf.is_in_added_branch,
            s_main.clone(),
            s_main.bytes[IS_BRANCH_C16_POS - RLP_NUM], // TODO: remove
            s_main.bytes[IS_BRANCH_C1_POS - RLP_NUM], // TODO: remove
            key_rlc,
            key_rlc_mult,
            acc_r,
        );

        BranchParallelChip::<F>::configure(
            meta,
            q_enable,
            q_not_first,
            branch.clone(),
            s_mod_node_hash_rlc,
            s_main.clone(),
            sel1,
            is_node_hashed_s,
            acc_r,
        );

        BranchParallelChip::<F>::configure(
            meta,
            q_enable,
            q_not_first,
            branch.clone(),
            c_mod_node_hash_rlc,
            c_main.clone(),
            sel2,
            is_node_hashed_c,
            acc_r,
        );

        BranchHashInParentChip::<F>::configure(
            meta,
            inter_start_root,
            not_first_level,
            q_not_first,
            account_leaf.is_in_added_branch,
            branch.is_last_child,
            s_main.bytes[IS_BRANCH_S_PLACEHOLDER_POS - RLP_NUM], // TODO: remove
            s_main.clone(),
            s_mod_node_hash_rlc,
            acc_s,
            acc_mult_s,
            keccak_table,
        );

        BranchHashInParentChip::<F>::configure(
            meta,
            inter_final_root,
            not_first_level,
            q_not_first,
            account_leaf.is_in_added_branch,
            branch.is_last_child,
            s_main.bytes[IS_BRANCH_C_PLACEHOLDER_POS - RLP_NUM], // TODO: remove
            s_main.clone(),
            c_mod_node_hash_rlc,
            acc_c,
            acc_mult_c,
            keccak_table,
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
            acc_s,
            acc_mult_s,
            acc_c,
            acc_mult_c,
            keccak_table,
            s_mod_node_hash_rlc,
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
            acc_s,
            acc_mult_s,
            acc_c,
            acc_mult_c,
            keccak_table,
            c_mod_node_hash_rlc,
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
            key_rlc,
            key_rlc_mult,
            mult_diff,
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
            acc_s,
            acc_mult_s,
            acc_c,
            acc_mult_c,
            sel1,
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
            acc_s,
            acc_mult_s,
            acc_c,
            acc_mult_c,
            sel2,
            keccak_table,
            acc_r,
            false,
        );

        BranchRLCInitChip::<F>::configure(
            meta,
            |meta| {
                meta.query_advice(branch.is_init, Rotation::cur())
                    * meta.query_fixed(q_enable, Rotation::cur())
            },
            s_main.clone(),
            acc_s,
            acc_mult_s,
            acc_c,
            acc_mult_c,
            acc_r,
        );

        BranchRLCChip::<F>::configure(
            meta,
            |meta| {
                let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
                let is_branch_child = meta.query_advice(branch.is_child, Rotation::cur());

                q_not_first * is_branch_child
            },
            s_main.clone(),
            acc_s,
            acc_mult_s,
            is_node_hashed_s,
            node_mult_diff_s,
            r_table.clone(),
            fixed_table,
        );

        BranchRLCChip::<F>::configure(
            meta,
            |meta| {
                let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
                let is_branch_child = meta.query_advice(branch.is_child, Rotation::cur());

                q_not_first * is_branch_child
            },
            c_main.clone(),
            acc_c,
            acc_mult_c,
            is_node_hashed_c,
            node_mult_diff_c,
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
            s_mod_node_hash_rlc,
            c_mod_node_hash_rlc,
            acc_s,
            acc_mult_s,
            key_rlc,
            key_rlc_mult,
            sel1,
            sel2,
            s_main.bytes[IS_BRANCH_S_PLACEHOLDER_POS - RLP_NUM], // TODO: remove
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
            s_mod_node_hash_rlc,
            c_mod_node_hash_rlc,
            acc_s,
            acc_mult_s,
            key_rlc,
            key_rlc_mult,
            sel1,
            sel2,
            s_main.bytes[IS_BRANCH_C_PLACEHOLDER_POS - RLP_NUM], // TODO: remove
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
            s_mod_node_hash_rlc,
            c_mod_node_hash_rlc,
            acc_s,
            acc_mult_s,
            key_rlc,
            key_rlc_mult,
            mult_diff,
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
            s_mod_node_hash_rlc,
            c_mod_node_hash_rlc,
            keccak_table,
            acc_s,
            acc_mult_s,
            acc_c,
            sel1,
            sel2,
            key_rlc,
            key_rlc_mult,
            mult_diff,
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
            storage_leaf.is__c_value,
            s_main.clone(),
            s_mod_node_hash_rlc,
            c_mod_node_hash_rlc,
            keccak_table,
            acc_s,
            acc_mult_s,
            acc_c,
            sel1,
            sel2,
            key_rlc,
            key_rlc_mult,
            mult_diff,
            account_leaf.is_in_added_branch,
            s_main.bytes[IS_BRANCH_C_PLACEHOLDER_POS - RLP_NUM],
            false,
            acc_r,
            fixed_table.clone(),
        );

        AccountLeafKeyChip::<F>::configure(
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
            acc_s,
            acc_mult_s,
            key_rlc,
            key_rlc_mult,
            acc_c,
            acc_mult_c,
            r_table.clone(),
            fixed_table.clone(),
            address_rlc,
            sel2,
            true,
        );

        AccountLeafKeyChip::<F>::configure(
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
            acc_s,
            acc_mult_s,
            key_rlc,
            key_rlc_mult,
            acc_c,
            acc_mult_c,
            r_table.clone(),
            fixed_table.clone(),
            address_rlc,
            sel2,
            false,
        );

        AccountNonExistingChip::<F>::configure(
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
            key_rlc,
            key_rlc_mult,
            acc_s,
            sel1,
            r_table.clone(),
            fixed_table.clone(),
            address_rlc,
        );

        let account_leaf_nonce_balance_config_s = AccountLeafNonceBalanceConfig::<F>::configure(
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
            acc_s,
            acc_mult_s,
            acc_mult_c,
            acc_c,
            key_rlc_mult,
            r_table.clone(),
            s_mod_node_hash_rlc,
            c_mod_node_hash_rlc,
            sel1,
            sel2,
            fixed_table.clone(),
            true,
        );

        let account_leaf_nonce_balance_config_c = AccountLeafNonceBalanceConfig::<F>::configure(
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
            acc_s,
            acc_mult_s,
            acc_mult_c,
            acc_c,
            key_rlc_mult,
            r_table.clone(),
            s_mod_node_hash_rlc,
            c_mod_node_hash_rlc,
            sel1,
            sel2,
            fixed_table.clone(),
            false,
        );

        AccountLeafStorageCodehashChip::<F>::configure(
            meta,
            proof_type.clone(),
            inter_start_root,
            q_not_first,
            not_first_level,
            account_leaf.is_storage_codehash_s,
            s_main.clone(),
            c_main.clone(),
            acc_r,
            acc_s,
            acc_mult_s,
            fixed_table.clone(),
            s_mod_node_hash_rlc,
            c_mod_node_hash_rlc,
            sel1,
            sel2,
            keccak_table,
            true,
        );

        AccountLeafStorageCodehashChip::<F>::configure(
            meta,
            proof_type.clone(),
            inter_final_root,
            q_not_first,
            not_first_level,
            account_leaf.is_storage_codehash_c,
            s_main.clone(),
            c_main.clone(),
            acc_r,
            acc_s,
            acc_mult_s,
            fixed_table.clone(),
            s_mod_node_hash_rlc,
            c_mod_node_hash_rlc,
            sel1,
            sel2,
            keccak_table,
            false,
        );

        AccountLeafKeyInAddedBranchChip::<F>::configure(
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
            s_mod_node_hash_rlc,
            c_mod_node_hash_rlc,
            acc_s,
            acc_mult_s,
            acc_c, // mult_diff_nonce
            acc_mult_c,
            key_rlc,
            key_rlc_mult,
            mult_diff,
            branch.drifted_pos,
            sel1,
            sel2,
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
            s_mod_node_hash_rlc,
            c_mod_node_hash_rlc,
            acc_s,
            acc_mult_s,
            acc_c,
            acc_mult_c,
            acc_r,
            sel1,
            sel2,
            is_node_hashed_s,
            is_node_hashed_c,
            node_mult_diff_s,
            node_mult_diff_c,
            r_table,
            key_rlc,
            key_rlc_mult,
            mult_diff,
            keccak_table,
            fixed_table,
            address_rlc,
            counter,
            account_leaf_nonce_balance_config_s,
            account_leaf_nonce_balance_config_c,
        }
    }

    fn assign_row(
        &self,
        region: &mut Region<'_, F>,
        row: &[u8],
        is_branch_init: bool,
        is_branch_child: bool,
        is_last_branch_child: bool,
        node_index: u8,
        modified_node: u8,
        account_leaf: AccountLeaf,
        storage_leaf: StorageLeaf,
        drifted_pos: u8,
        is_extension_node_s: bool,
        is_extension_node_c: bool,
        offset: usize,
    ) -> Result<(), Error> {
        region.assign_advice(
            || "assign is_branch_init".to_string(),
            self.branch.is_init,
            offset,
            || Ok(F::from(is_branch_init as u64)),
        )?;

        region.assign_advice(
            || "assign is_branch_child".to_string(),
            self.branch.is_child,
            offset,
            || Ok(F::from(is_branch_child as u64)),
        )?;

        region.assign_advice(
            || "assign acc_s".to_string(),
            self.acc_s,
            offset,
            || Ok(F::zero()),
        )?;

        region.assign_advice(
            || "assign acc_mult_s".to_string(),
            self.acc_mult_s,
            offset,
            || Ok(F::zero()),
        )?;

        region.assign_advice(
            || "assign acc_c".to_string(),
            self.acc_c,
            offset,
            || Ok(F::zero()),
        )?;

        region.assign_advice(
            || "assign acc_mult_c".to_string(),
            self.acc_mult_c,
            offset,
            || Ok(F::zero()),
        )?;

        // because used for is_long
        region.assign_advice(
            || "assign s_modified_node_rlc".to_string(),
            self.s_mod_node_hash_rlc,
            offset,
            || Ok(F::zero()),
        )?;
        // because used for is_short
        region.assign_advice(
            || "assign c_modified_node_rlc".to_string(),
            self.c_mod_node_hash_rlc,
            offset,
            || Ok(F::zero()),
        )?;

        region.assign_advice(
            || "assign is_last_branch_child".to_string(),
            self.branch.is_last_child,
            offset,
            || Ok(F::from(is_last_branch_child as u64)),
        )?;

        region.assign_advice(
            || "assign node_index".to_string(),
            self.branch.node_index,
            offset,
            || Ok(F::from(node_index as u64)),
        )?;

        region.assign_advice(
            || "assign modified node".to_string(),
            self.branch.modified_node,
            offset,
            || Ok(F::from(modified_node as u64)),
        )?;

        region.assign_advice(
            || "assign drifted_pos".to_string(),
            self.branch.drifted_pos,
            offset,
            || Ok(F::from(drifted_pos as u64)),
        )?;

        region.assign_advice(
            || "assign is_at_drifted_pos".to_string(),
            self.branch.is_at_drifted_pos,
            offset,
            || Ok(F::from((drifted_pos == node_index) as u64)),
        )?;

        region.assign_advice(
            || "assign key rlc".to_string(),
            self.key_rlc,
            offset,
            || Ok(F::zero()),
        )?;

        region.assign_advice(
            || "assign key rlc mult".to_string(),
            self.key_rlc_mult,
            offset,
            || Ok(F::zero()),
        )?;

        region.assign_advice(
            || "assign mult diff".to_string(),
            self.mult_diff,
            offset,
            || Ok(F::zero()),
        )?;

        region.assign_advice(
            || "assign sel1".to_string(),
            self.sel1,
            offset,
            || Ok(F::zero()),
        )?;
        region.assign_advice(
            || "assign sel2".to_string(),
            self.sel2,
            offset,
            || Ok(F::zero()),
        )?;

        region.assign_advice(
            || "assign is_modified".to_string(),
            self.branch.is_modified,
            offset,
            || Ok(F::from((modified_node == node_index) as u64)),
        )?;

        region.assign_advice(
            || "assign is_leaf_s".to_string(),
            self.storage_leaf.is_s_key,
            offset,
            || Ok(F::from(storage_leaf.is_s_key as u64)),
        )?;
        region.assign_advice(
            || "assign is_leaf_c".to_string(),
            self.storage_leaf.is_c_key,
            offset,
            || Ok(F::from(storage_leaf.is_c_key as u64)),
        )?;

        region.assign_advice(
            || "assign is_leaf_s_value".to_string(),
            self.storage_leaf.is_s_value,
            offset,
            || Ok(F::from(storage_leaf.is_s_value as u64)),
        )?;
        region.assign_advice(
            || "assign is_leaf_c_value".to_string(),
            self.storage_leaf.is__c_value,
            offset,
            || Ok(F::from(storage_leaf.is_c_value as u64)),
        )?;

        region.assign_advice(
            || "assign is account leaf key s".to_string(),
            self.account_leaf.is_key_s,
            offset,
            || Ok(F::from(account_leaf.is_key_s as u64)),
        )?;
        region.assign_advice(
            || "assign is account leaf key c".to_string(),
            self.account_leaf.is_key_c,
            offset,
            || Ok(F::from(account_leaf.is_key_c as u64)),
        )?;
        region.assign_advice(
            || "assign is account leaf nonce balance s".to_string(),
            self.account_leaf.is_nonce_balance_s,
            offset,
            || Ok(F::from(account_leaf.is_nonce_balance_s as u64)),
        )?;
        region.assign_advice(
            || "assign is account leaf nonce balance c".to_string(),
            self.account_leaf.is_nonce_balance_c,
            offset,
            || Ok(F::from(account_leaf.is_nonce_balance_c as u64)),
        )?;
        region.assign_advice(
            || "assign is account leaf storage codehash s".to_string(),
            self.account_leaf.is_storage_codehash_s,
            offset,
            || Ok(F::from(account_leaf.is_storage_codehash_s as u64)),
        )?;
        region.assign_advice(
            || "assign is account leaf storage codehash c".to_string(),
            self.account_leaf.is_storage_codehash_c,
            offset,
            || Ok(F::from(account_leaf.is_storage_codehash_c as u64)),
        )?;
        region.assign_advice(
            || "assign is account leaf in added branch".to_string(),
            self.account_leaf.is_in_added_branch,
            offset,
            || Ok(F::from(account_leaf.is_in_added_branch as u64)),
        )?;

        region.assign_advice(
            || "assign is leaf in added branch".to_string(),
            self.storage_leaf.is_in_added_branch,
            offset,
            || Ok(F::from(storage_leaf.is_in_added_branch as u64)),
        )?;
        region.assign_advice(
            || "assign is extension node s".to_string(),
            self.branch.is_extension_node_s,
            offset,
            || Ok(F::from(is_extension_node_s as u64)),
        )?;
        region.assign_advice(
            || "assign is extension node c".to_string(),
            self.branch.is_extension_node_c,
            offset,
            || Ok(F::from(is_extension_node_c as u64)),
        )?;
        region.assign_advice(
            || "assign is non existing account row".to_string(),
            self.account_leaf.is_non_existing_account_row,
            offset,
            || Ok(F::from(account_leaf.is_non_existing_account_row as u64)),
        )?;

        region.assign_advice(
            || "assign s_rlp1".to_string(),
            self.s_main.rlp1,
            offset,
            || Ok(F::from(row[0] as u64)),
        )?;

        region.assign_advice(
            || "assign s_rlp2".to_string(),
            self.s_main.rlp2,
            offset,
            || Ok(F::from(row[1] as u64)),
        )?;

        for idx in 0..HASH_WIDTH {
            region.assign_advice(
                || format!("assign s_advice {}", idx),
                self.s_main.bytes[idx],
                offset,
                || Ok(F::from(row[RLP_NUM + idx] as u64)),
            )?;
        }

        // not all columns may be needed
        let get_val = |curr_ind: usize| {
            let val;
            if curr_ind >= row.len() {
                val = 0;
            } else {
                val = row[curr_ind];
            }

            val as u64
        };

        region.assign_advice(
            || "assign c_rlp1".to_string(),
            self.c_main.rlp1,
            offset,
            || Ok(F::from(get_val(WITNESS_ROW_WIDTH / 2))),
        )?;
        region.assign_advice(
            || "assign c_rlp2".to_string(),
            self.c_main.rlp2,
            offset,
            || Ok(F::from(get_val(WITNESS_ROW_WIDTH / 2 + 1))),
        )?;

        for (idx, _c) in self.c_main.bytes.iter().enumerate() {
            let val = get_val(WITNESS_ROW_WIDTH / 2 + RLP_NUM + idx);
            region.assign_advice(
                || format!("assign c_advice {}", idx),
                self.c_main.bytes[idx],
                offset,
                || Ok(F::from(val)),
            )?;
        }
        Ok(())
    }

    fn assign_branch_init(
        &self,
        region: &mut Region<'_, F>,
        row: &Vec<u8>,
        offset: usize,
    ) -> Result<(), Error> {
        let account_leaf = AccountLeaf::default();
        let storage_leaf = StorageLeaf::default();

        self.assign_row(
            region, row, true, false, false, 0, 0, account_leaf,
            storage_leaf, 0, false, false, offset,
        )?;

        Ok(())
    }

    fn assign_branch_row(
        &self,
        region: &mut Region<'_, F>,
        node_index: u8,
        key: u8,
        key_rlc: F,
        key_rlc_mult: F,
        mult_diff: F,
        row: &[u8],
        s_mod_node_hash_rlc: F,
        c_mod_node_hash_rlc: F,
        drifted_pos: u8,
        s_rlp1: i32,
        c_rlp1: i32,
        offset: usize,
    ) -> Result<(), Error> {
        let account_leaf = AccountLeaf::default();
        let storage_leaf = StorageLeaf::default();

        self.assign_row(
            region,
            row,
            false,
            true,
            node_index == 15,
            node_index,
            key,
            account_leaf,
            storage_leaf,
            drifted_pos,
            false,
            false,
            offset,
        )?;

        region.assign_advice(
            || "s_mod_node_hash_rlc",
            self.s_mod_node_hash_rlc,
            offset,
            || Ok(s_mod_node_hash_rlc),
        )?;
        region.assign_advice(
            || "c_mod_node_hash_rlc",
            self.c_mod_node_hash_rlc,
            offset,
            || Ok(c_mod_node_hash_rlc),
        )?;

        region.assign_advice(|| "key rlc", self.key_rlc, offset, || Ok(key_rlc))?;
        region.assign_advice(
            || "key rlc mult",
            self.key_rlc_mult,
            offset,
            || Ok(key_rlc_mult),
        )?;
        region.assign_advice(|| "mult diff", self.mult_diff, offset, || Ok(mult_diff))?;

        region.assign_advice(
            || "s_rlp1",
            self.s_main.rlp1,
            offset,
            || Ok(F::from(s_rlp1 as u64)),
        )?;
        region.assign_advice(
            || "c_rlp1",
            self.c_main.rlp1,
            offset,
            || Ok(F::from(c_rlp1 as u64)),
        )?;

        region.assign_advice(
            || "is_node_hashed_s",
            self.is_node_hashed_s,
            offset,
            || Ok(F::from((row[S_RLP_START + 1] == 0 && row[S_START] > 192) as u64)),
        )?;
        region.assign_advice(
            || "is_node_hashed_c",
            self.is_node_hashed_c,
            offset,
            || Ok(F::from((row[C_RLP_START + 1] == 0 && row[C_START] > 192) as u64)),
        )?;

        Ok(())
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
            self.s_mod_node_hash_rlc,
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
            self.c_mod_node_hash_rlc,
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
            self.acc_s,
            offset,
            || Ok(acc_s),
        )?;

        region.assign_advice(
            || "assign acc_mult_s".to_string(),
            self.acc_mult_s,
            offset,
            || Ok(acc_mult_s),
        )?;

        region.assign_advice(
            || "assign acc_c".to_string(),
            self.acc_c,
            offset,
            || Ok(acc_c),
        )?;

        region.assign_advice(
            || "assign acc_mult_c".to_string(),
            self.acc_mult_c,
            offset,
            || Ok(acc_mult_c),
        )?;

        Ok(())
    }

    // TODO: split assign
    pub(crate) fn assign(&self, mut layouter: impl Layouter<F>, witness: &[Vec<u8>]) {
        layouter
            .assign_region(
                || "MPT",
                |mut region| {
                    let mut offset = 0;
                    let mut pv = ProofVariables::new();

                    // filter out rows that are just to be hashed
                    for (ind, row) in witness.iter().filter(|r| r[r.len() - 1] != 5).enumerate() {
                        if offset > 0 {
                            let row_prev = &witness[offset - 1];
                            let not_first_level_prev =
                                row_prev[row_prev.len() - NOT_FIRST_LEVEL_POS];
                            let not_first_level_cur = row[row.len() - NOT_FIRST_LEVEL_POS];
                            if not_first_level_cur == 0 && not_first_level_prev == 1 {
                                pv = ProofVariables::new();
                            }
                        }
                        if row[row.len() - 1] == 6 {
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
                            || Ok(F::from(row[row.len() - NOT_FIRST_LEVEL_POS] as u64)),
                        )?;

                        let l = row.len();
                        let s_root_rlc = bytes_into_rlc(
                            &row[l - 4 * HASH_WIDTH - COUNTER_WITNESS_LEN - IS_NON_EXISTING_ACCOUNT_POS
                                ..l - 4 * HASH_WIDTH - COUNTER_WITNESS_LEN - IS_NON_EXISTING_ACCOUNT_POS
                                    + HASH_WIDTH],
                            self.acc_r,
                        );
                        let c_root_rlc = bytes_into_rlc(
                            &row[l - 3 * HASH_WIDTH - COUNTER_WITNESS_LEN - IS_NON_EXISTING_ACCOUNT_POS
                                ..l - 3 * HASH_WIDTH - COUNTER_WITNESS_LEN - IS_NON_EXISTING_ACCOUNT_POS
                                    + HASH_WIDTH],
                            self.acc_r,
                        );
                        region.assign_advice(
                            || "inter start root",
                            self.inter_start_root,
                            offset,
                            || Ok(s_root_rlc),
                        )?;
                        region.assign_advice(
                            || "inter final root",
                            self.inter_final_root,
                            offset,
                            || Ok(c_root_rlc),
                        )?;

                        if pv.before_account_leaf {
                            region.assign_advice(
                                || "address RLC",
                                self.address_rlc,
                                offset,
                                || Ok(F::zero()),
                            )?;
                        } else {
                            // address_rlc can be set only in account leaf row - this is to
                            // prevent omitting account proof (and having only storage proof
                            // with the appropriate address_rlc)
                            let address_rlc = bytes_into_rlc(
                                &row[l - 2 * HASH_WIDTH - COUNTER_WITNESS_LEN - IS_NON_EXISTING_ACCOUNT_POS
                                    ..l - 2 * HASH_WIDTH
                                        - COUNTER_WITNESS_LEN
                                        - IS_NON_EXISTING_ACCOUNT_POS
                                        + HASH_WIDTH],
                                self.acc_r,
                            );
                            region.assign_advice(
                                || "address RLC",
                                self.address_rlc,
                                offset,
                                || Ok(address_rlc),
                            )?;
                        }

                        let counter_u32: u32 = u32::from_be_bytes(
                            row[l - HASH_WIDTH - COUNTER_WITNESS_LEN - IS_NON_EXISTING_ACCOUNT_POS
                                ..l - HASH_WIDTH - COUNTER_WITNESS_LEN - IS_NON_EXISTING_ACCOUNT_POS
                                    + COUNTER_WITNESS_LEN]
                                .try_into()
                                .expect("slice of incorrect length"),
                        );
                        region.assign_advice(
                            || "counter",
                            self.counter,
                            offset,
                            || Ok(F::from(counter_u32 as u64)),
                        )?;

                        region.assign_advice(
                            || "is_storage_mod",
                            self.proof_type.is_storage_mod,
                            offset,
                            || Ok(F::from(row[row.len() - IS_STORAGE_MOD_POS] as u64)),
                        )?;
                        region.assign_advice(
                            || "is_nonce_mod",
                            self.proof_type.is_nonce_mod,
                            offset,
                            || Ok(F::from(row[row.len() - IS_NONCE_MOD_POS] as u64)),
                        )?;
                        region.assign_advice(
                            || "is_balance_mod",
                            self.proof_type.is_balance_mod,
                            offset,
                            || Ok(F::from(row[row.len() - IS_BALANCE_MOD_POS] as u64)),
                        )?;
                        region.assign_advice(
                            || "is_account_delete_mod",
                            self.proof_type.is_account_delete_mod,
                            offset,
                            || Ok(F::from(row[row.len() - IS_ACCOUNT_DELETE_MOD_POS] as u64)),
                        )?;
                        region.assign_advice(
                            || "is_non_existing_account",
                            self.proof_type.is_non_existing_account_proof,
                            offset,
                            || Ok(F::from(row[row.len() - IS_NON_EXISTING_ACCOUNT_POS] as u64)),
                        )?;

                        if row[row.len() - 1] == 0 {
                            // branch init
                            pv.modified_node = row[BRANCH_0_KEY_POS];
                            pv.node_index = 0;
                            pv.drifted_pos = row[DRIFTED_POS];

                            // Get the child that is being changed and convert it to words to enable
                            // lookups:
                            let mut s_hash = witness[ind + 1 + pv.modified_node as usize]
                                [S_START..S_START + HASH_WIDTH]
                                .to_vec();
                            let mut c_hash = witness[ind + 1 + pv.modified_node as usize]
                                [C_START..C_START + HASH_WIDTH]
                                .to_vec();
                            pv.s_mod_node_hash_rlc = bytes_into_rlc(&s_hash, self.acc_r);
                            pv.c_mod_node_hash_rlc = bytes_into_rlc(&c_hash, self.acc_r);

                            if row[IS_BRANCH_S_PLACEHOLDER_POS] == 1 {
                                // We put hash of a node that moved down to the added branch.
                                // This is needed to check the hash of leaf_in_added_branch.
                                s_hash = witness[ind + 1 + pv.drifted_pos as usize]
                                    [S_START..S_START + HASH_WIDTH]
                                    .to_vec();
                                pv.s_mod_node_hash_rlc = bytes_into_rlc(&s_hash, self.acc_r);
                                pv.is_branch_s_placeholder = true
                            } else {
                                pv.is_branch_s_placeholder = false
                            }
                            if row[IS_BRANCH_C_PLACEHOLDER_POS] == 1 {
                                c_hash = witness[ind + 1 + pv.drifted_pos as usize]
                                    [C_START..C_START + HASH_WIDTH]
                                    .to_vec();
                                pv.c_mod_node_hash_rlc = bytes_into_rlc(&c_hash, self.acc_r);
                                pv.is_branch_c_placeholder = true
                            } else {
                                pv.is_branch_c_placeholder = false
                            }
                            // If no placeholder branch, we set drifted_pos = modified_node. This
                            // is needed just to make some other constraints (s_mod_node_hash_rlc
                            // and c_mod_node_hash_rlc correspond to the proper node) easier to
                            // write.
                            if row[IS_BRANCH_S_PLACEHOLDER_POS] == 0
                                && row[IS_BRANCH_C_PLACEHOLDER_POS] == 0
                            {
                                pv.drifted_pos = pv.modified_node
                            }

                            region.assign_fixed(
                                || "q_enable",
                                self.q_enable,
                                offset,
                                || Ok(F::one()),
                            )?;

                            self.assign_branch_init(
                                &mut region,
                                &row[0..row.len() - 1].to_vec(),
                                offset,
                            )?;

                            // reassign (it was assigned to 0 in assign_row) branch_acc and
                            // branch_mult to proper values

                            // Branch (length 83) with two bytes of RLP meta data
                            // [248,81,128,128,...

                            // Branch (length 340) with three bytes of RLP meta data
                            // [249,1,81,128,16,...

                            pv.acc_s = F::from(row[BRANCH_0_S_START] as u64);
                            pv.acc_mult_s = self.acc_r;

                            if row[BRANCH_0_S_START] == 249 {
                                pv.acc_s += F::from(row[BRANCH_0_S_START + 1] as u64) * pv.acc_mult_s; 
                                pv.acc_mult_s *= self.acc_r;
                                pv.acc_s +=
                                    F::from(row[BRANCH_0_S_START + 2] as u64) * pv.acc_mult_s;
                                pv.acc_mult_s *= self.acc_r;

                                pv.rlp_len_rem_s = row[BRANCH_0_S_START + 1] as i32 * 256
                                    + row[BRANCH_0_S_START + 2] as i32;
                            } else if row[BRANCH_0_S_START] == 248 {
                                pv.acc_s += F::from(row[BRANCH_0_S_START + 1] as u64) * pv.acc_mult_s; 
                                pv.acc_mult_s *= self.acc_r;

                                pv.rlp_len_rem_s = row[BRANCH_0_S_START + 1] as i32;
                            } else {
                                pv.rlp_len_rem_s = row[BRANCH_0_S_START] as i32 - 192;
                            }

                            pv.acc_c = F::from(row[BRANCH_0_C_START] as u64);
                            pv.acc_mult_c = self.acc_r;

                            if row[BRANCH_0_C_START] == 249 {
                                pv.acc_c += F::from(row[BRANCH_0_C_START + 1] as u64) * pv.acc_mult_c;
                                pv.acc_mult_c *= self.acc_r;
                                pv.acc_c +=
                                    F::from(row[BRANCH_0_C_START + 2] as u64) * pv.acc_mult_c;
                                pv.acc_mult_c *= self.acc_r;

                                pv.rlp_len_rem_c = row[BRANCH_0_C_START + 1] as i32 * 256
                                    + row[BRANCH_0_C_START + 2] as i32;
                            } else if row[BRANCH_0_C_START] == 248 {
                                pv.acc_c += F::from(row[BRANCH_0_C_START + 1] as u64) * pv.acc_mult_c;
                                pv.acc_mult_c *= self.acc_r;

                                pv.rlp_len_rem_c = row[BRANCH_0_C_START + 1] as i32;
                            } else {
                                pv.rlp_len_rem_c = row[BRANCH_0_C_START] as i32 - 192;
                            }

                            self.assign_acc(
                                &mut region,
                                pv.acc_s,
                                pv.acc_mult_s,
                                pv.acc_c,
                                pv.acc_mult_c,
                                offset,
                            )?;

                            // Note that if the last branch is placeholder,
                            pv.is_even = witness[offset][IS_EXT_LONG_EVEN_C16_POS]
                                + witness[offset][IS_EXT_LONG_EVEN_C1_POS]
                                == 1;
                            pv.is_odd = witness[offset][IS_EXT_LONG_ODD_C16_POS]
                                + witness[offset][IS_EXT_LONG_ODD_C1_POS]
                                + witness[offset][IS_EXT_SHORT_C16_POS]
                                + witness[offset][IS_EXT_SHORT_C1_POS]
                                == 1;
                            pv.is_short = witness[offset][IS_EXT_SHORT_C16_POS]
                                + witness[offset][IS_EXT_SHORT_C1_POS]
                                == 1;
                            pv.is_long = witness[offset][IS_EXT_LONG_EVEN_C16_POS]
                                + witness[offset][IS_EXT_LONG_EVEN_C1_POS]
                                + witness[offset][IS_EXT_LONG_ODD_C16_POS]
                                + witness[offset][IS_EXT_LONG_ODD_C1_POS]
                                == 1;
                            pv.is_extension_node = pv.is_even == true || pv.is_odd == true;
                            // end of extension node

                            offset += 1;
                        } else if row[row.len() - 1] == 1 {
                            // branch child
                            region.assign_fixed(
                                || "q_enable",
                                self.q_enable,
                                offset,
                                || Ok(F::one()),
                            )?;

                            let mut node_mult_diff_s = F::one();
                            let mut node_mult_diff_c = F::one();
                            
                            if row[S_RLP_START + 1] == 160 {
                                pv.rlp_len_rem_s -= 33;
                            } else if row[S_RLP_START + 1] == 0 && row[S_START] > 192 {
                                let len = row[S_START] as i32 - 192;
                                pv.rlp_len_rem_s -= len + 1;
                                for _ in 0..len {
                                    node_mult_diff_s *= self.acc_r;
                                }
                            } else if row[S_RLP_START + 1] == 0 {
                                pv.rlp_len_rem_s -= 1;
                            }
                            if row[C_RLP_START + 1] == 160 {
                                pv.rlp_len_rem_c -= 33;
                            } else if row[C_RLP_START + 1] == 0 && row[C_START] > 192 {
                                let len = row[C_START] as i32 - 192;
                                pv.rlp_len_rem_c -= len + 1;
                                for _ in 0..len {
                                    node_mult_diff_c *= self.acc_r;
                                }
                            } else if row[C_RLP_START + 1] == 0 {
                                pv.rlp_len_rem_c -= 1;
                            }

                            region.assign_advice(
                                || "node_mult_diff_s".to_string(),
                                self.node_mult_diff_s,
                                offset,
                                || Ok(node_mult_diff_s),
                            )?;
                            region.assign_advice(
                                || "node_mult_diff_c".to_string(),
                                self.node_mult_diff_c,
                                offset,
                                || Ok(node_mult_diff_c),
                            )?;

                            if pv.node_index == 0 {
                                // If it's not extension node, rlc and rlc_mult in extension row
                                // will be the same as for branch rlc.
                                pv.extension_node_rlc = pv.key_rlc;

                                pv.key_rlc_prev = pv.key_rlc;
                                pv.key_rlc_mult_prev = pv.key_rlc_mult;

                                if pv.is_extension_node
                                // Extension node
                                // We need nibbles here to be able to compute key RLC
                                {
                                    // For key RLC, we need to first take into account
                                    // extension node key.
                                    // witness[offset + 16]
                                    let ext_row = &witness[ind + 16];
                                    let mut key_len_pos = 1;
                                    if ext_row[0] == 248 {
                                        key_len_pos = 2;
                                    }

                                    if pv.key_rlc_sel {
                                        // Note: it can't be is_even = 1 && is_short = 1.
                                        if pv.is_even && pv.is_long {
                                            // extension node part:
                                            let key_len = ext_row[key_len_pos] as usize - 128 - 1; // -1 because the first byte is 0 (is_even)
                                            self.compute_acc_and_mult(
                                                ext_row,
                                                &mut pv.extension_node_rlc,
                                                &mut pv.key_rlc_mult,
                                                key_len_pos + 2, /* first position behind key_len_pos
                                                    * is 0 (because is_even), we start
                                                    * with the next one */
                                                key_len,
                                            );
                                            pv.mult_diff = F::one();
                                            for _ in 0..key_len {
                                                pv.mult_diff *= self.acc_r;
                                            }
                                            pv.key_rlc = pv.extension_node_rlc;
                                            // branch part:
                                            pv.key_rlc += F::from(pv.modified_node as u64)
                                                * F::from(16)
                                                * pv.key_rlc_mult;
                                            // key_rlc_mult stays the same
                                            pv.key_rlc_sel = !pv.key_rlc_sel;
                                        } else if pv.is_odd && pv.is_long {
                                            // extension node part:
                                            pv.extension_node_rlc +=
                                                F::from((ext_row[key_len_pos + 1] - 16) as u64)
                                                    * F::from(16)
                                                    * pv.key_rlc_mult;

                                            let ext_row_c = &witness[ind + 17];
                                            let key_len = ext_row[key_len_pos] as usize - 128;

                                            pv.mult_diff = F::one();
                                            for k in 0..key_len-1 {
                                                let second_nibble = ext_row_c[S_START + k];
                                                let first_nibble =
                                                    (ext_row[key_len_pos + 2 + k] - second_nibble) / 16;
                                                assert_eq!(
                                                    first_nibble * 16 + second_nibble,
                                                    ext_row[key_len_pos + 2 + k],
                                                );
                                                pv.extension_node_rlc +=
                                                    F::from(first_nibble as u64) * pv.key_rlc_mult;

                                                pv.key_rlc_mult *= self.acc_r;
                                                pv.mult_diff *= self.acc_r;

                                                pv.extension_node_rlc +=
                                                    F::from(second_nibble as u64)
                                                        * F::from(16)
                                                        * pv.key_rlc_mult;
                                            }

                                            pv.key_rlc = pv.extension_node_rlc;
                                            // branch part:
                                            pv.key_rlc +=
                                                F::from(pv.modified_node as u64) * pv.key_rlc_mult;
                                            pv.key_rlc_mult *= self.acc_r;
                                        } else if pv.is_short {
                                            pv.extension_node_rlc +=
                                                F::from((ext_row[1] - 16) as u64)
                                                    * F::from(16)
                                                    * pv.key_rlc_mult;
                                            pv.key_rlc = pv.extension_node_rlc;
                                            // branch part:
                                            pv.key_rlc +=
                                                F::from(pv.modified_node as u64) * pv.key_rlc_mult;
                                            pv.key_rlc_mult *= self.acc_r;
                                            pv.mult_diff = self.acc_r;
                                        }
                                    } else {
                                        if pv.is_even && pv.is_long {
                                            // extension node part:
                                            let ext_row_c = &witness[ind + 17];
                                            let key_len = ext_row[key_len_pos] as usize - 128 - 1; // -1 because the first byte is 0 (is_even)

                                            pv.mult_diff = F::one();
                                            for k in 0..key_len {
                                                let second_nibble = ext_row_c[S_START + k];
                                                let first_nibble =
                                                    (ext_row[key_len_pos + 2 + k] - second_nibble) / 16;
                                                assert_eq!(
                                                    first_nibble * 16 + second_nibble,
                                                    ext_row[key_len_pos + 2 + k],
                                                );
                                                pv.extension_node_rlc +=
                                                    F::from(first_nibble as u64) * pv.key_rlc_mult;

                                                pv.key_rlc_mult *= self.acc_r;
                                                pv.mult_diff *= self.acc_r;

                                                pv.extension_node_rlc += F::from(16)
                                                    * F::from(second_nibble as u64)
                                                    * pv.key_rlc_mult;
                                            }

                                            pv.key_rlc = pv.extension_node_rlc;
                                            // branch part:
                                            pv.key_rlc +=
                                                F::from(pv.modified_node as u64) * pv.key_rlc_mult;
                                            pv.key_rlc_mult *= self.acc_r;
                                            pv.key_rlc_sel = !pv.key_rlc_sel;
                                        } else if pv.is_odd && pv.is_long {
                                            pv.extension_node_rlc +=
                                                F::from((ext_row[key_len_pos + 1] - 16) as u64) * pv.key_rlc_mult;

                                            pv.key_rlc_mult *= self.acc_r;

                                            let key_len = ext_row[key_len_pos] as usize - 128;

                                            self.compute_acc_and_mult(
                                                ext_row,
                                                &mut pv.extension_node_rlc,
                                                &mut pv.key_rlc_mult,
                                                key_len_pos + 2, /* the first position after key_len_pos
                                                    * is single nibble which is taken into
                                                    * account above, we start
                                                    * with fourth */
                                                key_len - 1, // one byte is occupied by single nibble
                                            );
                                            pv.mult_diff = F::one();
                                            for _ in 0..key_len {
                                                pv.mult_diff *= self.acc_r;
                                            }
                                            pv.key_rlc = pv.extension_node_rlc;
                                            // branch part:
                                            pv.key_rlc += F::from(pv.modified_node as u64)
                                                * F::from(16)
                                                * pv.key_rlc_mult;
                                            // key_rlc_mult stays the same
                                        } else if pv.is_short {
                                            pv.extension_node_rlc +=
                                                F::from((ext_row[1] - 16) as u64) * pv.key_rlc_mult;

                                            pv.key_rlc = pv.extension_node_rlc;

                                            pv.key_rlc_mult *= self.acc_r;
                                            // branch part:
                                            pv.key_rlc += F::from(pv.modified_node as u64)
                                                * F::from(16)
                                                * pv.key_rlc_mult;
                                            pv.mult_diff = self.acc_r;
                                        }
                                    }
                                } else {
                                    if pv.key_rlc_sel {
                                        pv.key_rlc += F::from(pv.modified_node as u64)
                                            * F::from(16)
                                            * pv.key_rlc_mult;
                                        // key_rlc_mult stays the same
                                    } else {
                                        pv.key_rlc +=
                                            F::from(pv.modified_node as u64) * pv.key_rlc_mult;
                                        pv.key_rlc_mult *= self.acc_r;
                                    }
                                    pv.key_rlc_sel = !pv.key_rlc_sel;
                                }
                                self.assign_branch_row(
                                    &mut region,
                                    pv.node_index,
                                    pv.modified_node,
                                    pv.key_rlc,
                                    pv.key_rlc_mult,
                                    pv.mult_diff,
                                    &row[0..row.len() - 1].to_vec(),
                                    pv.s_mod_node_hash_rlc,
                                    pv.c_mod_node_hash_rlc,
                                    pv.drifted_pos,
                                    pv.rlp_len_rem_s,
                                    pv.rlp_len_rem_c,
                                    offset,
                                )?;
                            } else {
                                // Note that key_rlc and key_rlc_mult are set the same in all
                                // branch children to avoid some rotations - constraint for this
                                // equality is in extension_node_key.
                                self.assign_branch_row(
                                    &mut region,
                                    pv.node_index,
                                    pv.modified_node,
                                    pv.key_rlc,
                                    pv.key_rlc_mult,
                                    pv.mult_diff,
                                    &row[0..row.len() - 1].to_vec(),
                                    pv.s_mod_node_hash_rlc,
                                    pv.c_mod_node_hash_rlc,
                                    pv.drifted_pos,
                                    pv.rlp_len_rem_s,
                                    pv.rlp_len_rem_c,
                                    offset,
                                )?;
                            }
                            // sel1 is to distinguish whether the S node is empty.
                            // sel2 is to distinguish whether the C node is empty.
                            // Note that 128 comes from the RLP byte denoting empty leaf.
                            // Having 128 for *_mod_node_hash_rlc means there is no node at
                            // this position in branch - for example,
                            // s_mode_node_hash_rlc = 128 and c_words is some other value
                            // when new value is added to the trie
                            // (as opposed to just updating the value).
                            // Note that there is a potential attack if a leaf node
                            // is found with hash [128, 0, ..., 0],
                            // but the probability is negligible.
                            let mut sel1 = F::zero();
                            let mut sel2 = F::zero();
                            if pv.s_mod_node_hash_rlc == F::from(128 as u64) {
                                sel1 = F::one();
                            }
                            if pv.c_mod_node_hash_rlc == F::from(128 as u64) {
                                sel2 = F::one();
                            }

                            region.assign_advice(
                                || "assign sel1".to_string(),
                                self.sel1,
                                offset,
                                || Ok(sel1),
                            )?;
                            region.assign_advice(
                                || "assign sel2".to_string(),
                                self.sel2,
                                offset,
                                || Ok(sel2),
                            )?;

                            // reassign (it was assigned to 0 in assign_row) branch_acc and
                            // branch_mult to proper values

                            // We need to distinguish between empty and non-empty node:
                            // empty node at position 1: 0
                            // non-empty node at position 1: 160

                            let c128 = F::from(128_u64);
                            let c160 = F::from(160_u64);

                            let compute_branch_acc_and_mult =
                                |branch_acc: &mut F,
                                 branch_mult: &mut F,
                                 rlp_start: usize,
                                 start: usize| {
                                    if row[rlp_start + 1] == 0 && row[start] == 128 {
                                        *branch_acc += c128 * *branch_mult;
                                        *branch_mult *= self.acc_r;
                                    } else if row[rlp_start + 1] == 160 {
                                        *branch_acc += c160 * *branch_mult;
                                        *branch_mult *= self.acc_r;
                                        for i in 0..HASH_WIDTH {
                                            *branch_acc +=
                                                F::from(row[start + i] as u64) * *branch_mult;
                                            *branch_mult *= self.acc_r;
                                        }
                                    } else {
                                        *branch_acc += F::from(row[start] as u64) * *branch_mult;
                                        *branch_mult *= self.acc_r;
                                        let len = row[start] as usize - 192;
                                        for i in 0..len {
                                            *branch_acc +=
                                                F::from(row[start + 1 + i] as u64) * *branch_mult;
                                            *branch_mult *= self.acc_r;
                                        }
                                    }
                                };

                            // TODO: add branch ValueNode info

                            compute_branch_acc_and_mult(
                                &mut pv.acc_s,
                                &mut pv.acc_mult_s,
                                S_RLP_START,
                                S_START,
                            );
                            compute_branch_acc_and_mult(
                                &mut pv.acc_c,
                                &mut pv.acc_mult_c,
                                C_RLP_START,
                                C_START,
                            );
                            self.assign_acc(
                                &mut region,
                                pv.acc_s,
                                pv.acc_mult_s,
                                pv.acc_c,
                                pv.acc_mult_c,
                                offset,
                            )?;

                            // This is to avoid Poisoned Constraint in extension_node_key.
                            region.assign_advice(
                                || "assign key_rlc".to_string(),
                                self.key_rlc,
                                offset,
                                || Ok(pv.key_rlc),
                            )?;
                            region.assign_advice(
                                || "assign key_rlc_mult".to_string(),
                                self.key_rlc_mult,
                                offset,
                                || Ok(pv.key_rlc_mult),
                            )?;

                            offset += 1;
                            pv.node_index += 1;
                        } else {
                            // leaf s or leaf c or leaf key s or leaf key c
                            region.assign_fixed(
                                || "q_enable",
                                self.q_enable,
                                offset,
                                || Ok(F::one()),
                            )?;
                            
                            let mut account_leaf = AccountLeaf::default();
                            let mut storage_leaf = StorageLeaf::default();

                            let mut is_extension_node_s = false;
                            let mut is_extension_node_c = false;

                            if row[row.len() - 1] == 2 {
                                storage_leaf.is_s_key = true;
                            } else if row[row.len() - 1] == 3 {
                                storage_leaf.is_c_key = true;
                            } else if row[row.len() - 1] == 6 {
                                account_leaf.is_key_s = true;
                            } else if row[row.len() - 1] == 4 {
                                account_leaf.is_key_c = true;
                            } else if row[row.len() - 1] == 7 {
                                account_leaf.is_nonce_balance_s = true;
                            } else if row[row.len() - 1] == 8 {
                                account_leaf.is_nonce_balance_c = true;
                            } else if row[row.len() - 1] == 9 {
                                account_leaf.is_storage_codehash_s = true;
                            } else if row[row.len() - 1] == 11 {
                                account_leaf.is_storage_codehash_c = true;
                            } else if row[row.len() - 1] == 10 {
                                account_leaf.is_in_added_branch = true;
                                pv.key_rlc = F::zero(); // account address until here, storage key from here on
                                pv.key_rlc_mult = F::one();
                                pv.key_rlc_prev = F::zero();
                                pv.key_rlc_mult_prev = F::one();
                                pv.key_rlc_sel = true;
                                // TODO: check whether all constraints are implemented (extension_node_rlc ...)
                            } else if row[row.len() - 1] == 13 {
                                storage_leaf.is_s_value = true;
                            } else if row[row.len() - 1] == 14 {
                                storage_leaf.is_c_value = true;
                            } else if row[row.len() - 1] == 15 {
                                storage_leaf.is_in_added_branch = true;
                            } else if row[row.len() - 1] == 16 {
                                is_extension_node_s = true;
                            } else if row[row.len() - 1] == 17 {
                                is_extension_node_c = true;
                            } else if row[row.len() - 1] == 18 {
                                account_leaf.is_non_existing_account_row = true;
                            }

                            self.assign_row(
                                &mut region,
                                &row[0..row.len() - 1].to_vec(),
                                false,
                                false,
                                false,
                                0,
                                0,
                                account_leaf,
                                storage_leaf,
                                0,
                                is_extension_node_s,
                                is_extension_node_c,
                                offset,
                            )?;

                            let assign_long_short = |region: &mut Region<'_, F>, typ: &str| {
                                let mut flag1 = false;
                                let mut flag2 = false;
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
                                        self.s_mod_node_hash_rlc,
                                        offset,
                                        || Ok(F::from(flag1 as u64)),
                                    )
                                    .ok();
                                region
                                    .assign_advice(
                                        || "assign c_modified_node_rlc".to_string(),
                                        self.c_mod_node_hash_rlc,
                                        offset,
                                        || Ok(F::from(flag2 as u64)),
                                    )
                                    .ok();
                            };

                            let compute_key_rlc =
                                |key_rlc: &mut F, key_rlc_mult: &mut F, start: usize| {
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
                                };

                            // Storage leaf key
                            if row[row.len() - 1] == 2 || row[row.len() - 1] == 3 {
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
                                if witness[ind][0] == 248 {
                                    typ = "long";
                                } else if witness[ind][1] == 32 {
                                    typ = "last_level";
                                }
                                assign_long_short(&mut region, typ);

                                pv.acc_s = F::zero();
                                pv.acc_mult_s = F::one();
                                let len: usize;
                                if typ == "long" {
                                    len = (row[2] - 128) as usize + 3;
                                } else if typ == "short" {
                                    len = (row[1] - 128) as usize + 2;
                                } else {
                                    // last_level
                                    len = 2;
                                }
                                self.compute_acc_and_mult(
                                    row,
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
                                if row[0] < 223 { // when shorter than 32 bytes, the node doesn't get hashed
                                    // not_hashed
                                    region.assign_advice(
                                        || "assign not_hashed".to_string(),
                                        self.acc_c,
                                        offset,
                                        || Ok(F::one()),
                                    )?;
                                }

                                // TODO: handle if branch or extension node is added
                                let mut start = S_START - 1;
                                if row[0] == 248 {
                                    // long RLP
                                    start = S_START;
                                }

                                // For leaf S and leaf C we need to start with the same rlc.
                                let mut key_rlc_new = pv.key_rlc;
                                let mut key_rlc_mult_new = pv.key_rlc_mult;
                                if (pv.is_branch_s_placeholder && row[row.len() - 1] == 2)
                                    || (pv.is_branch_c_placeholder && row[row.len() - 1] == 3)
                                {
                                    key_rlc_new = pv.key_rlc_prev;
                                    key_rlc_mult_new = pv.key_rlc_mult_prev;
                                }
                                if typ != "last_level" {
                                    // If in last level, the key RLC is already computed.
                                    compute_key_rlc(&mut key_rlc_new, &mut key_rlc_mult_new, start);
                                }
                                region.assign_advice(
                                    || "assign key_rlc".to_string(),
                                    self.key_rlc,
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
                                    self.sel1,
                                    offset,
                                    || Ok(pv.key_rlc_prev),
                                )?;
                                region.assign_advice(
                                    || "assign key_rlc_mult".to_string(),
                                    self.sel2,
                                    offset,
                                    || Ok(pv.key_rlc_mult_prev),
                                )?;
                            }

                            if row[row.len() - 1] == 13 || row[row.len() - 1] == 14 {
                                // Info whether leaf value is 1 byte or more:
                                let mut is_long = false;
                                let row_prev = &witness[ind - 1];
                                if row_prev[0] == 248 {
                                    // whole leaf is in long format (3 RLP meta bytes)
                                    let key_len = row_prev[2] - 128;
                                    if row_prev[1] - key_len - 1 > 1 {
                                        is_long = true;
                                    }
                                } else if row_prev[1] == 32 {
                                    // last level
                                    let leaf_len = row_prev[0] - 192;
                                    if leaf_len - 1 > 1 {
                                        is_long = true;
                                    }
                                } else {
                                    let leaf_len = row_prev[0] - 192;
                                    let key_len = row_prev[1] - 128;
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
                                    row,
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
                                    row,
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
                                if row[row.len() - 1] == 13 {
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
                                    if row_prev[row_prev.len() - 1] == 9
                                        && row_prev[S_START..S_START + HASH_WIDTH]
                                            == empty_trie_hash
                                    {
                                        // Leaf is without branch and it is just a placeholder.
                                        region.assign_advice(
                                            || "assign sel1".to_string(),
                                            self.sel1,
                                            offset,
                                            || Ok(F::one()),
                                        )?;
                                    }
                                } else if row[row.len() - 1] == 14 {
                                    region.assign_advice(
                                        || "assign key_rlc into key_rlc_mult".to_string(),
                                        self.key_rlc_mult,
                                        offset,
                                        || Ok(pv.rlc2),
                                    )?;
                                    region.assign_advice(
                                        || "assign leaf value S into mult_diff".to_string(),
                                        self.mult_diff,
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
                                    if row_prev[row_prev.len() - 1] == 11
                                        && row_prev[S_START..S_START + HASH_WIDTH]
                                            == empty_trie_hash
                                    {
                                        // Leaf is without branch and it is just a placeholder.
                                        region.assign_advice(
                                            || "assign sel2".to_string(),
                                            self.sel2,
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

                            if row[row.len() - 1] == 6 || row[row.len() - 1] == 4 {
                                // account leaf key S & C
                                let mut acc = F::zero();
                                let mut acc_mult = F::one();
                                // 35 = 2 (leaf rlp) + 1 (key rlp) + key_len
                                let key_len = (row[2] - 128) as usize;
                                for b in row.iter().take(3 + key_len) {
                                    acc += F::from(*b as u64) * acc_mult;
                                    acc_mult *= self.acc_r;
                                }
                                // Assigning acc_s, acc_mult_s below together with acc_c
                                // (key_rlc_prev) and acc_c_mult
                                // (key_rlc_mult_prev).

                                if row[row.len() - 1] == 6 {
                                    pv.acc_account_s = acc;
                                    pv.acc_mult_account_s = acc_mult
                                } else {
                                    pv.acc_account_c = acc;
                                    pv.acc_mult_account_c = acc_mult
                                }

                                // For leaf S and leaf C we need to start with the same rlc.
                                let mut key_rlc_new = pv.key_rlc;
                                let mut key_rlc_mult_new = pv.key_rlc_mult;
                                if (pv.is_branch_s_placeholder && row[row.len() - 1] == 6)
                                    || (pv.is_branch_c_placeholder && row[row.len() - 1] == 4)
                                {
                                    key_rlc_new = pv.key_rlc_prev;
                                    key_rlc_mult_new = pv.key_rlc_mult_prev;
                                }
                                compute_key_rlc(&mut key_rlc_new, &mut key_rlc_mult_new, S_START);
                                region.assign_advice(
                                    || "assign key_rlc".to_string(),
                                    self.key_rlc,
                                    offset,
                                    || Ok(key_rlc_new),
                                )?;

                                // Assign previous key RLC and mult in acc_c and acc_c_mult - don't
                                // use sel1/sel2 here (as in storage leaf case) as sel1/sel2 is
                                // used for whether nonce/balance is short/long (in nonce balance
                                // row, see offset - 1).
                                // Constraints for previous key RLC are in account_leaf_key.
                                self.assign_acc(
                                    &mut region,
                                    acc,
                                    acc_mult,
                                    pv.key_rlc_prev,
                                    pv.key_rlc_mult_prev,
                                    offset,
                                )?;
                            } else if row[row.len() - 1] == 7 || row[row.len() - 1] == 8 {
                                self.account_leaf_nonce_balance_config_s.assign(&mut region, self, &mut pv, row, offset);
                            } else if row[row.len() - 1] == 9 || row[row.len() - 1] == 11 {
                                if row[row.len() - 1] == 9 {
                                    pv.acc_s = pv.acc_nonce_balance_s;
                                    pv.acc_mult_s = pv.acc_mult_nonce_balance_s;

                                    // storage root RLC and code hash RLC
                                    pv.rlc1 = F::zero();
                                    pv.rlc2 = F::zero();
                                    self.compute_rlc_and_assign(&mut region, row, &mut pv, offset, S_START, C_START, HASH_WIDTH, HASH_WIDTH);
                                } else {
                                    pv.acc_s = pv.acc_nonce_balance_c;
                                    pv.acc_mult_s = pv.acc_mult_nonce_balance_c;

                                    // assign storage root S
                                    region.assign_advice(
                                        || "assign sel1".to_string(),
                                        self.sel1,
                                        offset,
                                        || Ok(pv.rlc1),
                                    )?;
                                    // assign code hash S
                                    region.assign_advice(
                                        || "assign sel2".to_string(),
                                        self.sel2,
                                        offset,
                                        || Ok(pv.rlc2),
                                    )?;

                                    // assign storage root RLC and code hash RLC for this row
                                    pv.rlc1 = F::zero();
                                    pv.rlc2 = F::zero();
                                    self.compute_rlc_and_assign(&mut region, row, &mut pv, offset, S_START, C_START, HASH_WIDTH, HASH_WIDTH);
                                }
                                // storage
                                self.compute_acc_and_mult(
                                    row,
                                    &mut pv.acc_s,
                                    &mut pv.acc_mult_s,
                                    S_START - 1,
                                    HASH_WIDTH + 1,
                                );
                                // code hash
                                self.compute_acc_and_mult(
                                    row,
                                    &mut pv.acc_s,
                                    &mut pv.acc_mult_s,
                                    C_START - 1,
                                    HASH_WIDTH + 1,
                                );
                                self.assign_acc(
                                    &mut region,
                                    pv.acc_s,
                                    pv.acc_mult_s,
                                    F::zero(),
                                    F::zero(),
                                    offset,
                                )?;
                            } else if row[row.len() - 1] == 15 && row[1] != 0 {
                                // row[1] != 0 just to avoid usize problems below (when row doesn't
                                // need to be assigned) Info whether
                                // leaf rlp is long or short.
                                let mut typ = "short";
                                if witness[ind][0] == 248 {
                                    typ = "long";
                                } else if witness[ind][1] == 32 {
                                    typ = "last_level";
                                }
                                assign_long_short(&mut region, typ);

                                pv.acc_s = F::zero();
                                pv.acc_mult_s = F::one();
                                let len: usize;
                                if row[0] == 248 {
                                    len = (row[2] - 128) as usize + 3;
                                } else {
                                    len = (row[1] - 128) as usize + 2;
                                }
                                self.compute_acc_and_mult(
                                    row,
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
                            } else if row[row.len() - 1] == 16 {
                                if pv.is_extension_node {
                                  	// [228,130,0,149,160,114,253,150,133,18,192,156,19,241,162,51,210,24,1,151,16,48,7,177,42,60,49,34,230,254,242,79,132,165,90,75,249]
                                  	// [226,16,160,172,105,12...
                                   	// [247,160,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,213,128,194,32,1,128,194,32,1,128,128,128,128,128,128,128,128,128,128,128,128,128]
                                   	// [248,58,159,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,217,128,196,130,32,0,1,128,196,130,32,0,1,128,128,128,128,128,128,128,128,128,128,128,128,128]

                                    // Intermediate RLC value and mult (after key)
                                    // to know which mult we need to use in c_advices.
                                    pv.acc_s = F::zero();
                                    pv.acc_mult_s = F::one();
                                    let len: usize;
                                    if row[0] == 226 {
                                        // key length is 1
                                        len = 2 // [226, key]
                                    } else if row[0] < 248 {
                                        len = (row[1] - 128) as usize + 2;
                                    } else {
                                        len = (row[2] - 128) as usize + 3;
                                    }
                                    self.compute_acc_and_mult(
                                        row,
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
                                    if row[C_RLP_START + 1] == 0 {
                                        // non-hashed branch in extension node
                                        start = C_START;
                                        len = HASH_WIDTH;
                                    }
                                    self.compute_acc_and_mult(
                                        row,
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
                                    self.key_rlc,
                                    offset,
                                    || Ok(pv.extension_node_rlc),
                                )?;
                            } else if row[row.len() - 1] == 17 {
                                if pv.is_extension_node {
                                    // We use intermediate value from previous row (because
                                    // up to acc_s it's about key and this is the same
                                    // for both S and C).
                                    pv.acc_c = pv.acc_s;
                                    pv.acc_mult_c = pv.acc_mult_s;
                                    let mut start = C_RLP_START + 1;
                                    let mut len = HASH_WIDTH + 1;
                                    if row[C_RLP_START + 1] == 0 {
                                        // non-hashed branch in extension node
                                        start = C_START;
                                        len = HASH_WIDTH;
                                    }
                                    self.compute_acc_and_mult(
                                        row,
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
                                    self.key_rlc,
                                    offset,
                                    || Ok(pv.extension_node_rlc),
                                )?;
                            } else if row[row.len() - 1] == 10 && row[1] != 0 {
                                // row[1] != 0 just to avoid usize problems below (when row doesn't
                                // need to be assigned).
                                pv.acc_s = F::zero();
                                pv.acc_mult_s = F::one();
                                let len = (row[2] - 128) as usize + 3;
                                self.compute_acc_and_mult(
                                    row,
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
                            } else if row[row.len() - 1] == 18 { 
                                let key_len = witness[offset-1][2] as usize - 128;
                                let row_prev = &witness[offset - 1];
                                let mut sum = F::zero();
                                let mut sum_prev = F::zero();
                                let mut mult = self.acc_r;
                                for i in 0..key_len {
                                    sum += F::from(row[3+i] as u64) * mult ;
                                    sum_prev += F::from(row_prev[3+i] as u64) * mult;
                                    mult *= self.acc_r;
                                }
                                let mut diff_inv = F::zero();
                                if sum != sum_prev {
                                    diff_inv = F::invert(&(sum - sum_prev)).unwrap();
                                }

                                region.assign_advice(
                                    || "assign sum".to_string(),
                                    self.key_rlc,
                                    offset,
                                    || Ok(sum),
                                )?;
                                region.assign_advice(
                                    || "assign sum prev".to_string(),
                                    self.key_rlc_mult,
                                    offset,
                                    || Ok(sum_prev),
                                )?;
                                region.assign_advice(
                                    || "assign diff inv".to_string(),
                                    self.acc_s,
                                    offset,
                                    || Ok(diff_inv),
                                )?;
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

                for row in self.witness.iter() {
                    if row[row.len() - 1] == 5 {
                        to_be_hashed.push(row[0..row.len() - 1].to_vec());
                    }
                }

                config.load(&mut layouter, to_be_hashed)?;
                config.assign(layouter, &self.witness);

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
