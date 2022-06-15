use halo2_proofs::{
    circuit::{Layouter, Region},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed},
    poly::Rotation,
};
use keccak256::plain::Keccak;
use eth_types::Field;
use std::convert::TryInto;

use crate::param::WITNESS_ROW_WIDTH;
use crate::param::{
    BRANCH_0_C_START, BRANCH_0_KEY_POS, BRANCH_0_S_START, C_RLP_START, C_START, DRIFTED_POS,
    HASH_WIDTH, IS_BRANCH_C_PLACEHOLDER_POS, IS_BRANCH_S_PLACEHOLDER_POS, KECCAK_INPUT_WIDTH,
    KECCAK_OUTPUT_WIDTH, S_RLP_START, S_START,
};
use crate::{
    branch_hash_in_parent::BranchHashInParentConfig,
    branch_rlc::BranchRLCConfig,
    branch_rlc_init::BranchRLCInitConfig,
    helpers::bytes_into_rlc,
    param::{COUNTER_WITNESS_LEN, IS_NON_EXISTING_ACCOUNT_POS, LAYOUT_OFFSET, NOT_FIRST_LEVEL_POS},
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
struct AccountLeafCols {
    is_account_leaf_key_s: Column<Advice>,
    is_account_leaf_key_c: Column<Advice>,
    is_account_leaf_nonce_balance_s: Column<Advice>,
    is_account_leaf_nonce_balance_c: Column<Advice>,
    is_account_leaf_storage_codehash_s: Column<Advice>,
    is_account_leaf_storage_codehash_c: Column<Advice>,
    is_account_leaf_in_added_branch: Column<Advice>,
}

#[derive(Default)]
struct AccountLeaf {
    is_account_leaf_key_s: bool,
    is_account_leaf_key_c: bool,
    is_account_leaf_nonce_balance_s: bool,
    is_account_leaf_nonce_balance_c: bool,
    is_account_leaf_storage_codehash_s: bool,
    is_account_leaf_storage_codehash_c: bool,
    is_account_leaf_in_added_branch: bool,
}

#[derive(Clone, Debug)]
struct StorageLeafCols {
    is_leaf_s: Column<Advice>,
    is_leaf_s_value: Column<Advice>,
    is_leaf_c: Column<Advice>,
    is_leaf_c_value: Column<Advice>,
    /** it is at drifted_pos position in added branch,
    * note that this row could be omitted when there
    * is no added branch but then it would open a
    * vulnerability because the attacker could omit
    * these row in cases when it's needed too (and
    * constraints happen in this row) */
    is_leaf_in_added_branch: Column<Advice>,
}

#[derive(Default)]
struct StorageLeaf {
    is_leaf_s: bool,
    is_leaf_s_value: bool,
    is_leaf_c: bool,
    is_leaf_c_value: bool,
    is_leaf_in_added_branch: bool,
}

#[derive(Clone, Debug)]
struct BranchCols {
    is_branch_init: Column<Advice>,
    is_branch_child: Column<Advice>,
    is_last_branch_child: Column<Advice>,
    node_index: Column<Advice>,
    is_modified: Column<Advice>,   // whether this branch node is modified
    modified_node: Column<Advice>, // index of the modified node
    is_at_drifted_pos: Column<Advice>, // needed when leaf is turned into branch
    drifted_pos: Column<Advice>,   /* needed when leaf is turned into branch - first nibble of
                                    * the key stored in a leaf (because the existing leaf will
                                    * jump to this position in added branch) */
    is_extension_node_s: Column<Advice>, /* contains extension node key (s_advices) and hash of
                                          * the branch (c_advices) */
    is_extension_node_c: Column<Advice>,
}

#[derive(Default)]
struct Branch {
    is_branch_init: bool,
    is_branch_child: bool,
    is_last_branch_child: bool,
    node_index: u8,
    is_modified: bool, 
    modified_node: u8,
    is_at_drifted_pos: bool,
    drifted_pos: u8,
    is_extension_node_s: bool,
    is_extension_node_c: bool,
}

#[derive(Clone, Debug)]
pub struct MPTConfig<F> {
    account_leaf: AccountLeafCols,
    storage_leaf: StorageLeafCols,
    q_enable: Column<Fixed>,
    q_not_first: Column<Fixed>, // not first row
    not_first_level: Column<Advice>,
    inter_start_root: Column<Advice>,
    inter_final_root: Column<Advice>, 
    branch: BranchCols,
    s_rlp1: Column<Advice>,
    s_rlp2: Column<Advice>,
    c_rlp1: Column<Advice>,
    c_rlp2: Column<Advice>,
    s_advices: [Column<Advice>; HASH_WIDTH],
    c_advices: [Column<Advice>; HASH_WIDTH],
    s_mod_node_hash_rlc: Column<Advice>, /* modified node s_advices RLC when s_advices present
                                          * hash (used also for leaf long/short) */
    c_mod_node_hash_rlc: Column<Advice>, /* modified node c_advices RLC when c_advices present
                                          * hash (used also for leaf long/short) */
    acc_s: Column<Advice>,      // for branch s and account leaf
    acc_mult_s: Column<Advice>, // for branch s and account leaf
    acc_c: Column<Advice>,      // for branch c
    acc_mult_c: Column<Advice>, // for branch c
    acc_r: F,
    // sel1 and sel2 in branch children: denote whether there is no leaf at is_modified (when value
    // is added or deleted from trie - but no branch is added or turned into leaf)
    // sel1 and sel2 in storage leaf key: key_rlc_prev and key_rlc_mult_prev
    // sel1 and sel2 in storage leaf value (only when leaf without branch as otherwise this info is
    // in the branch above): whether leaf is just a placeholder
    // sel1 and sel2 in account leaf key specifies whether nonce / balance are short / long (check
    // nonce balance row: offset - 1)
    sel1: Column<Advice>,
    sel2: Column<Advice>,
    r_table: Vec<Expression<F>>,
    // key_rlc & key_rlc_mult used for account address, for storage key,
    // and for mult_diff_nonce/mult_diff_balance in account_leaf_nonce_balance
    key_rlc: Column<Advice>,
    key_rlc_mult: Column<Advice>,
    mult_diff: Column<Advice>,
    keccak_table: [Column<Fixed>; KECCAK_INPUT_WIDTH + KECCAK_OUTPUT_WIDTH],
    fixed_table: [Column<Fixed>; 3],
    address_rlc: Column<Advice>, /* The same in all rows of a modification. The same as
                                  * address_rlc computed in the account leaf key row. Needed to
                                  * enable lookup for storage key/value (to have address RLC in
                                  * the same row as storage key/value). */
    counter: Column<Advice>,
    is_storage_mod: Column<Advice>,
    is_nonce_mod: Column<Advice>,
    is_balance_mod: Column<Advice>,
    is_codehash_mod: Column<Advice>,
    is_account_delete_mod: Column<Advice>,
    is_non_existing_account_proof: Column<Advice>,
    is_non_existing_account_row: Column<Advice>,
}

#[derive(Clone, Copy, Debug)]
pub enum FixedTableTag {
    RMult,
    Range16,
    Range256,
    RangeKeyLen256,
}

struct ProofVariables<F> {
    modified_node: u8,
    s_mod_node_hash_rlc: F,
    c_mod_node_hash_rlc: F,
    node_index: u8,
    acc_s: F,
    acc_mult_s: F,
    acc_account_s: F,
    acc_mult_account_s: F,
    acc_account_c: F,
    acc_mult_account_c: F,
    acc_nonce_balance_s: F,
    acc_mult_nonce_balance_s: F,
    acc_nonce_balance_c: F,
    acc_mult_nonce_balance_c: F,
    acc_c: F,
    acc_mult_c: F,
    key_rlc: F, /* used first for account address, then for storage key */
    key_rlc_mult: F,
    extension_node_rlc: F,
    key_rlc_prev: F, /* for leaf after placeholder extension/branch, we need to go one level
                      * back to get previous key_rlc */
    key_rlc_mult_prev: F,
    mult_diff: F,
    key_rlc_sel: bool, /* If true, nibble is multiplied by 16, otherwise by 1. */
    is_branch_s_placeholder: bool,
    is_branch_c_placeholder: bool,
    drifted_pos: u8, /* needed when leaf turned into branch and leaf moves into a branch where
                      * it's at drifted_pos position */
    rlp_len_rem_s: i32, /* branch RLP length remainder, in each branch children row this value
                         * is subtracted by the number of RLP bytes in
                         * this row (1 or 33) */
    rlp_len_rem_c: i32,
    is_extension_node: bool,
    is_even: bool,
    is_odd: bool,
    is_short: bool,
    is_long: bool,
    rlc1: F,
    rlc2: F,
    nonce_value_s: F,
    balance_value_s: F,
    before_account_leaf: bool,
}

impl<F: Field> ProofVariables<F> {
    fn new() -> ProofVariables<F> {
        ProofVariables {
            modified_node: 0,
            s_mod_node_hash_rlc: F::zero(),
            c_mod_node_hash_rlc: F::zero(),
            node_index: 0,
            acc_s: F::zero(),
            acc_mult_s: F::zero(),
            acc_account_s: F::zero(),
            acc_mult_account_s: F::zero(),
            acc_account_c: F::zero(),
            acc_mult_account_c: F::zero(),
            acc_nonce_balance_s: F::zero(),
            acc_mult_nonce_balance_s: F::zero(),
            acc_nonce_balance_c: F::zero(),
            acc_mult_nonce_balance_c: F::zero(),
            acc_c: F::zero(),
            acc_mult_c: F::zero(),
            key_rlc: F::zero(),
            key_rlc_mult: F::one(),
            extension_node_rlc: F::zero(),
            key_rlc_prev: F::zero(),
            key_rlc_mult_prev: F::one(),
            mult_diff: F::one(),
            key_rlc_sel: true,
            is_branch_s_placeholder: false,
            is_branch_c_placeholder: false,
            drifted_pos: 0,
            rlp_len_rem_s: 0,
            rlp_len_rem_c: 0,
            is_extension_node: false,
            is_even: false,
            is_odd: false,
            is_short: false,
            is_long: false,
            rlc1: F::zero(),
            rlc2: F::zero(),
            nonce_value_s: F::zero(),
            balance_value_s: F::zero(),
            before_account_leaf: true,
        }
    }
}

impl<F: Field> MPTConfig<F> {
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
        let mut r = one;
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

        let storage_leaf = StorageLeafCols {
            is_leaf_s : meta.advice_column(),
            is_leaf_s_value : meta.advice_column(),
            is_leaf_c : meta.advice_column(),
            is_leaf_c_value : meta.advice_column(),
            is_leaf_in_added_branch : meta.advice_column(),
        };

        let account_leaf = AccountLeafCols {
            is_account_leaf_key_s : meta.advice_column(),
            is_account_leaf_key_c : meta.advice_column(),
            is_account_leaf_nonce_balance_s : meta.advice_column(),
            is_account_leaf_nonce_balance_c : meta.advice_column(),
            is_account_leaf_storage_codehash_s : meta.advice_column(),
            is_account_leaf_storage_codehash_c : meta.advice_column(),
            is_account_leaf_in_added_branch : meta.advice_column(),
        };

        let branch = BranchCols {
            is_branch_init: meta.advice_column(),
            is_branch_child: meta.advice_column(),
            is_last_branch_child: meta.advice_column(),
            node_index: meta.advice_column(),
            is_modified: meta.advice_column(),
            modified_node: meta.advice_column(),
            is_at_drifted_pos: meta.advice_column(),
            drifted_pos: meta.advice_column(),
            is_extension_node_s: meta.advice_column(),
            is_extension_node_c: meta.advice_column(),
        };
        
        let s_rlp1 = meta.advice_column();
        let s_rlp2 = meta.advice_column();
        let s_advices: [Column<Advice>; HASH_WIDTH] = (0..HASH_WIDTH)
            .map(|_| meta.advice_column())
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let c_rlp1 = meta.advice_column();
        let c_rlp2 = meta.advice_column();
        let c_advices: [Column<Advice>; HASH_WIDTH] = (0..HASH_WIDTH)
            .map(|_| meta.advice_column())
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

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
        let is_storage_mod = meta.advice_column();
        let is_nonce_mod = meta.advice_column();
        let is_balance_mod = meta.advice_column();
        let is_codehash_mod = meta.advice_column();
        let is_account_delete_mod = meta.advice_column();
        let is_non_existing_account_proof = meta.advice_column();
        let is_non_existing_account_row = meta.advice_column();

        BranchHashInParentConfig::<F>::configure(
            meta,
            inter_start_root,
            not_first_level,
            q_not_first,
            account_leaf.is_account_leaf_in_added_branch,
            branch.is_last_branch_child,
            s_advices[IS_BRANCH_S_PLACEHOLDER_POS - LAYOUT_OFFSET],
            s_advices,
            s_mod_node_hash_rlc,
            acc_s,
            acc_mult_s,
            keccak_table,
        );

        BranchHashInParentConfig::<F>::configure(
            meta,
            inter_final_root,
            not_first_level,
            q_not_first,
            account_leaf.is_account_leaf_in_added_branch,
            branch.is_last_branch_child,
            s_advices[IS_BRANCH_C_PLACEHOLDER_POS - LAYOUT_OFFSET],
            s_advices,
            c_mod_node_hash_rlc,
            acc_c,
            acc_mult_c,
            keccak_table,
        );

        BranchRLCInitConfig::<F>::configure(
            meta,
            |meta| {
                meta.query_advice(branch.is_branch_init, Rotation::cur())
                    * meta.query_fixed(q_enable, Rotation::cur())
            },
            s_rlp1,
            s_rlp2,
            s_advices,
            acc_s,
            acc_mult_s,
            acc_c,
            acc_mult_c,
            acc_r,
            fixed_table,
        );

        BranchRLCConfig::<F>::configure(
            meta,
            |meta| {
                let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
                let is_branch_child = meta.query_advice(branch.is_branch_child, Rotation::cur());

                q_not_first * is_branch_child
            },
            s_rlp2,
            s_advices,
            acc_s,
            acc_mult_s,
            r_table.clone(),
        );

        BranchRLCConfig::<F>::configure(
            meta,
            |meta| {
                let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
                let is_branch_child = meta.query_advice(branch.is_branch_child, Rotation::cur());

                q_not_first * is_branch_child
            },
            c_rlp2,
            c_advices,
            acc_c,
            acc_mult_c,
            r_table.clone(),
        );

        MPTConfig {
            account_leaf,
            storage_leaf,
            q_enable,
            q_not_first,
            not_first_level,
            inter_start_root,
            inter_final_root,
            branch,
            s_rlp1,
            s_rlp2,
            c_rlp1,
            c_rlp2,
            s_advices,
            c_advices,
            s_mod_node_hash_rlc,
            c_mod_node_hash_rlc,
            acc_s,
            acc_mult_s,
            acc_c,
            acc_mult_c,
            acc_r,
            sel1,
            sel2,
            r_table,
            key_rlc,
            key_rlc_mult,
            mult_diff,
            keccak_table,
            fixed_table,
            address_rlc,
            counter,
            is_storage_mod,
            is_nonce_mod,
            is_balance_mod,
            is_codehash_mod,
            is_account_delete_mod,
            is_non_existing_account_proof,
            is_non_existing_account_row,
        }
    }

    fn assign_row(
        &self,
        region: &mut Region<'_, F>,
        row: &[u8],
        account_leaf: AccountLeaf,
        storage_leaf: StorageLeaf,
        branch: Branch,
        is_non_existing_account_row: bool,
        offset: usize,
    ) -> Result<(), Error> {
        region.assign_advice(
            || "assign is_branch_init".to_string(),
            self.branch.is_branch_init,
            offset,
            || Ok(F::from(branch.is_branch_init as u64)),
        )?;

        region.assign_advice(
            || "assign is_branch_child".to_string(),
            self.branch.is_branch_child,
            offset,
            || Ok(F::from(branch.is_branch_child as u64)),
        )?;

        region.assign_advice(
            || "assign is_last_branch_child".to_string(),
            self.branch.is_last_branch_child,
            offset,
            || Ok(F::from(branch.is_last_branch_child as u64)),
        )?;

        region.assign_advice(
            || "assign node_index".to_string(),
            self.branch.node_index,
            offset,
            || Ok(F::from(branch.node_index as u64)),
        )?;

        region.assign_advice(
            || "assign modified node".to_string(),
            self.branch.modified_node,
            offset,
            || Ok(F::from(branch.modified_node as u64)),
        )?;

        region.assign_advice(
            || "assign drifted_pos".to_string(),
            self.branch.drifted_pos,
            offset,
            || Ok(F::from(branch.drifted_pos as u64)),
        )?;

        region.assign_advice(
            || "assign is_at_drifted_pos".to_string(),
            self.branch.is_at_drifted_pos,
            offset,
            || Ok(F::from((branch.drifted_pos == branch.node_index) as u64)),
        )?;

        region.assign_advice(
            || "assign is extension node s".to_string(),
            self.branch.is_extension_node_s,
            offset,
            || Ok(F::from(branch.is_extension_node_s as u64)),
        )?;
        region.assign_advice(
            || "assign is extension node c".to_string(),
            self.branch.is_extension_node_c,
            offset,
            || Ok(F::from(branch.is_extension_node_c as u64)),
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
            || Ok(F::from((branch.modified_node == branch.node_index) as u64)),
        )?;

        region.assign_advice(
            || "assign is_leaf_s".to_string(),
            self.storage_leaf.is_leaf_s,
            offset,
            || Ok(F::from(storage_leaf.is_leaf_s as u64)),
        )?;
        region.assign_advice(
            || "assign is_leaf_c".to_string(),
            self.storage_leaf.is_leaf_c,
            offset,
            || Ok(F::from(storage_leaf.is_leaf_c as u64)),
        )?;

        region.assign_advice(
            || "assign is_leaf_s_value".to_string(),
            self.storage_leaf.is_leaf_s_value,
            offset,
            || Ok(F::from(storage_leaf.is_leaf_s_value as u64)),
        )?;
        region.assign_advice(
            || "assign is_leaf_c_value".to_string(),
            self.storage_leaf.is_leaf_c_value,
            offset,
            || Ok(F::from(storage_leaf.is_leaf_c_value as u64)),
        )?;
        region.assign_advice(
            || "assign is leaf in added branch".to_string(),
            self.storage_leaf.is_leaf_in_added_branch,
            offset,
            || Ok(F::from(storage_leaf.is_leaf_in_added_branch as u64)),
        )?;

        region.assign_advice(
            || "assign is account leaf key s".to_string(),
            self.account_leaf.is_account_leaf_key_s,
            offset,
            || Ok(F::from(account_leaf.is_account_leaf_key_s as u64)),
        )?;
        region.assign_advice(
            || "assign is account leaf key c".to_string(),
            self.account_leaf.is_account_leaf_key_c,
            offset,
            || Ok(F::from(account_leaf.is_account_leaf_key_c as u64)),
        )?;
        region.assign_advice(
            || "assign is account leaf nonce balance s".to_string(),
            self.account_leaf.is_account_leaf_nonce_balance_s,
            offset,
            || Ok(F::from(account_leaf.is_account_leaf_nonce_balance_s as u64)),
        )?;
        region.assign_advice(
            || "assign is account leaf nonce balance c".to_string(),
            self.account_leaf.is_account_leaf_nonce_balance_c,
            offset,
            || Ok(F::from(account_leaf.is_account_leaf_nonce_balance_c as u64)),
        )?;
        region.assign_advice(
            || "assign is account leaf storage codehash s".to_string(),
            self.account_leaf.is_account_leaf_storage_codehash_s,
            offset,
            || Ok(F::from(account_leaf.is_account_leaf_storage_codehash_s as u64)),
        )?;
        region.assign_advice(
            || "assign is account leaf storage codehash c".to_string(),
            self.account_leaf.is_account_leaf_storage_codehash_c,
            offset,
            || Ok(F::from(account_leaf.is_account_leaf_storage_codehash_c as u64)),
        )?;
        region.assign_advice(
            || "assign is account leaf in added branch".to_string(),
            self.account_leaf.is_account_leaf_in_added_branch,
            offset,
            || Ok(F::from(account_leaf.is_account_leaf_in_added_branch as u64)),
        )?; 
        region.assign_advice(
            || "assign is non existing account row".to_string(),
            self.is_non_existing_account_row,
            offset,
            || Ok(F::from(is_non_existing_account_row as u64)),
        )?;

        region.assign_advice(
            || "assign s_rlp1".to_string(),
            self.s_rlp1,
            offset,
            || Ok(F::from(row[0] as u64)),
        )?;

        region.assign_advice(
            || "assign s_rlp2".to_string(),
            self.s_rlp2,
            offset,
            || Ok(F::from(row[1] as u64)),
        )?;

        for idx in 0..HASH_WIDTH {
            region.assign_advice(
                || format!("assign s_advice {}", idx),
                self.s_advices[idx],
                offset,
                || Ok(F::from(row[LAYOUT_OFFSET + idx] as u64)),
            )?;
        }

        // not all columns may be needed
        let get_val = |curr_ind: usize| {
            if curr_ind >= row.len() { 0 } else { row[curr_ind] as u64 }
        };

        region.assign_advice(
            || "assign c_rlp1".to_string(),
            self.c_rlp1,
            offset,
            || Ok(F::from(get_val(WITNESS_ROW_WIDTH / 2))),
        )?;
        region.assign_advice(
            || "assign c_rlp2".to_string(),
            self.c_rlp2,
            offset,
            || Ok(F::from(get_val(WITNESS_ROW_WIDTH / 2 + 1))),
        )?;

        for (idx, _c) in self.c_advices.iter().enumerate() {
            let val = get_val(WITNESS_ROW_WIDTH / 2 + LAYOUT_OFFSET + idx);
            region.assign_advice(
                || format!("assign c_advice {}", idx),
                self.c_advices[idx],
                offset,
                || Ok(F::from(val)),
            )?;
        }
        Ok(())
    }

    fn assign_branch_init(
        &self,
        region: &mut Region<'_, F>,
        row: &[u8],
        offset: usize,
    ) -> Result<(), Error> {
        let account_leaf = AccountLeaf::default();
        let storage_leaf = StorageLeaf::default();
        let branch = Branch::default();

        self.assign_row(
            region,
            row,
            account_leaf,
            storage_leaf,
            branch,
            false,
            offset,
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
        let mut branch = Branch::default();
        branch.is_branch_child = true;
        branch.is_last_branch_child = node_index == 15;
        branch.node_index = node_index;
        branch.modified_node = key;
        branch.drifted_pos = drifted_pos;

        self.assign_row(
            region,
            row,
            account_leaf,
            storage_leaf,
            branch,
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
            self.s_rlp1,
            offset,
            || Ok(F::from(s_rlp1 as u64)),
        )?;
        region.assign_advice(
            || "c_rlp1",
            self.c_rlp1,
            offset,
            || Ok(F::from(c_rlp1 as u64)),
        )?;

        Ok(())
    }

    fn assign_acc(
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

    pub(crate) fn assign(&self, mut layouter: impl Layouter<F>, witness: &[Vec<u8>]) {
        layouter
            .assign_region(
                || "MPT",
                |mut region| {
                    let mut offset = 0;
                    let mut pv = ProofVariables::new();

                    // Note: filter out rows that are just to be hashed. We cannot simply use ind instead of offset
                    // because hashing rows appear in the middle of other rows.
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

                        region.assign_fixed(
                            || "q_enable",
                            self.q_enable,
                            offset,
                            || Ok(F::one()),
                        )?;

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
                            &row[l
                                - 4 * HASH_WIDTH
                                - COUNTER_WITNESS_LEN
                                - IS_NON_EXISTING_ACCOUNT_POS
                                ..l - 4 * HASH_WIDTH
                                    - COUNTER_WITNESS_LEN
                                    - IS_NON_EXISTING_ACCOUNT_POS
                                    + HASH_WIDTH],
                            self.acc_r,
                        );
                        let c_root_rlc = bytes_into_rlc(
                            &row[l
                                - 3 * HASH_WIDTH
                                - COUNTER_WITNESS_LEN
                                - IS_NON_EXISTING_ACCOUNT_POS
                                ..l - 3 * HASH_WIDTH
                                    - COUNTER_WITNESS_LEN
                                    - IS_NON_EXISTING_ACCOUNT_POS
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

                            pv.acc_s = F::from(row[BRANCH_0_S_START] as u64)
                                + F::from(row[BRANCH_0_S_START + 1] as u64) * self.acc_r;
                            pv.acc_mult_s = self.acc_r * self.acc_r;

                            if row[BRANCH_0_S_START] == 249 {
                                pv.acc_s +=
                                    F::from(row[BRANCH_0_S_START + 2] as u64) * pv.acc_mult_s;
                                pv.acc_mult_s *= self.acc_r;

                                pv.rlp_len_rem_s = row[BRANCH_0_S_START + 1] as i32 * 256
                                    + row[BRANCH_0_S_START + 2] as i32;
                            } else {
                                pv.rlp_len_rem_s = row[BRANCH_0_S_START + 1] as i32;
                            }

                            pv.acc_c = F::from(row[BRANCH_0_C_START] as u64)
                                + F::from(row[BRANCH_0_C_START + 1] as u64) * self.acc_r;
                            pv.acc_mult_c = self.acc_r * self.acc_r;

                            if row[BRANCH_0_C_START] == 249 {
                                pv.acc_c +=
                                    F::from(row[BRANCH_0_C_START + 2] as u64) * pv.acc_mult_c;
                                pv.acc_mult_c *= self.acc_r;

                                pv.rlp_len_rem_c = row[BRANCH_0_C_START + 1] as i32 * 256
                                    + row[BRANCH_0_C_START + 2] as i32;
                            } else {
                                pv.rlp_len_rem_c = row[BRANCH_0_C_START + 1] as i32;
                            }

                            self.assign_acc(
                                &mut region,
                                pv.acc_s,
                                pv.acc_mult_s,
                                pv.acc_c,
                                pv.acc_mult_c,
                                offset,
                            )?;
                        } else if row[row.len() - 1] == 1 {
                            // branch child

                            if pv.node_index == 0 {
                                // If it's not extension node, rlc and rlc_mult in extension row
                                // will be the same as for branch rlc.
                                pv.extension_node_rlc = pv.key_rlc;

                                pv.key_rlc_prev = pv.key_rlc;
                                pv.key_rlc_mult_prev = pv.key_rlc_mult;

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

                            let c128 = F::from(128_u64);
                            let c160 = F::from(160_u64);

                            let compute_branch_acc_and_mult =
                                |branch_acc: &mut F,
                                 branch_mult: &mut F,
                                 rlp_start: usize,
                                 start: usize| {
                                    if row[rlp_start + 1] == 0 {
                                        *branch_acc += c128 * *branch_mult;
                                        *branch_mult *= self.acc_r;
                                    } else {
                                        *branch_acc += c160 * *branch_mult;
                                        *branch_mult *= self.acc_r;
                                        for i in 0..HASH_WIDTH {
                                            *branch_acc +=
                                                F::from(row[start + i] as u64) * *branch_mult;
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

                            pv.node_index += 1;
                        } else if row[row.len() - 1] != 5 {
                            let mut account_leaf = AccountLeaf::default();
                            let mut storage_leaf = StorageLeaf::default();
                            let mut branch = Branch::default();

                            let mut is_non_existing_account = false;

                            if row[row.len() - 1] == 2 {
                                storage_leaf.is_leaf_s = true;
                            } else if row[row.len() - 1] == 3 {
                                storage_leaf.is_leaf_c = true;
                            } else if row[row.len() - 1] == 6 {
                                account_leaf.is_account_leaf_key_s = true;
                            } else if row[row.len() - 1] == 4 {
                                account_leaf.is_account_leaf_key_c = true;
                            } else if row[row.len() - 1] == 7 {
                                account_leaf.is_account_leaf_nonce_balance_s = true;
                            } else if row[row.len() - 1] == 8 {
                                account_leaf.is_account_leaf_nonce_balance_c = true;
                            } else if row[row.len() - 1] == 9 {
                                account_leaf.is_account_leaf_storage_codehash_s = true;
                            } else if row[row.len() - 1] == 11 {
                                account_leaf.is_account_leaf_storage_codehash_c = true;
                            } else if row[row.len() - 1] == 10 {
                                account_leaf.is_account_leaf_in_added_branch = true;
                                pv.key_rlc = F::zero(); // account address until here, storage key from here on
                                pv.key_rlc_mult = F::one();
                                pv.key_rlc_prev = F::zero();
                                pv.key_rlc_mult_prev = F::one();
                                pv.key_rlc_sel = true;
                                // TODO: check whether all constraints are
                                // implemented (extension_node_rlc ...)
                            } else if row[row.len() - 1] == 13 {
                                storage_leaf.is_leaf_s_value = true;
                            } else if row[row.len() - 1] == 14 {
                                storage_leaf.is_leaf_c_value = true;
                            } else if row[row.len() - 1] == 15 {
                                storage_leaf.is_leaf_in_added_branch = true;
                            } else if row[row.len() - 1] == 16 {
                                branch.is_extension_node_s = true;
                            } else if row[row.len() - 1] == 17 {
                                branch.is_extension_node_c = true;
                            } else if row[row.len() - 1] == 18 {
                                is_non_existing_account = true;
                            }

                            self.assign_row(
                                &mut region,
                                &row[0..row.len() - 1].to_vec(),
                                account_leaf,
                                storage_leaf,
                                branch,
                                is_non_existing_account,
                                offset,
                            )?;
                        }
                        offset += 1;
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

                for (offset, t) in to_be_hashed.iter().enumerate() {
                    let hash = self.compute_keccak(t);
                    let mut rlc = F::zero();
                    let mut mult = F::one();

                    for i in t.iter() {
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
                    mult *= self.acc_r;

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
        dev::{MockProver},
        pairing::bn256::Fr as Fp,
        plonk::{
            Circuit, ConstraintSystem, Error,
        },
    };

    use eth_types::Field;
    use std::{marker::PhantomData};

    #[test]
    fn test_mpt() {
        #[derive(Default)]
        struct MyCircuit<F> {
            _marker: PhantomData<F>,
            witness: Vec<Vec<u8>>,
        }

        impl<F: Field> Circuit<F> for MyCircuit<F> {
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


        let list_to_run = [
            "AddBranchLong.json",
            "DeleteBranchTwoLevels.json",
            "Delete.json",
            "BalanceModCLong.json",
            "ExtensionDeletedTwoKeyBytesSel1.json",
            "ExtensionAddedOneKeyByteSel2.json",
            "ExtensionDeletedOneKeyByteSel1.json",
            "ExtensionThreeKeyBytesSel2.json",
            "UpdateOneLevelEvenAddress.json",
            "ExtensionOneKeyByteSel2.json",
            "ExtensionTwoKeyBytesSel1.json",
            "NonceModCLong.json",
            "ExtensionAddedTwoKeyBytesSel1.json",
            "FromNilToValue.json",
            "ExtensionInFirstStorageLevelTwoKeyBytes.json",
            "ExtensionThreeKeyBytes.json",
            "NonceModCShort.json",
            "AccountDeletePlaceholderBranch.json",
            "AddBranchTwoLevels.json",
            "DeleteBranch.json",
            "ExtensionAddedInFirstStorageLevelTwoKeyBytes.json",
            "UpdateOneLevel1.json",
            "AccountDeletePlaceholderExtension.json",
            "LeafAddedToEmptyTrie.json",
            "AddAccount.json",
            "UpdateTwoLevels.json",
            "UpdateOneLevelBigVal.json",
            "DeleteBranchTwoLevelsLong.json",
            "ExtensionAddedThreeKeyBytesSel2.json",
            "ExtensionInFirstStorageLevel.json",
            "UpdateOneLevel.json",
            "ImplicitlyCreateAccountWithBalance.json",
            "ExtensionTwoKeyBytesSel2.json",
            "UpdateThreeLevels.json",
            "AddBranchTwoLevelsLong.json",
            "ExtensionAddedTwoKeyBytesSel2.json",
            "ExtensionDeletedThreeKeyBytesSel2.json",
            "AddBranch.json",
            "AccountAddPlaceholderExtension.json",
            "UpdateTwoLevelsBigVal.json",
            "ExtensionAddedInFirstStorageLevelOneKeyByte.json",
            "AccountAddPlaceholderBranch.json",
            "ExtensionOneKeyByteSel1.json",
            "DeleteBranchLong.json",
            "ImplicitlyCreateAccountWithNonce.json",
            "DeleteToEmptyTrie.json",
            "ExtensionAddedOneKeyByteSel1.json",
            "ExtensionDeletedOneKeyByteSel2.json",
            "UpdateTwoModifications.json",
            "ExtensionDeletedTwoKeyBytesSel2.json",
            "OnlyLeafInStorageProof.json",
            "DeleteAccount.json",
            "ExtensionInFirstStorageLevelOneKeyByte.json",
            "BalanceModCShort.json",
        ];

        list_to_run
            .iter().for_each (|path| {
                let path = format!("mpt/tests/{}", path);
                println!("{:?}", path);
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
            });
    }
}
