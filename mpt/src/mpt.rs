use halo2::{
    circuit::{Layouter, Region},
    plonk::{
        Advice, Column, ConstraintSystem, Error, Expression, Fixed, Selector,
    },
    poly::Rotation,
};
use keccak256::plain::Keccak;
use pairing::arithmetic::FieldExt;
use std::{convert::TryInto, marker::PhantomData};

use crate::{
    account_leaf_key::AccountLeafKeyChip,
    account_leaf_nonce_balance::AccountLeafNonceBalanceChip,
    account_leaf_storage_codehash::AccountLeafStorageCodehashChip,
    branch_acc::BranchAccChip, leaf_key::LeafKeyChip,
    leaf_key_in_added_branch::LeafKeyInAddedBranchChip,
    leaf_value::LeafValueChip, param::LAYOUT_OFFSET,
};
use crate::{branch_acc::BranchAccConfig, param::WITNESS_ROW_WIDTH};
use crate::{
    param::{
        BRANCH_0_C_START, BRANCH_0_KEY_POS, BRANCH_0_S_START, C_RLP_START,
        C_START, FIRST_NIBBLE_POS, HASH_WIDTH, IS_BRANCH_C_PLACEHOLDER_POS,
        IS_BRANCH_S_PLACEHOLDER_POS, KECCAK_INPUT_WIDTH, KECCAK_OUTPUT_WIDTH,
        S_RLP_START, S_START,
    },
    selectors::SelectorsChip,
};

#[derive(Clone, Debug)]
pub struct MPTConfig<F> {
    q_enable: Selector,
    q_not_first: Column<Fixed>,     // not first row
    not_first_level: Column<Fixed>, // to avoid rotating back when in the first branch (for key rlc)
    is_branch_init: Column<Advice>,
    is_branch_child: Column<Advice>,
    is_last_branch_child: Column<Advice>,
    is_leaf_s: Column<Advice>,
    is_leaf_s_value: Column<Advice>,
    is_leaf_c: Column<Advice>,
    is_leaf_c_value: Column<Advice>,
    is_account_leaf_key_s: Column<Advice>,
    is_account_leaf_nonce_balance_s: Column<Advice>,
    is_account_leaf_storage_codehash_s: Column<Advice>,
    // There is no is_account_leaf_key_c and is_account_leaf_nonce_balance_c
    // because it's always the same for S and C, so we just use S for both.
    is_account_leaf_storage_codehash_c: Column<Advice>,
    node_index: Column<Advice>,
    is_modified: Column<Advice>, // whether this branch node is modified
    modified_node: Column<Advice>, // index of the modified node
    is_at_first_nibble: Column<Advice>, // needed when leaf is turned into branch
    first_nibble: Column<Advice>, // needed when leaf is turned into branch - first nibble of the key stored in a leaf (because the existing leaf will jump to this position in added branch)
    is_leaf_in_added_branch: Column<Advice>, // it is at first_nibble position in added branch, note that this row could be omitted when there is no added branch but then it would open a vulnerability because the attacker could omit these row in cases when it's needed too (and constraints happen in this row)
    is_extension_node_s: Column<Advice>, // contains extension node key (s_advices) and hash of the branch (c_advices)
    is_extension_node_c: Column<Advice>,
    s_rlp1: Column<Advice>,
    s_rlp2: Column<Advice>,
    c_rlp1: Column<Advice>,
    c_rlp2: Column<Advice>,
    s_advices: [Column<Advice>; HASH_WIDTH],
    c_advices: [Column<Advice>; HASH_WIDTH],
    s_keccak: [Column<Advice>; KECCAK_OUTPUT_WIDTH],
    c_keccak: [Column<Advice>; KECCAK_OUTPUT_WIDTH],
    acc_s: Column<Advice>, // for branch s and account leaf
    acc_mult_s: Column<Advice>, // for branch s and account leaf
    acc_c: Column<Advice>, // for branch c
    acc_mult_c: Column<Advice>, // for branch c
    acc_r: F,
    // sel1 and sel2 in branch init: denote whether it's the first or second nibble of the key byte
    // sel1 and sel2 in branch children: denote whether there is no leaf at is_modified (when value is added or deleted from trie)
    sel1: Column<Advice>,
    sel2: Column<Advice>,
    r_table: Vec<Expression<F>>,
    branch_acc_s_chip: BranchAccConfig,
    branch_acc_c_chip: BranchAccConfig,
    key_rlc: Column<Advice>, // used first for account address, then for storage key
    key_rlc_mult: Column<Advice>,
    keccak_table: [Column<Fixed>; KECCAK_INPUT_WIDTH + KECCAK_OUTPUT_WIDTH],
    r_mult_table: [Column<Fixed>; 2],
    _marker: PhantomData<F>,
}

impl<F: FieldExt> MPTConfig<F> {
    pub(crate) fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let q_enable = meta.selector();
        let q_not_first = meta.fixed_column();
        let not_first_level = meta.fixed_column();

        let acc_r = F::rand(); // TODO: generate from commitments

        let one = Expression::Constant(F::one());
        let mut r_table = vec![];
        let mut r = one.clone();
        for _ in 0..HASH_WIDTH {
            r = r * acc_r;
            r_table.push(r.clone());
        }

        // TODO: r_table constraints

        // TODO: in many cases different rotations can be used - for example, when getting back
        // into s_keccak or c_keccak to get the hash (all 16 branch children contain the same hash in
        // s_keccak and c_keccak), so we can choose the rotations smartly to have at least as possible of them

        let is_branch_init = meta.advice_column();
        let is_branch_child = meta.advice_column();
        let is_last_branch_child = meta.advice_column();
        let is_leaf_s = meta.advice_column();
        let is_leaf_s_value = meta.advice_column();
        let is_leaf_c = meta.advice_column();
        let is_leaf_c_value = meta.advice_column();

        let is_account_leaf_key_s = meta.advice_column();
        let is_account_leaf_nonce_balance_s = meta.advice_column();
        let is_account_leaf_storage_codehash_s = meta.advice_column();
        let is_account_leaf_storage_codehash_c = meta.advice_column();

        let node_index = meta.advice_column();
        let is_modified = meta.advice_column();
        let modified_node = meta.advice_column();

        let is_at_first_nibble = meta.advice_column();
        let first_nibble = meta.advice_column();
        let is_leaf_in_added_branch = meta.advice_column();
        let is_extension_node_s = meta.advice_column();
        let is_extension_node_c = meta.advice_column();

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

        let keccak_table: [Column<Fixed>;
            KECCAK_INPUT_WIDTH + KECCAK_OUTPUT_WIDTH] = (0..KECCAK_INPUT_WIDTH
            + KECCAK_OUTPUT_WIDTH)
            .map(|_| meta.fixed_column())
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let r_mult_table: [Column<Fixed>; 2] = (0..2)
            .map(|_| meta.fixed_column())
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let s_keccak: [Column<Advice>; KECCAK_OUTPUT_WIDTH] = (0
            ..KECCAK_OUTPUT_WIDTH)
            .map(|_| meta.advice_column())
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        let c_keccak: [Column<Advice>; KECCAK_OUTPUT_WIDTH] = (0
            ..KECCAK_OUTPUT_WIDTH)
            .map(|_| meta.advice_column())
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

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

        // Turn 32 hash cells into 4 cells containing keccak words.
        let into_words_expr = |hash: Vec<Expression<F>>| {
            let mut words = vec![];
            for i in 0..4 {
                let mut word = Expression::Constant(F::zero());
                let mut exp = Expression::Constant(F::one());
                for j in 0..8 {
                    word = word + hash[i * 8 + j].clone() * exp.clone();
                    exp = exp * Expression::Constant(F::from(256));
                }
                words.push(word)
            }

            words
        };

        SelectorsChip::<F>::configure(
            meta,
            |meta| meta.query_selector(q_enable),
            is_branch_init,
            is_branch_child,
            is_last_branch_child,
            is_leaf_s,
            is_leaf_s_value,
            is_leaf_c,
            is_leaf_c_value,
            is_account_leaf_key_s,
            is_account_leaf_nonce_balance_s,
            is_account_leaf_storage_codehash_s,
            is_account_leaf_storage_codehash_c,
            is_leaf_in_added_branch,
            is_extension_node_s,
            is_extension_node_c,
            sel1,
            sel2,
            is_modified,
            is_at_first_nibble,
        );

        // TODO: range proofs for bytes

        meta.create_gate("branch equalities", |meta| {
            let q_enable = meta.query_selector(q_enable);

            let mut constraints = vec![];

            let is_branch_child_cur =
                meta.query_advice(is_branch_child, Rotation::cur());
            let node_index_cur = meta.query_advice(node_index, Rotation::cur());
            let modified_node =
                meta.query_advice(modified_node, Rotation::cur());
            let is_modified = meta.query_advice(is_modified, Rotation::cur());
            let is_at_first_nibble =
                meta.query_advice(is_at_first_nibble, Rotation::cur());
            let first_nibble = meta.query_advice(first_nibble, Rotation::cur());

            // is_modified is:
            //   0 when node_index_cur != modified_node
            //   1 when node_index_cur == modified_node (it's checked elsewhere for booleanity)
            constraints.push((
                "is modified",
                q_enable.clone()
                    * is_branch_child_cur.clone()
                    * is_modified
                    * (node_index_cur.clone() - modified_node.clone()),
            ));

            // is_at_first_nibble is:
            //   0 when node_index_cur != first_nibble
            //   1 when node_index_cur == first_nibble (it's checked elsewhere for booleanity)
            constraints.push((
                "is at first nibble",
                q_enable.clone()
                    * is_branch_child_cur.clone()
                    * is_at_first_nibble
                    * (node_index_cur.clone() - first_nibble.clone()),
            ));

            let s_rlp1 = meta.query_advice(s_rlp1, Rotation::cur());
            let s_rlp2 = meta.query_advice(s_rlp2, Rotation::cur());

            let c_rlp1 = meta.query_advice(c_rlp1, Rotation::cur());
            let c_rlp2 = meta.query_advice(c_rlp2, Rotation::cur());

            constraints.push((
                "rlp 1",
                q_enable.clone()
                    * is_branch_child_cur.clone()
                    * (s_rlp1 - c_rlp1)
                    * (node_index_cur.clone() - modified_node.clone()),
            ));
            constraints.push((
                "rlp 2",
                q_enable.clone()
                    * is_branch_child_cur.clone()
                    * (s_rlp2 - c_rlp2)
                    * (node_index_cur.clone() - modified_node.clone()),
            ));

            for (ind, col) in s_advices.iter().enumerate() {
                let s = meta.query_advice(*col, Rotation::cur());
                let c = meta.query_advice(c_advices[ind], Rotation::cur());
                constraints.push((
                    "s = c",
                    q_enable.clone()
                        * is_branch_child_cur.clone()
                        * (s - c)
                        * (node_index_cur.clone() - modified_node.clone()),
                ));
            }

            // TODO: use permutation argument for s = c.

            // TODO: use permutation argument to make sure modified_node is the same in all branch rows.

            // TODO: use permutation argument to make sure first_nibble is the same in all branch rows.

            constraints
        });

        meta.create_gate("branch children", |meta| {
            let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
            let not_first_level =
                meta.query_fixed(not_first_level, Rotation::cur());

            let mut constraints = vec![];
            let is_branch_child_prev =
                meta.query_advice(is_branch_child, Rotation::prev());
            let is_branch_child_cur =
                meta.query_advice(is_branch_child, Rotation::cur());
            let is_branch_init_prev =
                meta.query_advice(is_branch_init, Rotation::prev());
            let is_last_branch_child_prev =
                meta.query_advice(is_last_branch_child, Rotation::prev());
            let is_last_branch_child_cur =
                meta.query_advice(is_last_branch_child, Rotation::cur());

            // TODO: is_compact_leaf + is_branch_child + is_branch_init + ... = 1
            // It's actually more complex that just sum = 1.
            // For example, we have to allow is_last_branch_child to have value 1 only
            // when is_branch_child. So we need to add constraint like:
            // (is_branch_child - is_last_branch_child) * is_last_branch_child
            // There are already constraints "is last branch child 1 and 2" below
            // to make sure that is_last_branch_child is 1 only when node_index = 15.

            // TODO: not_first_level constraints (needs to be 0 or 1 and needs to
            // be strictly decreasing)

            // if we have branch child, we can only have branch child or branch init in the previous row
            constraints.push((
                "before branch children",
                q_not_first.clone()
                    * is_branch_child_cur.clone()
                    * (is_branch_child_prev.clone() - one.clone())
                    * (is_branch_init_prev.clone() - one.clone()),
            ));

            // If we have is_branch_init in the previous row, we have
            // is_branch_child with node_index = 0 in the current row.
            constraints.push((
                "first branch children 1",
                q_not_first.clone()
                    * is_branch_init_prev.clone()
                    * (is_branch_child_cur.clone() - one.clone()), // is_branch_child has to be 1
            ));
            // We could have only one constraint using sum, but then we would need
            // to limit node_index (to prevent values like -1). Now, node_index is
            // limited by ensuring it's first value is 0, its last value is 15,
            // and it's increasing by 1.
            let node_index_cur = meta.query_advice(node_index, Rotation::cur());
            constraints.push((
                "first branch children 2",
                q_not_first.clone()
                    * is_branch_init_prev.clone()
                    * node_index_cur.clone(), // node_index has to be 0
            ));

            // When is_branch_child changes back to 0, previous node_index has to be 15.
            let node_index_prev =
                meta.query_advice(node_index, Rotation::prev());
            constraints.push((
                "last branch children",
                q_not_first.clone()
                    * (one.clone() - is_branch_init_prev.clone()) // ignore if previous row was is_branch_init (here is_branch_child changes too)
                    * (is_branch_child_prev.clone()
                        - is_branch_child_cur.clone()) // for this to work properly make sure to have constraints like is_branch_child + is_keccak_leaf + ... = 1
                    * (node_index_prev
                        - Expression::Constant(F::from(15_u64))), // node_index has to be 15
            ));

            // When node_index is not 15, is_last_branch_child needs to be 0.
            constraints.push((
                "is last branch child 1",
                q_not_first.clone()
                    * is_last_branch_child_cur
                    * (node_index_cur.clone() // for this to work properly is_last_branch_child needs to have value 1 only when is_branch_child
                        - Expression::Constant(F::from(15_u64))),
            ));
            // When node_index is 15, is_last_branch_child needs to be 1.
            constraints.push((
                "is last branch child 2",
                q_not_first.clone()
                    * (one.clone() - is_branch_init_prev.clone()) // ignore if previous row was is_branch_init (here is_branch_child changes too)
                    * (is_last_branch_child_prev - one.clone())
                    * (is_branch_child_prev
                        - is_branch_child_cur.clone()), // for this to work properly make sure to have constraints like is_branch_child + is_keccak_leaf + ... = 1
            ));

            // node_index is increasing by 1 for is_branch_child
            let node_index_prev =
                meta.query_advice(node_index, Rotation::prev());
            constraints.push((
                "node index increasing for branch children",
                q_not_first.clone()
                    * is_branch_child_cur.clone()
                    * node_index_cur.clone() // ignore if node_index = 0
                    * (node_index_cur.clone() - node_index_prev - one.clone()),
            ));

            // modified_node needs to be the same for all branch nodes
            let modified_node_prev =
                meta.query_advice(modified_node, Rotation::prev());
            let modified_node_cur =
                meta.query_advice(modified_node, Rotation::cur());
            constraints.push((
                "modified node the same for all branch children",
                q_not_first.clone()
                    * is_branch_child_cur
                    * node_index_cur // ignore if node_index = 0
                    * (modified_node_cur.clone() - modified_node_prev),
            ));

            // For the first branch node (node_index = 0), the key rlc needs to be:
            // key_rlc = key_rlc::Rotation(-19) + modified_node * key_rlc_mult
            // Note: we check this in the first branch node (after branch init),
            // Rotation(-19) lands into the previous first branch node, that's because
            // branch has 1 (init) + 16 (children) + 2 (extension nodes for S and C) rows

            // We need to check whether we are in the first storage level, we can do this
            // by checking whether is_account_leaf_storage_codehash_c is true in the previous row.

            // -2 because we are in the first branch child and -1 is branch init row, -2 is
            // account leaf storage codehash when we are in the first storage proof level
            let is_account_leaf_storage_codehash_prev = meta
                .query_advice(is_account_leaf_storage_codehash_c, Rotation(-2));

            let c16 = Expression::Constant(F::from(16));
            // If sel1 = 1, then modified_node is multiplied by 16.
            // If sel2 = 1, then modified_node is multiplied by 1.
            // NOTE: modified_node presents nibbles: n0, n1, ...
            // key_rlc = (n0 * 16 + n1) + (n2 * 16 + n3) * r + (n4 * 16 + n5) * r^2 + ...
            let sel1_prev = meta.query_advice(sel1, Rotation(-20));
            let sel2_prev = meta.query_advice(sel2, Rotation(-20));
            // Rotation(-20) lands into previous branch init.
            let sel1_cur = meta.query_advice(sel1, Rotation::prev());
            let sel2_cur = meta.query_advice(sel2, Rotation::prev());

            let key_rlc_prev = meta.query_advice(key_rlc, Rotation(-19));
            let key_rlc_cur = meta.query_advice(key_rlc, Rotation::cur());
            let key_rlc_mult_prev =
                meta.query_advice(key_rlc_mult, Rotation(-19));
            let key_rlc_mult_cur =
                meta.query_advice(key_rlc_mult, Rotation::cur());
            constraints.push((
                "first branch children key_rlc sel1",
                not_first_level.clone()
                    * is_branch_init_prev.clone()
                    * (one.clone() - is_account_leaf_storage_codehash_prev.clone()) // When this is 0, we check as for the first level key rlc.
                    * sel1_cur.clone()
                    * (key_rlc_cur.clone()
                        - key_rlc_prev.clone()
                        - modified_node_cur.clone() * c16.clone()
                            * key_rlc_mult_prev.clone()),
            ));
            constraints.push((
                "first branch children key_rlc sel2",
                not_first_level.clone()
                    * is_branch_init_prev.clone()
                    * (one.clone() - is_account_leaf_storage_codehash_prev.clone()) // When this is 0, we check as for the first level key rlc.
                    * sel2_cur.clone()
                    * (key_rlc_cur.clone()
                        - key_rlc_prev
                        - modified_node_cur.clone()
                            * key_rlc_mult_prev.clone()),
            ));

            constraints.push((
                "first branch children key_rlc_mult sel1",
                not_first_level.clone()
                    * is_branch_init_prev.clone()
                    * (one.clone() - is_account_leaf_storage_codehash_prev.clone()) // When this is 0, we check as for the first level key rlc.
                    * sel1_cur.clone()
                    * (key_rlc_mult_cur.clone() - key_rlc_mult_prev.clone()),
            ));
            constraints.push((
                "first branch children key_rlc_mult sel2",
                not_first_level.clone()
                    * is_branch_init_prev.clone()
                    * (one.clone() - is_account_leaf_storage_codehash_prev.clone()) // When this is 0, we check as for the first level key rlc.
                    * sel2_cur.clone()
                    * (key_rlc_mult_cur.clone() - key_rlc_mult_prev * acc_r),
            ));

            constraints.push((
                "first branch children sel1 0->1->0->...",
                not_first_level.clone()
                    * is_branch_init_prev.clone()
                    * (one.clone() - is_account_leaf_storage_codehash_prev.clone()) // When this is 0, we check as for the first level key rlc.
                    * (sel1_cur.clone() + sel1_prev - one.clone()),
            ));
            constraints.push((
                "first branch children sel2 0->1->0->...",
                not_first_level.clone()
                    * is_branch_init_prev.clone()
                    * (one.clone() - is_account_leaf_storage_codehash_prev.clone()) // When this is 0, we check as for the first level key rlc.
                    * (sel2_cur.clone() + sel2_prev - one.clone()),
            ));

            // Key (which actually means account address) in first level in account proof.
            constraints.push((
                "account first level key_rlc",
                q_not_first.clone()
                    * (one.clone() - not_first_level.clone())
                    * is_branch_init_prev.clone()
                    * (key_rlc_cur.clone()
                        - modified_node_cur.clone() * c16.clone()),
            ));
            constraints.push((
                "account first level key_rlc_mult",
                q_not_first.clone()
                    * (one.clone() - not_first_level.clone())
                    * is_branch_init_prev.clone()
                    * (key_rlc_mult_cur.clone() - one.clone()),
            ));
            // First sel1 is 1, first sel2 is 0.
            constraints.push((
                "account first level key_rlc sel1",
                q_not_first.clone()
                    * (one.clone() - not_first_level.clone())
                    * is_branch_init_prev.clone()
                    * (sel1_cur.clone() - one.clone()),
            ));
            constraints.push((
                "account first level key_rlc sel2",
                q_not_first.clone()
                    * (one.clone() - not_first_level)
                    * is_branch_init_prev.clone()
                    * sel2_cur.clone(),
            ));

            // First storage level.
            constraints.push((
                "storage first level key_rlc",
                q_not_first.clone()
                    * is_account_leaf_storage_codehash_prev.clone()
                    * is_branch_init_prev.clone()
                    * (key_rlc_cur - modified_node_cur * c16),
            ));
            constraints.push((
                "storage first level key_rlc_mult",
                q_not_first.clone()
                    * is_account_leaf_storage_codehash_prev.clone()
                    * is_branch_init_prev.clone()
                    * (key_rlc_mult_cur - one.clone()),
            ));
            // First sel1 is 1, first sel2 is 0.
            constraints.push((
                "storage first level key_rlc sel1",
                q_not_first.clone()
                    * is_account_leaf_storage_codehash_prev.clone()
                    * is_branch_init_prev.clone()
                    * (sel1_cur - one.clone()),
            ));
            constraints.push((
                "storage first level key_rlc sel2",
                q_not_first
                    * is_account_leaf_storage_codehash_prev
                    * is_branch_init_prev
                    * sel2_cur,
            ));

            // TODO:
            // empty nodes have 0 at s_rlp2, while non-empty nodes have 160;
            // empty nodes have 128 at s_advices[0] and 0 everywhere else;
            // non-empty nodes have 32 values ...

            // TODO: is_branch_child is followed by is_compact_leaf
            // TODO: is_compact_leaf is followed by is_keccak_leaf

            // TODO: constraints for branch init

            constraints
        });

        meta.create_gate("branch init accumulator", |meta| {
            let q_enable = meta.query_selector(q_enable);
            let is_branch_init_cur =
                meta.query_advice(is_branch_init, Rotation::cur());

            let mut constraints = vec![];

            // check branch accumulator S in row 0
            let branch_acc_s_cur = meta.query_advice(acc_s, Rotation::cur());
            let branch_acc_c_cur = meta.query_advice(acc_c, Rotation::cur());
            let branch_mult_s_cur =
                meta.query_advice(acc_mult_s, Rotation::cur());
            let branch_mult_c_cur =
                meta.query_advice(acc_mult_c, Rotation::cur());

            let two_rlp_bytes_s = meta.query_advice(s_rlp1, Rotation::cur());
            let three_rlp_bytes_s = meta.query_advice(s_rlp2, Rotation::cur());

            let two_rlp_bytes_c =
                meta.query_advice(s_advices[0], Rotation::cur());
            let three_rlp_bytes_c =
                meta.query_advice(s_advices[1], Rotation::cur());

            // TODO: two_rlp_bytes and three_rlp_bytes are bools for S and C
            // TODO: two_rlp_bytes + three_rlp_bytes = 1 for S and C

            let s_rlp1 = meta.query_advice(s_advices[2], Rotation::cur());
            let s_rlp2 = meta.query_advice(s_advices[3], Rotation::cur());
            let s_rlp3 = meta.query_advice(s_advices[4], Rotation::cur());

            let c_rlp1 = meta.query_advice(s_advices[5], Rotation::cur());
            let c_rlp2 = meta.query_advice(s_advices[6], Rotation::cur());
            let c_rlp3 = meta.query_advice(s_advices[7], Rotation::cur());

            let acc_s_two = s_rlp1.clone() + s_rlp2.clone() * acc_r;
            constraints.push((
                "branch accumulator S row 0",
                q_enable.clone()
                    * is_branch_init_cur.clone()
                    * two_rlp_bytes_s.clone()
                    * (acc_s_two - branch_acc_s_cur.clone()),
            ));

            let mult_s_two = Expression::Constant(acc_r * acc_r);
            constraints.push((
                "branch mult S row 0",
                q_enable.clone()
                    * is_branch_init_cur.clone()
                    * two_rlp_bytes_s
                    * (mult_s_two - branch_mult_s_cur.clone()),
            ));

            let acc_c_two = c_rlp1.clone() + c_rlp2.clone() * acc_r;
            constraints.push((
                "branch accumulator C row 0",
                q_enable.clone()
                    * is_branch_init_cur.clone()
                    * two_rlp_bytes_c.clone()
                    * (acc_c_two - branch_acc_c_cur.clone()),
            ));

            let mult_c_two = Expression::Constant(acc_r * acc_r);
            constraints.push((
                "branch mult C row 0",
                q_enable.clone()
                    * is_branch_init_cur.clone()
                    * two_rlp_bytes_c
                    * (mult_c_two - branch_mult_c_cur.clone()),
            ));

            //

            let acc_s_three = s_rlp1 + s_rlp2 * acc_r + s_rlp3 * acc_r * acc_r;
            constraints.push((
                "branch accumulator S row 0 (3)",
                q_enable.clone()
                    * is_branch_init_cur.clone()
                    * three_rlp_bytes_s.clone()
                    * (acc_s_three - branch_acc_s_cur),
            ));

            let mult_s_three = Expression::Constant(acc_r * acc_r * acc_r);
            constraints.push((
                "branch mult S row 0 (3)",
                q_enable.clone()
                    * is_branch_init_cur.clone()
                    * three_rlp_bytes_s
                    * (mult_s_three - branch_mult_s_cur),
            ));

            let acc_c_three = c_rlp1 + c_rlp2 * acc_r + c_rlp3 * acc_r * acc_r;
            constraints.push((
                "branch accumulator C row 0 (3)",
                q_enable.clone()
                    * is_branch_init_cur.clone()
                    * three_rlp_bytes_c.clone()
                    * (acc_c_three - branch_acc_c_cur),
            ));

            let mult_c_three = Expression::Constant(acc_r * acc_r * acc_r);
            constraints.push((
                "branch mult C row 0 (3)",
                q_enable
                    * is_branch_init_cur
                    * three_rlp_bytes_c
                    * (mult_c_three - branch_mult_c_cur),
            ));

            constraints
        });

        meta.create_gate("keccak constraints", |meta| {
            let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());

            let mut constraints = vec![];
            let is_branch_child_cur =
                meta.query_advice(is_branch_child, Rotation::cur());

            let node_index_cur = meta.query_advice(node_index, Rotation::cur());

            /*
            TODO for leaf:
            Let's say we have a leaf n where
                n.Key = [10,6,3,5,7,0,1,2,12,1,10,3,10,14,0,10,1,7,13,3,0,4,12,9,9,2,0,3,1,0,3,8,2,13,9,6,8,14,11,12,12,4,11,1,7,7,1,15,4,1,12,6,11,3,0,4,2,0,5,11,5,7,0,16]
                n.Val = [2].
            Before put in a proof, a leaf is hashed:
            https://github.com/ethereum/go-ethereum/blob/master/trie/proof.go#L78
            But before being hashed, Key is put in compact form:
            https://github.com/ethereum/go-ethereum/blob/master/trie/hasher.go#L110
            Key becomes:
                [58,99,87,1,44,26,58,224,161,125,48,76,153,32,49,3,130,217,104,235,204,75,23,113,244,28,107,48,66,5,181,112]
            Then the node is RLP encoded:
            https://github.com/ethereum/go-ethereum/blob/master/trie/hasher.go#L157
            RLP:
                [226,160,58,99,87,1,44,26,58,224,161,125,48,76,153,32,49,3,130,217,104,235,204,75,23,113,244,28,107,48,66,5,181,112,2]
            Finally, the RLP is hashed:
                [32,34,39,131,73,65,47,37,211,142,206,231,172,16,11,203,33,107,30,7,213,226,2,174,55,216,4,117,220,10,186,68]

            In a proof (witness), we have [226, 160, ...] in columns s_rlp1, s_rlp2, ...
            Constraint 1: We need to compute a hash of this value and compare it with [32, 34, ...] which should be
                one of the branch children. lookup ...
                Constraint 1.1: s_keccak, c_keccak the same for all 16 children
                Constraint 1.2: for key = ind: s_keccak = converted s_advice and c_keccak = converted c_advice
                Constraint 1.3: we add additional row for a leaf prepared for keccak (17 words),
                  we do a lookup on this 17 words in s_keccak / c_keccak
            Constraint 2: We need to convert it back to non-compact format to get the remaining key.
                We need to verify the key until now (in nodes above) concatenated with the remaining key
                gives us the key where the storage change is happening.
            */

            // s_keccak is the same for all is_branch_child rows.
            // This is to enable easier comparison when in leaf row
            // where we need to compare the keccak output is the same as keccak of the modified node,
            // this way we just rotate back to one of the branch children rows and we get s_keccak there
            // (otherwise we would need iterate over all branch children rows (many rotations) and check
            // that at is_modified the value corresponds).
            for column in s_keccak.iter() {
                let s_keccak_prev =
                    meta.query_advice(*column, Rotation::prev());
                let s_keccak_cur = meta.query_advice(*column, Rotation::cur());
                constraints.push((
                    "s_keccak the same for all branch children",
                    q_not_first.clone()
                    * is_branch_child_cur.clone()
                    * node_index_cur.clone() // ignore if node_index = 0
                    * (s_keccak_cur.clone() - s_keccak_prev),
                ));
            }
            // c_keccak is the same for all is_branch_child rows.
            for column in c_keccak.iter() {
                let c_keccak_prev =
                    meta.query_advice(*column, Rotation::prev());
                let c_keccak_cur = meta.query_advice(*column, Rotation::cur());
                constraints.push((
                    "c_keccak the same for all branch children",
                    q_not_first.clone()
                    * is_branch_child_cur.clone()
                    * node_index_cur.clone() // ignore if node_index = 0
                    * (c_keccak_cur.clone() - c_keccak_prev),
                ));
            }

            // TODO: replace constraints above with permutation argument - for s_keccak and
            // c_keccak being the same in all branch children (similarly needs to be done
            // for sel1 and sel2 below).

            // NOTE: the reason why s_keccak and c_keccak need to be the same in all branch
            // children is that we need to check s_keccak and c_keccak in is_modified row,
            // but we don't know in advance at which position (in branch) is this row.

            // s_keccak and c_keccak correspond to s and c at the modified index
            let is_modified = meta.query_advice(is_modified, Rotation::cur());
            let is_at_first_nibble =
                meta.query_advice(is_at_first_nibble, Rotation::cur());

            let mut s_hash = vec![];
            let mut c_hash = vec![];
            for (ind, column) in s_advices.iter().enumerate() {
                s_hash.push(meta.query_advice(*column, Rotation::cur()));
                c_hash.push(meta.query_advice(c_advices[ind], Rotation::cur()));
            }
            let s_advices_words = into_words_expr(s_hash);
            let c_advices_words = into_words_expr(c_hash);

            // When it's NOT placeholder branch, is_modified = is_at_first_nibble.
            // When it's placeholder branch, is_modified != is_at_first_nibble.
            // This is used instead of having is_branch_s_placeholder and is_branch_c_placeholder columns -
            // we only have this info in branch init where we don't need additional columns.

            for (ind, column) in s_keccak.iter().enumerate() {
                // In placeholder branch (when is_modified != is_at_first_nibble) the following
                // constraint could be satisfied by attacker by putting hash of is_modified (while
                // it should be is_at_first_nibble), but then the attacker would need to
                // use is_modified node for leaf_key_in_added_branch (hash of it is in keccak
                // at is_at_first_nibble), but then the constraint of leaf_in_added_branch having
                // the same key (TODO this constraint in leaf_key_in_added_branch) except for
                // the nibble will fail.
                let s_keccak_cur = meta.query_advice(*column, Rotation::cur());
                constraints.push((
                    "s_keccak correspond to s_advices at the modified index",
                    q_not_first.clone()
                        * is_branch_child_cur.clone()
                        * is_at_first_nibble.clone() // is_at_first_nibble = is_modified when NOT placeholder
                        * is_modified.clone()
                        * (s_advices_words[ind].clone() - s_keccak_cur),
                ));
            }
            for (ind, column) in c_keccak.iter().enumerate() {
                let c_keccak_cur = meta.query_advice(*column, Rotation::cur());
                constraints.push((
                    "c_keccak correspond to c_advices at the modified index",
                    q_not_first.clone()
                        * is_branch_child_cur.clone()
                        * is_modified.clone()
                        * (c_advices_words[ind].clone() - c_keccak_cur),
                ));
            }

            // sel1 - denoting whether leaf is empty at modified_node.
            let c128 = Expression::Constant(F::from(128));
            let sel1_cur = meta.query_advice(sel1, Rotation::cur());

            // s_advices[0] = 128
            let s_advices0 = meta.query_advice(s_advices[0], Rotation::cur());
            constraints.push((
                "branch child sel1 s_advices0",
                q_not_first.clone()
                    * is_branch_child_cur.clone()
                    * is_modified.clone()
                    * (s_advices0 - c128.clone())
                    * sel1_cur.clone(),
            ));
            // s_advices[i] = 0 for i > 0
            for column in s_advices.iter().skip(1) {
                let s = meta.query_advice(*column, Rotation::cur());
                constraints.push((
                    "branch child sel1 s_advices",
                    q_not_first.clone()
                        * is_branch_child_cur.clone()
                        * is_modified.clone()
                        * s
                        * sel1_cur.clone(),
                ));
            }

            // sel2 - denoting whether leaf is empty at modified_node.
            let sel2_cur = meta.query_advice(sel2, Rotation::cur());

            // s_advices[0] = 128
            let c_advices0 = meta.query_advice(c_advices[0], Rotation::cur());
            constraints.push((
                "branch child sel2 c_advices0",
                q_not_first.clone()
                    * is_branch_child_cur.clone()
                    * is_modified.clone()
                    * (c_advices0 - c128.clone())
                    * sel2_cur.clone(),
            ));
            // c_advices[i] = 0 for i > 0
            for column in c_advices.iter().skip(1) {
                let c = meta.query_advice(*column, Rotation::cur());
                constraints.push((
                    "branch child sel2 c_advices",
                    q_not_first.clone()
                        * is_branch_child_cur.clone()
                        * is_modified.clone()
                        * c
                        * sel2_cur.clone(),
                ));
            }

            // TODO: constraint for is_modified = is_at_first_nibble, to do this
            // we can check modified_node = first_nibble in branch init and then check
            // in each branch node: modified_node_prev = modified_node_cur and
            // first_nibble_prev = first_nibble_cur, this way we can use only Rotation(-1).

            // TODO: permutation argument for sel1 and sel2 - need to be the same in all
            // branch children

            constraints
        });

        // Storage first level branch hash for S - root in last account leaf.
        // TODO: S and C can be in the same lookup, but it's easier to debug if we have two.
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

            let acc_s = meta.query_advice(acc_s, Rotation::cur());

            // TODO: acc_s currently doesn't have branch ValueNode info (which 128 if nil)
            let c128 = Expression::Constant(F::from(128));
            let mult_s = meta.query_advice(acc_mult_s, Rotation::cur());
            let branch_acc_s1 = acc_s + c128 * mult_s;

            let mut s_hash = vec![];
            for column in s_advices.iter() {
                // s (account leaf) key (-20), s nonce balance (-19), s storage codehash (-18),
                // c storage codehash (-17),
                s_hash.push(meta.query_advice(*column, Rotation(-18)));
            }
            let storage_root_words = into_words_expr(s_hash);

            let mut constraints = vec![];
            constraints.push((
                not_first_level.clone()
                    * is_last_branch_child.clone()
                    * is_account_leaf_storage_codehash_prev.clone()
                    * branch_acc_s1, // TODO: replace with acc_s once ValueNode is added
                meta.query_fixed(keccak_table[0], Rotation::cur()),
            ));
            for (ind, word) in storage_root_words.iter().enumerate() {
                let keccak_table_i =
                    meta.query_fixed(keccak_table[ind + 1], Rotation::cur());
                constraints.push((
                    not_first_level.clone()
                        * is_last_branch_child.clone()
                        * is_account_leaf_storage_codehash_prev.clone()
                        * word.clone(),
                    keccak_table_i,
                ));
            }

            constraints
        });

        // Storage first level branch hash for C - root in last account leaf.
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

            let acc_c = meta.query_advice(acc_c, Rotation::cur());

            // TODO: acc_c currently doesn't have branch ValueNode info (which 128 if nil)
            let c128 = Expression::Constant(F::from(128));
            let mult_c = meta.query_advice(acc_mult_c, Rotation::cur());
            let branch_acc_c1 = acc_c + c128 * mult_c;

            let mut c_hash = vec![];
            // storage root is always in s_advices
            for column in s_advices.iter() {
                // s (account leaf) key (-20), s nonce balance (-19), s storage codehash (-18),
                // c storage codehash (-17),
                c_hash.push(meta.query_advice(*column, Rotation(-17)));
            }
            let storage_root_words = into_words_expr(c_hash);

            let mut constraints = vec![];
            constraints.push((
                not_first_level.clone()
                    * is_last_branch_child.clone()
                    * is_account_leaf_storage_codehash_prev.clone()
                    * branch_acc_c1, // TODO: replace with acc_s once ValueNode is added
                meta.query_fixed(keccak_table[0], Rotation::cur()),
            ));
            for (ind, word) in storage_root_words.iter().enumerate() {
                let keccak_table_i =
                    meta.query_fixed(keccak_table[ind + 1], Rotation::cur());
                constraints.push((
                    not_first_level.clone()
                        * is_last_branch_child.clone()
                        * is_account_leaf_storage_codehash_prev.clone()
                        * word.clone(),
                    keccak_table_i,
                ));
            }

            constraints
        });

        // TODO: account first level branch hash for S and C - compared to root

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

        // Check hash of a leaf.
        meta.lookup_any(|meta| {
            let not_first_level =
                meta.query_fixed(not_first_level, Rotation::cur());

            let is_account_leaf_storage_codehash_s = meta.query_advice(
                is_account_leaf_storage_codehash_s,
                Rotation::cur(),
            );

            let acc_s = meta.query_advice(acc_s, Rotation::cur());

            let mut constraints = vec![];
            constraints.push((
                not_first_level.clone()
                    * is_account_leaf_storage_codehash_s.clone()
                    * acc_s,
                meta.query_fixed(keccak_table[0], Rotation::cur()),
            ));
            for (ind, column) in s_keccak.iter().enumerate() {
                // Any rotation that lands into branch can be used instead of -17.
                let s_keccak = meta.query_advice(*column, Rotation(-17));
                let keccak_table_i =
                    meta.query_fixed(keccak_table[ind + 1], Rotation::cur());
                constraints.push((
                    not_first_level.clone()
                        * is_account_leaf_storage_codehash_s.clone()
                        * s_keccak,
                    keccak_table_i,
                ));
            }

            constraints
        });

        meta.lookup_any(|meta| {
            let not_first_level =
                meta.query_fixed(not_first_level, Rotation::cur());

            let is_account_leaf_storage_codehash_c = meta.query_advice(
                is_account_leaf_storage_codehash_c,
                Rotation::cur(),
            );

            // Accumulated in s (not in c):
            let acc_s = meta.query_advice(acc_s, Rotation::cur());

            let mut constraints = vec![];
            constraints.push((
                not_first_level.clone()
                    * is_account_leaf_storage_codehash_c.clone()
                    * acc_s,
                meta.query_fixed(keccak_table[0], Rotation::cur()),
            ));
            for (ind, column) in c_keccak.iter().enumerate() {
                // Any rotation that lands into branch can be used instead of -17.
                let c_keccak = meta.query_advice(*column, Rotation(-17));
                let keccak_table_i =
                    meta.query_fixed(keccak_table[ind + 1], Rotation::cur());
                constraints.push((
                    not_first_level.clone()
                        * is_account_leaf_storage_codehash_c.clone()
                        * c_keccak,
                    keccak_table_i,
                ));
            }

            constraints
        });

        let branch_acc_s_chip = BranchAccChip::<F>::configure(
            meta,
            |meta| {
                let q_not_first =
                    meta.query_fixed(q_not_first, Rotation::cur());
                let is_branch_child =
                    meta.query_advice(is_branch_child, Rotation::cur());

                q_not_first * is_branch_child
            },
            s_rlp2,
            s_advices,
            acc_s,
            acc_mult_s,
            r_table.clone(),
        );

        let branch_acc_c_chip = BranchAccChip::<F>::configure(
            meta,
            |meta| {
                let q_not_first =
                    meta.query_fixed(q_not_first, Rotation::cur());
                let is_branch_child =
                    meta.query_advice(is_branch_child, Rotation::cur());

                q_not_first * is_branch_child
            },
            c_rlp2,
            c_advices,
            acc_c,
            acc_mult_c,
            r_table.clone(),
        );

        LeafKeyChip::<F>::configure(
            meta,
            |meta| {
                let not_first_level =
                    meta.query_fixed(not_first_level, Rotation::cur());
                let is_leaf_s = meta.query_advice(is_leaf_s, Rotation::cur());

                not_first_level * is_leaf_s
            },
            s_rlp1,
            s_rlp2,
            c_rlp1,
            s_advices,
            s_keccak[0],
            s_keccak[1],
            acc_s,
            acc_mult_s,
            key_rlc,
            key_rlc_mult,
            sel1,
            sel2,
            s_advices[IS_BRANCH_S_PLACEHOLDER_POS - LAYOUT_OFFSET],
            modified_node,
            r_table.clone(),
            true,
        );

        LeafKeyChip::<F>::configure(
            meta,
            |meta| {
                let not_first_level =
                    meta.query_fixed(not_first_level, Rotation::cur());
                let is_leaf_c = meta.query_advice(is_leaf_c, Rotation::cur());

                not_first_level * is_leaf_c
            },
            s_rlp1,
            s_rlp2,
            c_rlp1,
            s_advices,
            s_keccak[0],
            s_keccak[1],
            acc_s,
            acc_mult_s,
            key_rlc,
            key_rlc_mult,
            sel1,
            sel2,
            s_advices[IS_BRANCH_C_PLACEHOLDER_POS - LAYOUT_OFFSET],
            modified_node,
            r_table.clone(),
            false,
        );

        LeafKeyInAddedBranchChip::<F>::configure(
            meta,
            |meta| {
                let not_first_level =
                    meta.query_fixed(not_first_level, Rotation::cur());
                let is_leaf_c =
                    meta.query_advice(is_leaf_in_added_branch, Rotation::cur());

                not_first_level * is_leaf_c
            },
            s_rlp1,
            s_rlp2,
            c_rlp1,
            s_advices,
            s_keccak,
            c_keccak,
            acc_s,
            acc_mult_s,
            sel1,
            sel2,
            first_nibble,
            r_table.clone(),
            r_mult_table.clone(),
            keccak_table.clone(),
        );

        LeafValueChip::<F>::configure(
            meta,
            |meta| {
                let q_not_first =
                    meta.query_fixed(q_not_first, Rotation::cur());
                let is_leaf_s_value =
                    meta.query_advice(is_leaf_s_value, Rotation::cur());

                q_not_first * is_leaf_s_value
            },
            s_rlp1,
            s_rlp2,
            s_advices,
            s_keccak,
            keccak_table,
            acc_s,
            acc_mult_s,
            sel1,
            s_advices[IS_BRANCH_S_PLACEHOLDER_POS - LAYOUT_OFFSET],
            true,
            acc_r,
        );

        LeafValueChip::<F>::configure(
            meta,
            |meta| {
                let q_not_first =
                    meta.query_fixed(q_not_first, Rotation::cur());
                let is_leaf_c_value =
                    meta.query_advice(is_leaf_c_value, Rotation::cur());

                q_not_first * is_leaf_c_value
            },
            s_rlp1,
            s_rlp2,
            s_advices,
            c_keccak,
            keccak_table,
            acc_s,
            acc_mult_s,
            sel2,
            s_advices[IS_BRANCH_C_PLACEHOLDER_POS - LAYOUT_OFFSET],
            false,
            acc_r,
        );

        AccountLeafKeyChip::<F>::configure(
            meta,
            |meta| {
                let q_not_first =
                    meta.query_fixed(q_not_first, Rotation::cur());
                let is_account_leaf_key_s =
                    meta.query_advice(is_account_leaf_key_s, Rotation::cur());

                q_not_first * is_account_leaf_key_s
            },
            s_rlp1,
            s_rlp2,
            c_rlp1,
            s_advices,
            acc_s,
            acc_mult_s,
            key_rlc,
            key_rlc_mult,
            sel1,
            sel2,
            r_table.clone(),
        );

        AccountLeafNonceBalanceChip::<F>::configure(
            meta,
            |meta| {
                let q_not_first =
                    meta.query_fixed(q_not_first, Rotation::cur());
                let is_account_leaf_nonce_balance_s = meta.query_advice(
                    is_account_leaf_nonce_balance_s,
                    Rotation::cur(),
                );
                q_not_first * is_account_leaf_nonce_balance_s
            },
            s_rlp1,
            s_rlp2,
            c_rlp1,
            c_rlp2,
            s_advices,
            c_advices,
            acc_s,
            acc_mult_s,
            acc_mult_c,
            r_table.clone(),
        );

        // NOTE: storage leaf chip (LeafHashChip) checks the keccak, while
        // account leaf chip doesn't do this internally, the lookup is in mpt.rs
        AccountLeafStorageCodehashChip::<F>::configure(
            meta,
            |meta| {
                let q_not_first =
                    meta.query_fixed(q_not_first, Rotation::cur());
                let is_account_leaf_storage_codehash_s = meta.query_advice(
                    is_account_leaf_storage_codehash_s,
                    Rotation::cur(),
                );
                q_not_first * is_account_leaf_storage_codehash_s
            },
            s_rlp2,
            c_rlp2,
            s_advices,
            c_advices,
            acc_r,
            acc_s,
            acc_mult_s,
            true,
        );

        AccountLeafStorageCodehashChip::<F>::configure(
            meta,
            |meta| {
                let q_not_first =
                    meta.query_fixed(q_not_first, Rotation::cur());
                let is_account_leaf_storage_codehash_c = meta.query_advice(
                    is_account_leaf_storage_codehash_c,
                    Rotation::cur(),
                );
                q_not_first * is_account_leaf_storage_codehash_c
            },
            s_rlp2,
            c_rlp2,
            s_advices,
            c_advices,
            acc_r,
            acc_s,
            acc_mult_s,
            false,
        );

        MPTConfig {
            q_enable,
            q_not_first,
            not_first_level,
            is_branch_init,
            is_branch_child,
            is_last_branch_child,
            is_leaf_s,
            is_leaf_s_value,
            is_leaf_c,
            is_leaf_c_value,
            is_account_leaf_key_s,
            is_account_leaf_nonce_balance_s,
            is_account_leaf_storage_codehash_s,
            is_account_leaf_storage_codehash_c,
            node_index,
            is_modified,
            modified_node,
            is_at_first_nibble,
            first_nibble,
            is_leaf_in_added_branch,
            is_extension_node_s,
            is_extension_node_c,
            s_rlp1,
            s_rlp2,
            c_rlp1,
            c_rlp2,
            s_advices,
            c_advices,
            s_keccak,
            c_keccak,
            acc_s,
            acc_mult_s,
            acc_c,
            acc_mult_c,
            acc_r,
            sel1,
            sel2,
            r_table,
            branch_acc_s_chip,
            branch_acc_c_chip,
            key_rlc,
            key_rlc_mult,
            keccak_table,
            r_mult_table,
            _marker: PhantomData,
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
        is_leaf_s: bool,
        is_leaf_s_value: bool,
        is_leaf_c: bool,
        is_leaf_c_value: bool,
        is_account_leaf_key_s: bool,
        is_account_leaf_nonce_balance_s: bool,
        is_account_leaf_storage_codehash_s: bool,
        is_account_leaf_storage_codehash_c: bool,
        first_nibble: u8,
        is_leaf_in_added_branch: bool,
        is_extension_node_s: bool,
        is_extension_node_c: bool,
        offset: usize,
    ) -> Result<(), Error> {
        region.assign_advice(
            || "assign is_branch_init".to_string(),
            self.is_branch_init,
            offset,
            || Ok(F::from(is_branch_init as u64)),
        )?;

        region.assign_advice(
            || "assign is_branch_child".to_string(),
            self.is_branch_child,
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
            || "assign s_keccak 0".to_string(),
            self.s_keccak[0],
            offset,
            || Ok(F::zero()),
        )?;
        // because used for is_short
        region.assign_advice(
            || "assign s_keccak 1".to_string(),
            self.s_keccak[1],
            offset,
            || Ok(F::zero()),
        )?;

        region.assign_advice(
            || "assign is_last_branch_child".to_string(),
            self.is_last_branch_child,
            offset,
            || Ok(F::from(is_last_branch_child as u64)),
        )?;

        region.assign_advice(
            || "assign node_index".to_string(),
            self.node_index,
            offset,
            || Ok(F::from(node_index as u64)),
        )?;

        region.assign_advice(
            || "assign modified node".to_string(),
            self.modified_node,
            offset,
            || Ok(F::from(modified_node as u64)),
        )?;

        region.assign_advice(
            || "assign first_nibble".to_string(),
            self.first_nibble,
            offset,
            || Ok(F::from(first_nibble as u64)),
        )?;

        region.assign_advice(
            || "assign is_at_first_nibble".to_string(),
            self.is_at_first_nibble,
            offset,
            || Ok(F::from((first_nibble == node_index) as u64)),
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
            self.is_modified,
            offset,
            || Ok(F::from((modified_node == node_index) as u64)),
        )?;

        region.assign_advice(
            || "assign is_leaf_s".to_string(),
            self.is_leaf_s,
            offset,
            || Ok(F::from(is_leaf_s as u64)),
        )?;
        region.assign_advice(
            || "assign is_leaf_c".to_string(),
            self.is_leaf_c,
            offset,
            || Ok(F::from(is_leaf_c as u64)),
        )?;

        region.assign_advice(
            || "assign is_leaf_s_value".to_string(),
            self.is_leaf_s_value,
            offset,
            || Ok(F::from(is_leaf_s_value as u64)),
        )?;
        region.assign_advice(
            || "assign is_leaf_c_value".to_string(),
            self.is_leaf_c_value,
            offset,
            || Ok(F::from(is_leaf_c_value as u64)),
        )?;

        region.assign_advice(
            || "assign is account leaf key s".to_string(),
            self.is_account_leaf_key_s,
            offset,
            || Ok(F::from(is_account_leaf_key_s as u64)),
        )?;
        region.assign_advice(
            || "assign is account leaf nonce balance s".to_string(),
            self.is_account_leaf_nonce_balance_s,
            offset,
            || Ok(F::from(is_account_leaf_nonce_balance_s as u64)),
        )?;
        region.assign_advice(
            || "assign is account leaf storage codehash s".to_string(),
            self.is_account_leaf_storage_codehash_s,
            offset,
            || Ok(F::from(is_account_leaf_storage_codehash_s as u64)),
        )?;
        region.assign_advice(
            || "assign is account leaf storage codehash c".to_string(),
            self.is_account_leaf_storage_codehash_c,
            offset,
            || Ok(F::from(is_account_leaf_storage_codehash_c as u64)),
        )?;

        region.assign_advice(
            || "assign is leaf in added branch".to_string(),
            self.is_leaf_in_added_branch,
            offset,
            || Ok(F::from(is_leaf_in_added_branch as u64)),
        )?;
        region.assign_advice(
            || "assign is extension node s".to_string(),
            self.is_extension_node_s,
            offset,
            || Ok(F::from(is_extension_node_s as u64)),
        )?;
        region.assign_advice(
            || "assign is extension node c".to_string(),
            self.is_extension_node_c,
            offset,
            || Ok(F::from(is_extension_node_c as u64)),
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
        row: &Vec<u8>,
        offset: usize,
    ) -> Result<(), Error> {
        self.assign_row(
            region, row, true, false, false, 0, 0, false, false, false, false,
            false, false, false, false, 0, false, false, false, offset,
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
        row: &[u8],
        s_words: &[u64],
        c_words: &[u64],
        first_nibble: u8,
        offset: usize,
    ) -> Result<(), Error> {
        self.assign_row(
            region,
            row,
            false,
            true,
            node_index == 15,
            node_index,
            key,
            false,
            false,
            false,
            false,
            false,
            false,
            false,
            false,
            first_nibble,
            false,
            false,
            false,
            offset,
        )?;

        for (ind, column) in self.s_keccak.iter().enumerate() {
            region.assign_advice(
                || "Keccak s",
                *column,
                offset,
                || Ok(F::from(s_words[ind])),
            )?;
        }
        for (ind, column) in self.c_keccak.iter().enumerate() {
            region.assign_advice(
                || "Keccak c",
                *column,
                offset,
                || Ok(F::from(c_words[ind])),
            )?;
        }

        region.assign_advice(
            || "key rlc",
            self.key_rlc,
            offset,
            || Ok(key_rlc),
        )?;
        region.assign_advice(
            || "key rlc mult",
            self.key_rlc_mult,
            offset,
            || Ok(key_rlc_mult),
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

    pub(crate) fn assign(
        &self,
        mut layouter: impl Layouter<F>,
        witness: &[Vec<u8>],
    ) {
        layouter
            .assign_region(
                || "MPT",
                |mut region| {
                    let mut offset = 0;

                    let mut modified_node = 0;
                    let mut s_words: Vec<u64> = vec![0, 0, 0, 0];
                    let mut c_words: Vec<u64> = vec![0, 0, 0, 0];
                    let mut node_index: u8 = 0;
                    let mut acc_s = F::zero();
                    let mut acc_mult_s = F::zero();
                    let mut acc_nonce_balance = F::zero();
                    let mut acc_mult_nonce_balance = F::zero();

                    let mut acc_c = F::zero();
                    let mut acc_mult_c = F::zero();
                    let mut key_rlc = F::zero(); // used first for account address, then for storage key
                    let mut key_rlc_mult = F::one();
                    let mut key_rlc_sel = true; // If true, nibble is multiplied by 16, otherwise by 1.

                    let mut first_nibble: u8 = 0; // needed when leaf turned into branch and leaf moves into a branch where it's at first_nibble position

                    let mut not_first_level = F::zero();
                    // filter out rows that are just to be hashed
                    for (ind, row) in witness
                        .iter()
                        .filter(|r| {
                            r[r.len() - 1] != 5
                                && r[r.len() - 1] != 4
                                && r[r.len() - 1] != 9
                        })
                        .enumerate()
                    {
                        if ind == 19_usize && row[row.len() - 1] == 0 {
                            // when the first branch ends
                            not_first_level = F::one();
                        }
                        region.assign_fixed(
                            || "not first level",
                            self.not_first_level,
                            offset,
                            || Ok(not_first_level),
                        )?;

                        if row[row.len() - 1] == 0 {
                            // branch init
                            modified_node = row[BRANCH_0_KEY_POS];
                            node_index = 0;
                            first_nibble = row[FIRST_NIBBLE_POS];

                            // Get the child that is being changed and convert it to words to enable lookups:
                            let mut s_hash = witness
                                [ind + 1 + modified_node as usize]
                                [S_START..S_START + HASH_WIDTH]
                                .to_vec();
                            let mut c_hash = witness
                                [ind + 1 + modified_node as usize]
                                [C_START..C_START + HASH_WIDTH]
                                .to_vec();
                            s_words = self.convert_into_words(&s_hash);
                            c_words = self.convert_into_words(&c_hash);

                            if row[IS_BRANCH_S_PLACEHOLDER_POS] == 1 {
                                // We put hash of a nibble that drifted down to the added branch.
                                // This is needed to check the hash of leaf_in_added_branch.
                                s_hash = witness
                                    [ind + 1 + first_nibble as usize]
                                    [S_START..S_START + HASH_WIDTH]
                                    .to_vec();
                                s_words = self.convert_into_words(&s_hash);
                            }
                            if row[IS_BRANCH_C_PLACEHOLDER_POS] == 1 {
                                c_hash = witness
                                    [ind + 1 + modified_node as usize]
                                    [C_START..C_START + HASH_WIDTH]
                                    .to_vec();
                                c_words = self.convert_into_words(&c_hash);
                            }
                            // If no placeholder branch, we set first_nibble = modified_node. This
                            // is needed just to make some other constraints (s_keccak/c_keccak
                            // corresponds to the proper node) easier to write.
                            if row[IS_BRANCH_S_PLACEHOLDER_POS] == 0
                                && row[IS_BRANCH_C_PLACEHOLDER_POS] == 0
                            {
                                first_nibble = modified_node
                            }

                            self.q_enable.enable(&mut region, offset)?;
                            if ind == 0 {
                                region.assign_fixed(
                                    || "not first",
                                    self.q_not_first,
                                    offset,
                                    || Ok(F::zero()),
                                )?;
                            } else {
                                region.assign_fixed(
                                    || "not first",
                                    self.q_not_first,
                                    offset,
                                    || Ok(F::one()),
                                )?;
                            }
                            self.assign_branch_init(
                                &mut region,
                                &row[0..row.len() - 1].to_vec(),
                                offset,
                            )?;

                            // reassign (it was assigned to 0 in assign_row) branch_acc and branch_mult to proper values

                            // Branch (length 83) with two bytes of RLP meta data
                            // [248,81,128,128,...

                            // Branch (length 340) with three bytes of RLP meta data
                            // [249,1,81,128,16,...

                            acc_s = F::from(row[BRANCH_0_S_START] as u64)
                                + F::from(row[BRANCH_0_S_START + 1] as u64)
                                    * self.acc_r;
                            acc_mult_s = self.acc_r * self.acc_r;

                            if row[BRANCH_0_S_START] == 249 {
                                acc_s +=
                                    F::from(row[BRANCH_0_S_START + 2] as u64)
                                        * acc_mult_s;
                                acc_mult_s *= self.acc_r;
                            }

                            acc_c = F::from(row[BRANCH_0_C_START] as u64)
                                + F::from(row[BRANCH_0_C_START + 1] as u64)
                                    * self.acc_r;
                            acc_mult_c = self.acc_r * self.acc_r;

                            if row[BRANCH_0_C_START] == 249 {
                                acc_c +=
                                    F::from(row[BRANCH_0_C_START + 2] as u64)
                                        * acc_mult_c;
                                acc_mult_c *= self.acc_r;
                            }

                            self.assign_acc(
                                &mut region,
                                acc_s,
                                acc_mult_s,
                                acc_c,
                                acc_mult_c,
                                offset,
                            )?;

                            // sel1 and sel2 are here to distinguish whether it's the
                            // first or the second nibble of the key byte
                            // If sel1 = 1 and short, we have one nibble+48 in s_advices[0].
                            // If sel1 = 1 and long, we have nibble+48 in s_advices[1].
                            // If sel2 = 1 and short, we have 32 in s_advices[0].
                            // If sel2 = 1 and long, we have 32 in s_advices[1].

                            // Note that if the last branch is placeholder,
                            // sel1 and sel2 are still switched at this branch which
                            // needs to be considered in leaf rows.
                            let mut sel1 = F::zero();
                            let mut sel2 = F::zero();
                            if key_rlc_sel {
                                sel1 = F::one();
                            } else {
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

                            offset += 1;
                        } else if row[row.len() - 1] == 1 {
                            // branch child
                            self.q_enable.enable(&mut region, offset)?;
                            region.assign_fixed(
                                || "not first",
                                self.q_not_first,
                                offset,
                                || Ok(F::one()),
                            )?;

                            if node_index == 0 {
                                if key_rlc_sel {
                                    key_rlc += F::from(modified_node as u64)
                                        * F::from(16)
                                        * key_rlc_mult;
                                    // key_rlc_mult stays the same
                                } else {
                                    key_rlc += F::from(modified_node as u64)
                                        * key_rlc_mult;
                                    key_rlc_mult *= self.acc_r;
                                }
                                key_rlc_sel = !key_rlc_sel;
                                self.assign_branch_row(
                                    &mut region,
                                    node_index,
                                    modified_node,
                                    key_rlc,
                                    key_rlc_mult,
                                    &row[0..row.len() - 1].to_vec(),
                                    &s_words,
                                    &c_words,
                                    first_nibble,
                                    offset,
                                )?;
                            } else {
                                // assigning key_rlc and key_rlc_mult to avoid the possibility
                                // of bugs when wrong rotation would retrieve correct values
                                // and these values wouldn't be checked with constraints
                                // (constraints check only branch node with node_index=0)
                                self.assign_branch_row(
                                    &mut region,
                                    node_index,
                                    modified_node,
                                    F::zero(),
                                    F::zero(),
                                    &row[0..row.len() - 1].to_vec(),
                                    &s_words,
                                    &c_words,
                                    first_nibble,
                                    offset,
                                )?;
                                // sel1 is to distinguish whether s_words is [128, 0, 0, 0].
                                // sel2 is to distinguish whether c_words is [128, 0, 0, 0].
                                // Note that 128 comes from the RLP byte denoting empty leaf.
                                // Having [128, 0, 0, 0] for *_word means there is no node at
                                // this position in branch - for example, s_words
                                // is [128, 0, 0, 0] and c_words is some other value
                                // when new value is added to the trie
                                // (as opposed to just updating the value).
                                // Note that there is a potential attack if a leaf node
                                // is found with hash [128, 0, ..., 0],
                                // but the probability is negligible.
                                let mut sel1 = F::zero();
                                let mut sel2 = F::zero();
                                if s_words[0] == 128
                                    && s_words
                                        .iter()
                                        .skip(1)
                                        .filter(|w| **w == 0_u64)
                                        .count()
                                        == KECCAK_OUTPUT_WIDTH - 1
                                {
                                    sel1 = F::one();
                                }
                                if c_words[0] == 128
                                    && c_words
                                        .iter()
                                        .skip(1)
                                        .filter(|w| **w == 0_u64)
                                        .count()
                                        == KECCAK_OUTPUT_WIDTH - 1
                                {
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
                            }

                            // reassign (it was assigned to 0 in assign_row) branch_acc and branch_mult to proper values

                            // We need to distinguish between empty and non-empty node:
                            // empty node at position 1: 0
                            // non-empty node at position 1: 160

                            let c128 = F::from(128_u64);
                            let c160 = F::from(160_u64);

                            let compute_acc_and_mult =
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
                                                F::from(row[start + i] as u64)
                                                    * *branch_mult;
                                            *branch_mult *= self.acc_r;
                                        }
                                    }
                                };

                            // TODO: add branch ValueNode info

                            compute_acc_and_mult(
                                &mut acc_s,
                                &mut acc_mult_s,
                                S_RLP_START,
                                S_START,
                            );
                            compute_acc_and_mult(
                                &mut acc_c,
                                &mut acc_mult_c,
                                C_RLP_START,
                                C_START,
                            );
                            self.assign_acc(
                                &mut region,
                                acc_s,
                                acc_mult_s,
                                acc_c,
                                acc_mult_c,
                                offset,
                            )?;

                            offset += 1;
                            node_index += 1;
                        } else if row[row.len() - 1] == 2
                            || row[row.len() - 1] == 3
                            || row[row.len() - 1] == 6
                            || row[row.len() - 1] == 7
                            || row[row.len() - 1] == 8
                            || row[row.len() - 1] == 11
                            || row[row.len() - 1] == 13
                            || row[row.len() - 1] == 14
                            || row[row.len() - 1] == 15
                            || row[row.len() - 1] == 16
                            || row[row.len() - 1] == 17
                        {
                            // leaf s or leaf c or leaf key s or leaf key c
                            self.q_enable.enable(&mut region, offset)?;
                            region.assign_fixed(
                                || "not first",
                                self.q_not_first,
                                offset,
                                || Ok(F::one()),
                            )?;
                            let mut is_leaf_s = false;
                            let mut is_leaf_s_value = false;
                            let mut is_leaf_c = false;
                            let mut is_leaf_c_value = false;

                            let mut is_account_leaf_key_s = false;
                            let mut is_account_leaf_nonce_balance_s = false;
                            let mut is_account_leaf_storage_codehash_s = false;
                            let mut is_account_leaf_storage_codehash_c = false;

                            let mut is_leaf_in_added_branch = false;
                            let mut is_extension_node_s = false;
                            let mut is_extension_node_c = false;

                            if row[row.len() - 1] == 2 {
                                is_leaf_s = true;
                            } else if row[row.len() - 1] == 3 {
                                is_leaf_c = true;
                            } else if row[row.len() - 1] == 6 {
                                is_account_leaf_key_s = true;
                            } else if row[row.len() - 1] == 7 {
                                is_account_leaf_nonce_balance_s = true;
                            } else if row[row.len() - 1] == 8 {
                                is_account_leaf_storage_codehash_s = true;
                            } else if row[row.len() - 1] == 11 {
                                is_account_leaf_storage_codehash_c = true;
                                key_rlc = F::zero(); // account address until here, storage key from here on
                                key_rlc_mult = F::one();
                                key_rlc_sel = true;
                            } else if row[row.len() - 1] == 13 {
                                is_leaf_s_value = true;
                            } else if row[row.len() - 1] == 14 {
                                is_leaf_c_value = true;
                            } else if row[row.len() - 1] == 15 {
                                is_leaf_in_added_branch = true;
                            } else if row[row.len() - 1] == 16 {
                                is_extension_node_s = true;
                            } else if row[row.len() - 1] == 17 {
                                is_extension_node_c = true;
                            }

                            self.assign_row(
                                &mut region,
                                &row[0..row.len() - 1].to_vec(),
                                false,
                                false,
                                false,
                                0,
                                0,
                                is_leaf_s,
                                is_leaf_s_value,
                                is_leaf_c,
                                is_leaf_c_value,
                                is_account_leaf_key_s,
                                is_account_leaf_nonce_balance_s,
                                is_account_leaf_storage_codehash_s,
                                is_account_leaf_storage_codehash_c,
                                0,
                                is_leaf_in_added_branch,
                                is_extension_node_s,
                                is_extension_node_c,
                                offset,
                            )?;

                            let mut assign_long_short =
                                |region: &mut Region<'_, F>, long: bool| {
                                    let mut is_short = false;
                                    let mut is_long = false;
                                    if long {
                                        is_long = true;
                                    } else {
                                        is_short = true;
                                    }
                                    region
                                        .assign_advice(
                                            || "assign acc_s".to_string(),
                                            self.s_keccak[0],
                                            offset,
                                            || Ok(F::from(is_long as u64)),
                                        )
                                        .ok();
                                    region
                                        .assign_advice(
                                            || "assign acc_c".to_string(),
                                            self.s_keccak[1],
                                            offset,
                                            || Ok(F::from(is_short as u64)),
                                        )
                                        .ok();
                                };

                            // assign leaf accumulator that will be used as keccak input
                            let compute_acc_and_mult =
                                |acc: &mut F,
                                 mult: &mut F,
                                 start: usize,
                                 len: usize| {
                                    for i in 0..len {
                                        *acc += F::from(row[start + i] as u64)
                                            * *mult;
                                        *mult *= self.acc_r;
                                    }
                                };

                            let compute_key_rlc =
                                |key_rlc: &mut F,
                                 key_rlc_mult: &mut F,
                                 start: usize| {
                                    if !key_rlc_sel {
                                        // That means we had key_rlc_sel=true when setting rlc last time,
                                        // that means we have nibble+48 in s_advices[0].
                                        *key_rlc += F::from(
                                            (row[start + 1] - 48) as u64,
                                        ) * *key_rlc_mult;
                                        *key_rlc_mult *= self.acc_r;

                                        let len = row[start] as usize - 128;
                                        compute_acc_and_mult(
                                            key_rlc,
                                            key_rlc_mult,
                                            start + 2,
                                            len - 1, // -1 because one byte was already considered
                                        );
                                    } else {
                                        let len = row[start] as usize - 128;
                                        compute_acc_and_mult(
                                            key_rlc,
                                            key_rlc_mult,
                                            start + 2,
                                            len - 1, // -1 because the first byte doesn't contain any key byte (it's just 32)
                                        );
                                    }
                                };

                            // Storage leaf key
                            if row[row.len() - 1] == 2
                                || row[row.len() - 1] == 3
                            {
                                // Info whether leaf rlp is long or short.
                                assign_long_short(
                                    &mut region,
                                    witness[ind][0] == 248,
                                );

                                acc_s = F::zero();
                                acc_mult_s = F::one();
                                let len: usize;
                                if row[0] == 248 {
                                    len = (row[2] - 128) as usize + 3;
                                } else {
                                    len = (row[1] - 128) as usize + 2;
                                }
                                compute_acc_and_mult(
                                    &mut acc_s,
                                    &mut acc_mult_s,
                                    0,
                                    len,
                                );

                                self.assign_acc(
                                    &mut region,
                                    acc_s,
                                    acc_mult_s,
                                    F::zero(),
                                    F::zero(),
                                    offset,
                                )?;

                                // TODO: handle if branch or extension node is added
                                let mut start = S_START - 1;
                                if row[0] == 248 {
                                    // long RLP
                                    start = S_START;
                                }

                                // For leaf S and leaf C we need to start with the same rlc.
                                let mut key_rlc_new = key_rlc;
                                let mut key_rlc_mult_new = key_rlc_mult;
                                compute_key_rlc(
                                    &mut key_rlc_new,
                                    &mut key_rlc_mult_new,
                                    start,
                                );
                                region.assign_advice(
                                    || "assign key_rlc".to_string(),
                                    self.key_rlc,
                                    offset,
                                    || Ok(key_rlc_new),
                                )?;
                            }

                            if row[row.len() - 1] == 6 {
                                acc_s = F::zero();
                                acc_mult_s = F::one();
                                // 35 = 2 (leaf rlp) + 1 (key rlp) + key_len
                                let key_len = (row[2] - 128) as usize;
                                for b in row.iter().take(3 + key_len) {
                                    acc_s += F::from(*b as u64) * acc_mult_s;
                                    acc_mult_s *= self.acc_r;
                                }
                                self.assign_acc(
                                    &mut region,
                                    acc_s,
                                    acc_mult_s,
                                    F::zero(),
                                    F::zero(),
                                    offset,
                                )?;

                                // For leaf S and leaf C we need to start with the same rlc.
                                let mut key_rlc_new = key_rlc;
                                let mut key_rlc_mult_new = key_rlc_mult;
                                compute_key_rlc(
                                    &mut key_rlc_new,
                                    &mut key_rlc_mult_new,
                                    S_START,
                                );
                                region.assign_advice(
                                    || "assign key_rlc".to_string(),
                                    self.key_rlc,
                                    offset,
                                    || Ok(key_rlc_new),
                                )?;
                            } else if row[row.len() - 1] == 7 {
                                // s_rlp1, s_rlp2
                                compute_acc_and_mult(
                                    &mut acc_s,
                                    &mut acc_mult_s,
                                    S_START - 2,
                                    2,
                                );
                                // c_rlp1, c_rlp2
                                compute_acc_and_mult(
                                    &mut acc_s,
                                    &mut acc_mult_s,
                                    C_START - 2,
                                    2,
                                );
                                // nonce
                                compute_acc_and_mult(
                                    &mut acc_s,
                                    &mut acc_mult_s,
                                    S_START,
                                    row[S_START] as usize - 128 + 1, // +1 for byte with length info
                                );
                                // It's easier to constrain (in account_leaf_nonce_balance.rs)
                                // the multiplier if we store acc_mult both after nonce and after balance.
                                let acc_mult_tmp = acc_mult_s;
                                // balance
                                compute_acc_and_mult(
                                    &mut acc_s,
                                    &mut acc_mult_s,
                                    C_START,
                                    row[C_START] as usize - 128 + 1, // +1 for byte with length info
                                );

                                self.assign_acc(
                                    &mut region,
                                    acc_s,
                                    acc_mult_s,
                                    F::zero(),
                                    acc_mult_tmp,
                                    offset,
                                )?;

                                acc_nonce_balance = acc_s;
                                acc_mult_nonce_balance = acc_mult_s;
                            } else if row[row.len() - 1] == 8
                                || row[row.len() - 1] == 11
                            {
                                if row[row.len() - 1] == 11 {
                                    // Leaf key and nonce/balance for S and C
                                    // are always the same, so we just use
                                    // accumulated value from S.
                                    acc_s = acc_nonce_balance;
                                    acc_mult_s = acc_mult_nonce_balance;
                                }
                                // storage
                                compute_acc_and_mult(
                                    &mut acc_s,
                                    &mut acc_mult_s,
                                    S_START - 1,
                                    HASH_WIDTH + 1,
                                );
                                // code hash
                                compute_acc_and_mult(
                                    &mut acc_s,
                                    &mut acc_mult_s,
                                    C_START - 1,
                                    HASH_WIDTH + 1,
                                );
                                self.assign_acc(
                                    &mut region,
                                    acc_s,
                                    acc_mult_s,
                                    F::zero(),
                                    F::zero(),
                                    offset,
                                )?;
                            } else if row[row.len() - 1] == 15 && row[1] != 0 {
                                // row[1] != 0 just to avoid usize problems below (when row doesn't need to be assigned)
                                // Info whether leaf rlp is long or short.
                                assign_long_short(
                                    &mut region,
                                    witness[ind][0] == 248,
                                );

                                acc_s = F::zero();
                                acc_mult_s = F::one();
                                let len: usize;
                                if row[0] == 248 {
                                    len = (row[2] - 128) as usize + 3;
                                } else {
                                    len = (row[1] - 128) as usize + 2;
                                }
                                compute_acc_and_mult(
                                    &mut acc_s,
                                    &mut acc_mult_s,
                                    0,
                                    len,
                                );

                                self.assign_acc(
                                    &mut region,
                                    acc_s,
                                    acc_mult_s,
                                    F::zero(),
                                    F::zero(),
                                    offset,
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
        self.load_r_mult_table(_layouter).ok();

        Ok(())
    }

    // see bits_to_u64_words_le
    fn convert_into_words(&self, message: &[u8]) -> Vec<u64> {
        let words_total = message.len() / 8;
        let mut words: Vec<u64> = vec![0; words_total];

        for i in 0..words_total {
            let mut word_bits: [u8; 8] = Default::default();
            word_bits.copy_from_slice(&message[i * 8..i * 8 + 8]);
            words[i] = u64::from_le_bytes(word_bits);
        }

        words
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

                    let keccak_output = self.convert_into_words(&hash);

                    for (ind, column) in self.keccak_table.iter().enumerate() {
                        if ind == 0 {
                            continue;
                        }
                        let val = keccak_output[ind - KECCAK_INPUT_WIDTH];
                        region.assign_fixed(
                            || "Keccak table",
                            *column,
                            offset,
                            || Ok(F::from(val)),
                        )?;
                    }
                    offset += 1;
                }

                Ok(())
            },
        )
    }

    fn load_r_mult_table(
        &self,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "r multiplication table",
            |mut region| {
                let mut offset = 0;
                let mut mult = F::one();
                for ind in 0..(2 * HASH_WIDTH + 1) {
                    region.assign_fixed(
                        || "multiplication table",
                        self.r_mult_table[0],
                        offset,
                        || Ok(F::from(ind as u64)),
                    )?;

                    region.assign_fixed(
                        || "multiplication table",
                        self.r_mult_table[1],
                        offset,
                        || Ok(mult),
                    )?;
                    mult = mult * self.acc_r;

                    offset += 1;
                }

                Ok(())
            },
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use halo2::{
        circuit::{Layouter, SimpleFloorPlanner},
        dev::{MockProver, VerifyFailure},
        plonk::{
            create_proof, keygen_pk, keygen_vk, verify_proof, Advice, Circuit,
            Column, ConstraintSystem, Error,
        },
        poly::commitment::Params,
        transcript::{Blake2bRead, Blake2bWrite, Challenge255},
    };

    use pairing::{arithmetic::FieldExt, bn256::Fr as Fp};
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
                        // leaves or branch RLP
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
                let file = std::fs::File::open(f.path());
                let reader = std::io::BufReader::new(file.unwrap());
                let w: Vec<Vec<u8>> = serde_json::from_reader(reader).unwrap();
                let circuit = MyCircuit::<Fp> {
                    _marker: PhantomData,
                    witness: w,
                };

                let prover =
                    MockProver::<Fp>::run(9, &circuit, vec![]).unwrap();
                assert_eq!(prover.verify(), Ok(()));

                /*
                const K: u32 = 4;
                let params: Params<EqAffine> = Params::new(K);
                let empty_circuit = MyCircuit::<pallas::Base> {
                    _marker: PhantomData,
                    witness: vec![],
                };

                let vk = keygen_vk(&params, &empty_circuit)
                    .expect("keygen_vk should not fail");

                let pk = keygen_pk(&params, vk, &empty_circuit)
                    .expect("keygen_pk should not fail");

                let mut transcript =
                    Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
                create_proof(&params, &pk, &[circuit], &[&[]], &mut transcript)
                    .expect("proof generation should not fail");
                let proof = transcript.finalize();

                let msm = params.empty_msm();
                let mut transcript =
                    Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
                let guard = verify_proof(
                    &params,
                    pk.get_vk(),
                    msm,
                    &[],
                    &mut transcript,
                )
                .unwrap();
                let msm = guard.clone().use_challenges();
                assert!(msm.eval());
                */
            });
    }
}
