use halo2::{
    circuit::{Layouter, Region},
    plonk::{
        Advice, Column, ConstraintSystem, Error, Expression, Fixed, Selector,
    },
    poly::Rotation,
};
use keccak256::plain::Keccak;
use pasta_curves::arithmetic::FieldExt;
use std::{convert::TryInto, marker::PhantomData};

use crate::param::{
    BRANCH_0_C_START, BRANCH_0_KEY_POS, BRANCH_0_S_START, C_RLP_START, C_START,
    HASH_WIDTH, KECCAK_INPUT_WIDTH, KECCAK_OUTPUT_WIDTH, S_RLP_START, S_START,
};
use crate::{
    account_leaf_key::{AccountLeafKeyChip, AccountLeafKeyConfig},
    account_leaf_nonce_balance::{
        AccountLeafNonceBalanceChip, AccountLeafNonceBalanceConfig,
    },
    account_leaf_storage_codehash::{
        AccountLeafStorageCodehashChip, AccountLeafStorageCodehashConfig,
    },
    branch_acc::BranchAccChip,
    leaf_key::{LeafKeyChip, LeafKeyConfig},
    leaf_value::{LeafValueChip, LeafValueConfig},
    param::LAYOUT_OFFSET,
};
use crate::{branch_acc::BranchAccConfig, param::WITNESS_ROW_WIDTH};

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
    sel1: Column<Advice>,
    sel2: Column<Advice>,
    r_table: Vec<Expression<F>>,
    branch_acc_s_chip: BranchAccConfig,
    branch_acc_c_chip: BranchAccConfig,
    account_leaf_key_chip: AccountLeafKeyConfig,
    account_leaf_nonce_balance_chip_s: AccountLeafNonceBalanceConfig,
    account_leaf_storage_codehash_chip_s: AccountLeafStorageCodehashConfig,
    account_leaf_storage_codehash_chip_c: AccountLeafStorageCodehashConfig,
    key_rlc: Column<Advice>, // used first for account address, then for storage key
    key_rlc_mult: Column<Advice>,
    keccak_table: [Column<Fixed>; KECCAK_INPUT_WIDTH + KECCAK_OUTPUT_WIDTH],
    leaf_s_key_chip: LeafKeyConfig,
    leaf_c_key_chip: LeafKeyConfig,
    leaf_s_value_chip: LeafValueConfig,
    leaf_c_value_chip: LeafValueConfig,
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
                    exp = exp * Expression::Constant(F::from_u64(256));
                }
                words.push(word)
            }

            words
        };

        // TODO: range proofs for bytes

        meta.create_gate("general constraints", |meta| {
            let q_enable = meta.query_selector(q_enable);

            let mut constraints = vec![];
            let is_branch_init_cur =
                meta.query_advice(is_branch_init, Rotation::cur());
            let is_branch_child_cur =
                meta.query_advice(is_branch_child, Rotation::cur());
            let is_last_branch_child_cur =
                meta.query_advice(is_last_branch_child, Rotation::cur());
            let is_leaf_s = meta.query_advice(is_leaf_s, Rotation::cur());
            let is_leaf_s_value =
                meta.query_advice(is_leaf_s_value, Rotation::cur());
            let is_leaf_c = meta.query_advice(is_leaf_c, Rotation::cur());
            let is_leaf_c_value =
                meta.query_advice(is_leaf_c_value, Rotation::cur());

            let is_account_leaf_key_s =
                meta.query_advice(is_account_leaf_key_s, Rotation::cur());
            let is_account_leaf_nonce_balance_s = meta
                .query_advice(is_account_leaf_nonce_balance_s, Rotation::cur());
            let is_account_leaf_storage_codehash_s = meta.query_advice(
                is_account_leaf_storage_codehash_s,
                Rotation::cur(),
            );

            let is_account_leaf_storage_codehash_c = meta.query_advice(
                is_account_leaf_storage_codehash_c,
                Rotation::cur(),
            );
            let sel1 = meta.query_advice(sel1, Rotation::cur());
            let sel2 = meta.query_advice(sel2, Rotation::cur());

            let bool_check_is_branch_init = is_branch_init_cur.clone()
                * (one.clone() - is_branch_init_cur.clone());
            let bool_check_is_branch_child = is_branch_child_cur.clone()
                * (one.clone() - is_branch_child_cur.clone());
            let bool_check_is_last_branch_child = is_last_branch_child_cur
                .clone()
                * (one.clone() - is_last_branch_child_cur.clone());
            let bool_check_is_leaf_s =
                is_leaf_s.clone() * (one.clone() - is_leaf_s.clone());
            let bool_check_is_leaf_c =
                is_leaf_c.clone() * (one.clone() - is_leaf_c.clone());

            let bool_check_is_leaf_s_value = is_leaf_s_value.clone()
                * (one.clone() - is_leaf_s_value.clone());
            let bool_check_is_leaf_c_value = is_leaf_c_value.clone()
                * (one.clone() - is_leaf_c_value.clone());

            let bool_check_is_account_leaf_key_s = is_account_leaf_key_s
                .clone()
                * (one.clone() - is_account_leaf_key_s.clone());
            let bool_check_is_account_nonce_balance_s =
                is_account_leaf_nonce_balance_s.clone()
                    * (one.clone() - is_account_leaf_nonce_balance_s.clone());
            let bool_check_is_account_storage_codehash_s =
                is_account_leaf_storage_codehash_s.clone()
                    * (one.clone()
                        - is_account_leaf_storage_codehash_s.clone());
            let bool_check_is_account_storage_codehash_c =
                is_account_leaf_storage_codehash_c.clone()
                    * (one.clone()
                        - is_account_leaf_storage_codehash_c.clone());

            let bool_check_sel1 = sel1.clone() * (one.clone() - sel1.clone());
            let bool_check_sel2 = sel2.clone() * (one.clone() - sel2.clone());

            // TODO: sel1 + sel2 = 1

            // TODO: is_last_branch_child followed by is_leaf_s followed by is_leaf_c
            // followed by is_leaf_key_nibbles
            // is_leaf_s_value ...

            // TODO: account leaf constraints (order and also that account leaf selectors
            // are truea only in account proof part & normal leaf selectors are true only
            // in storage part, for this we also need account proof selector and storage
            // proof selector - bool and strictly increasing for example. Also, is_account_leaf_key_nibbles
            // needs to be 1 in the previous row when the account/storage selector changes.

            let node_index_cur = meta.query_advice(node_index, Rotation::cur());
            let modified_node =
                meta.query_advice(modified_node, Rotation::cur());
            let is_modified = meta.query_advice(is_modified, Rotation::cur());

            let s_rlp1 = meta.query_advice(s_rlp1, Rotation::cur());
            let s_rlp2 = meta.query_advice(s_rlp2, Rotation::cur());

            let c_rlp1 = meta.query_advice(c_rlp1, Rotation::cur());
            let c_rlp2 = meta.query_advice(c_rlp2, Rotation::cur());

            constraints.push((
                "bool check is branch init",
                q_enable.clone() * bool_check_is_branch_init,
            ));
            constraints.push((
                "bool check is branch child",
                q_enable.clone() * bool_check_is_branch_child,
            ));
            constraints.push((
                "bool check is last branch child",
                q_enable.clone() * bool_check_is_last_branch_child,
            ));
            constraints.push((
                "bool check is leaf s",
                q_enable.clone() * bool_check_is_leaf_s,
            ));
            constraints.push((
                "bool check is leaf c",
                q_enable.clone() * bool_check_is_leaf_c,
            ));

            constraints.push((
                "bool check is leaf s value",
                q_enable.clone() * bool_check_is_leaf_s_value,
            ));
            constraints.push((
                "bool check is leaf c value",
                q_enable.clone() * bool_check_is_leaf_c_value,
            ));

            constraints.push((
                "bool check is leaf account key s",
                q_enable.clone() * bool_check_is_account_leaf_key_s,
            ));
            constraints.push((
                "bool check is leaf account nonce balance s",
                q_enable.clone() * bool_check_is_account_nonce_balance_s,
            ));
            constraints.push((
                "bool check is leaf account storage codehash s",
                q_enable.clone() * bool_check_is_account_storage_codehash_s,
            ));
            constraints.push((
                "bool check is leaf account storage codehash c",
                q_enable.clone() * bool_check_is_account_storage_codehash_c,
            ));
            constraints
                .push(("bool check sel1", q_enable.clone() * bool_check_sel1));
            constraints
                .push(("bool check sel2", q_enable.clone() * bool_check_sel2));

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

            let bool_check_is_modified =
                is_modified.clone() * (one.clone() - is_modified.clone());
            constraints.push((
                "bool check is_modified",
                q_enable.clone() * bool_check_is_modified,
            ));

            // is_modified is:
            //   0 when node_index_cur != key
            //   1 when node_index_cur == key
            constraints.push((
                "is modified",
                q_enable.clone()
                    * is_branch_child_cur.clone()
                    * is_modified
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
                    * (node_index_prev.clone()
                        - Expression::Constant(F::from_u64(15 as u64))), // node_index has to be 15
            ));

            // When node_index is not 15, is_last_branch_child needs to be 0.
            constraints.push((
                "is last branch child 1",
                q_not_first.clone()
                    * is_last_branch_child_cur.clone()
                    * (node_index_cur.clone() // for this to work properly is_last_branch_child needs to have value 1 only when is_branch_child
                        - Expression::Constant(F::from_u64(15 as u64))),
            ));
            // When node_index is 15, is_last_branch_child needs to be 1.
            constraints.push((
                "is last branch child 2",
                q_not_first.clone()
                    * (one.clone() - is_branch_init_prev.clone()) // ignore if previous row was is_branch_init (here is_branch_child changes too)
                    * (is_last_branch_child_prev - one.clone())
                    * (is_branch_child_prev.clone()
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
                    * is_branch_child_cur.clone()
                    * node_index_cur.clone() // ignore if node_index = 0
                    * (modified_node_cur.clone() - modified_node_prev),
            ));

            // For the first branch node (node_index = 0), the key rlc needs to be:
            // key_rlc = key_rlc::Rotation(-17) + modified_node * key_rlc_mult

            // We need to check whether we are in the first storage level, we can do this
            // by checking whether is_account_leaf_storage_codehash_c is true in the previous row.

            // -2 because we are in the first branch child and there is branch init row in between
            let is_account_leaf_storage_codehash_prev = meta
                .query_advice(is_account_leaf_storage_codehash_c, Rotation(-2));

            let c16 = Expression::Constant(F::from_u64(16));
            // If sel1 = 1, then modified_node is multiplied by 16.
            // If sel2 = 1, then modified_node is multiplied by 1.
            // NOTE: modified_node presents nibbles: n0, n1, ...
            // key_rlc = (n0 * 16 + n1) + (n2 * 16 + n3) * r + (n4 * 16 + n5) * r^2 + ...
            let sel1_prev = meta.query_advice(sel1, Rotation(-17));
            let sel2_prev = meta.query_advice(sel2, Rotation(-17));
            let sel1_cur = meta.query_advice(sel1, Rotation::cur());
            let sel2_cur = meta.query_advice(sel2, Rotation::cur());

            let key_rlc_prev = meta.query_advice(key_rlc, Rotation(-17));
            let key_rlc_cur = meta.query_advice(key_rlc, Rotation::cur());
            let key_rlc_mult_prev =
                meta.query_advice(key_rlc_mult, Rotation(-17));
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
                    * (sel1_cur.clone() + sel1_prev.clone() - one.clone()),
            ));
            constraints.push((
                "first branch children sel2 0->1->0->...",
                not_first_level.clone()
                    * is_branch_init_prev.clone()
                    * (one.clone() - is_account_leaf_storage_codehash_prev.clone()) // When this is 0, we check as for the first level key rlc.
                    * (sel2_cur.clone() + sel2_prev.clone() - one.clone()),
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
                    * (one.clone() - not_first_level.clone())
                    * is_branch_init_prev.clone()
                    * sel2_cur.clone(),
            ));

            // First storage level.
            constraints.push((
                "storage first level key_rlc",
                q_not_first.clone()
                    * is_account_leaf_storage_codehash_prev.clone()
                    * is_branch_init_prev.clone()
                    * (key_rlc_cur - modified_node_cur * c16.clone()),
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
                    * (sel1_cur.clone() - one.clone()),
            ));
            constraints.push((
                "storage first level key_rlc sel2",
                q_not_first.clone()
                    * is_account_leaf_storage_codehash_prev.clone()
                    * is_branch_init_prev.clone()
                    * sel2_cur.clone(),
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
                    * two_rlp_bytes_s.clone()
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
                    * three_rlp_bytes_s.clone()
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
                q_enable.clone()
                    * is_branch_init_cur.clone()
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

            // s_keccak is the same for all is_branch_child rows
            // (this is to enable easier comparison when in keccak leaf row
            // where we need to compare the keccak output is the same as keccak of the modified node)
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
            // c_keccak is the same for all is_branch_child rows
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

            // s_keccak and c_keccak correspond to s and c at the modified index
            let is_modified = meta.query_advice(is_modified, Rotation::cur());

            let mut s_hash = vec![];
            let mut c_hash = vec![];
            for (ind, column) in s_advices.iter().enumerate() {
                s_hash.push(meta.query_advice(*column, Rotation::cur()));
                c_hash.push(meta.query_advice(c_advices[ind], Rotation::cur()));
            }
            let s_advices_words = into_words_expr(s_hash);
            let c_advices_words = into_words_expr(c_hash);

            for (ind, column) in s_keccak.iter().enumerate() {
                let s_keccak_cur = meta.query_advice(*column, Rotation::cur());
                constraints.push((
                    "s_keccak correspond to s_advices at the modified index",
                    q_not_first.clone()
                        * is_branch_child_cur.clone()
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

            constraints
        });

        // Storage first level branch hash for S - root in last account leaf.
        // TODO: S and C can be in the same lookup, but it's easier to debug if we have two.
        meta.lookup(|meta| {
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
            let c128 = Expression::Constant(F::from_u64(128));
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
        meta.lookup(|meta| {
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
            let c128 = Expression::Constant(F::from_u64(128));
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
        meta.lookup(|meta| {
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
            let c128 = Expression::Constant(F::from_u64(128));
            let mult_s = meta.query_advice(acc_mult_s, Rotation::cur());
            let branch_acc_s1 = acc_s + c128 * mult_s;

            let mut constraints = vec![];
            constraints.push((
                not_first_level.clone()
                    * is_last_branch_child.clone()
                    * (one.clone() - is_account_leaf_storage_codehash_prev.clone()) // we don't check this in the first storage level
                    * branch_acc_s1, // TODO: replace with acc_s once ValueNode is added
                meta.query_fixed(keccak_table[0], Rotation::cur()),
            ));
            for (ind, column) in s_keccak.iter().enumerate() {
                // Any rotation that lands into branch can be used instead of -17.
                let s_keccak = meta.query_advice(*column, Rotation(-17));
                let keccak_table_i =
                    meta.query_fixed(keccak_table[ind + 1], Rotation::cur());
                constraints.push((
                    not_first_level.clone()
                        * is_last_branch_child.clone()
                        * (one.clone()
                            - is_account_leaf_storage_codehash_prev.clone()) // we don't check this in the first storage level
                        * s_keccak,
                    keccak_table_i,
                ));
            }

            constraints
        });

        // Check if (accumulated_c_rlc, hash1, hash2, hash3, hash4) is in keccak table,
        // where hash1, hash2, hash3, hash4 are stored in the previous branch and
        // accumulated_c_rlc presents the branch RLC.
        meta.lookup(|meta| {
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
            let c128 = Expression::Constant(F::from_u64(128));
            let mult_c = meta.query_advice(acc_mult_c, Rotation::cur());
            let branch_acc_c1 = acc_c + c128 * mult_c;

            let mut constraints = vec![];
            constraints.push((
                not_first_level.clone()
                    * is_last_branch_child.clone()
                    * (one.clone() - is_account_leaf_storage_codehash_prev.clone()) // we don't check this in the first storage level
                    * branch_acc_c1, // TODO: replace with acc_c once ValueNode is added
                meta.query_fixed(keccak_table[0], Rotation::cur()),
            ));
            for (ind, column) in c_keccak.iter().enumerate() {
                // Any rotation that lands into branch can be used instead of -17.
                let c_keccak = meta.query_advice(*column, Rotation(-17));
                let keccak_table_i =
                    meta.query_fixed(keccak_table[ind + 1], Rotation::cur());
                constraints.push((
                    not_first_level.clone()
                        * is_last_branch_child.clone()
                        * (one.clone() - is_account_leaf_storage_codehash_prev.clone()) // we don't check this in the first storage level
                        * c_keccak,
                    keccak_table_i,
                ));
            }

            constraints
        });

        // Check hash of a leaf.
        meta.lookup(|meta| {
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

        meta.lookup(|meta| {
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

        let leaf_s_key_chip = LeafKeyChip::<F>::configure(
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
            r_table.clone(),
            true,
        );

        let leaf_c_key_chip = LeafKeyChip::<F>::configure(
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
            r_table.clone(),
            false,
        );

        let leaf_s_value_chip = LeafValueChip::<F>::configure(
            meta,
            |meta| {
                let q_enable = meta.query_selector(q_enable);
                let is_leaf_s_value =
                    meta.query_advice(is_leaf_s_value, Rotation::cur());

                q_enable * is_leaf_s_value
            },
            s_rlp1,
            s_rlp2,
            s_advices,
            s_keccak,
            keccak_table,
            acc_s,
            acc_mult_s,
            acc_r,
        );

        let leaf_c_value_chip = LeafValueChip::<F>::configure(
            meta,
            |meta| {
                let q_enable = meta.query_selector(q_enable);
                let is_leaf_c_value =
                    meta.query_advice(is_leaf_c_value, Rotation::cur());

                q_enable * is_leaf_c_value
            },
            s_rlp1,
            s_rlp2,
            s_advices,
            c_keccak,
            keccak_table,
            acc_s,
            acc_mult_s,
            acc_r,
        );

        let account_leaf_key_chip = AccountLeafKeyChip::<F>::configure(
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

        let account_leaf_nonce_balance_chip_s =
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
        let account_leaf_storage_codehash_chip_s =
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

        let account_leaf_storage_codehash_chip_c =
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
            account_leaf_key_chip,
            account_leaf_nonce_balance_chip_s,
            account_leaf_storage_codehash_chip_s,
            account_leaf_storage_codehash_chip_c,
            key_rlc,
            key_rlc_mult,
            keccak_table,
            leaf_s_key_chip,
            leaf_c_key_chip,
            leaf_s_value_chip,
            leaf_c_value_chip,
            _marker: PhantomData,
        }
    }

    fn assign_row(
        &self,
        region: &mut Region<'_, F>,
        row: &Vec<u8>,
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
        offset: usize,
    ) -> Result<(), Error> {
        region.assign_advice(
            || format!("assign is_branch_init"),
            self.is_branch_init,
            offset,
            || Ok(F::from_u64(is_branch_init as u64)),
        )?;

        region.assign_advice(
            || format!("assign is_branch_child"),
            self.is_branch_child,
            offset,
            || Ok(F::from_u64(is_branch_child as u64)),
        )?;

        region.assign_advice(
            || format!("assign acc_s"),
            self.acc_s,
            offset,
            || Ok(F::zero()),
        )?;

        region.assign_advice(
            || format!("assign acc_mult_s"),
            self.acc_mult_s,
            offset,
            || Ok(F::zero()),
        )?;

        region.assign_advice(
            || format!("assign acc_c"),
            self.acc_c,
            offset,
            || Ok(F::zero()),
        )?;

        region.assign_advice(
            || format!("assign acc_mult_c"),
            self.acc_mult_c,
            offset,
            || Ok(F::zero()),
        )?;

        // because used for is_long
        region.assign_advice(
            || format!("assign s_keccak 0"),
            self.s_keccak[0],
            offset,
            || Ok(F::zero()),
        )?;
        // because used for is_short
        region.assign_advice(
            || format!("assign s_keccak 1"),
            self.s_keccak[1],
            offset,
            || Ok(F::zero()),
        )?;

        region.assign_advice(
            || format!("assign is_last_branch_child"),
            self.is_last_branch_child,
            offset,
            || Ok(F::from_u64(is_last_branch_child as u64)),
        )?;

        region.assign_advice(
            || format!("assign node_index"),
            self.node_index,
            offset,
            || Ok(F::from_u64(node_index as u64)),
        )?;

        region.assign_advice(
            || format!("assign modified node"),
            self.modified_node,
            offset,
            || Ok(F::from_u64(modified_node as u64)),
        )?;

        region.assign_advice(
            || format!("assign key rlc"),
            self.key_rlc,
            offset,
            || Ok(F::zero()),
        )?;

        region.assign_advice(
            || format!("assign key rlc mult"),
            self.key_rlc_mult,
            offset,
            || Ok(F::zero()),
        )?;

        region.assign_advice(
            || format!("assign sel1"),
            self.sel1,
            offset,
            || Ok(F::zero()),
        )?;
        region.assign_advice(
            || format!("assign sel2"),
            self.sel2,
            offset,
            || Ok(F::zero()),
        )?;

        region.assign_advice(
            || format!("assign is_modified"),
            self.is_modified,
            offset,
            || Ok(F::from_u64((modified_node == node_index) as u64)),
        )?;

        region.assign_advice(
            || format!("assign is_leaf_s"),
            self.is_leaf_s,
            offset,
            || Ok(F::from_u64(is_leaf_s as u64)),
        )?;
        region.assign_advice(
            || format!("assign is_leaf_c"),
            self.is_leaf_c,
            offset,
            || Ok(F::from_u64(is_leaf_c as u64)),
        )?;

        region.assign_advice(
            || format!("assign is_leaf_s_value"),
            self.is_leaf_s_value,
            offset,
            || Ok(F::from_u64(is_leaf_s_value as u64)),
        )?;
        region.assign_advice(
            || format!("assign is_leaf_c_value"),
            self.is_leaf_c_value,
            offset,
            || Ok(F::from_u64(is_leaf_c_value as u64)),
        )?;

        region.assign_advice(
            || format!("assign is account leaf key s"),
            self.is_account_leaf_key_s,
            offset,
            || Ok(F::from_u64(is_account_leaf_key_s as u64)),
        )?;
        region.assign_advice(
            || format!("assign is account leaf nonce balance s"),
            self.is_account_leaf_nonce_balance_s,
            offset,
            || Ok(F::from_u64(is_account_leaf_nonce_balance_s as u64)),
        )?;
        region.assign_advice(
            || format!("assign is account leaf storage codehash s"),
            self.is_account_leaf_storage_codehash_s,
            offset,
            || Ok(F::from_u64(is_account_leaf_storage_codehash_s as u64)),
        )?;
        region.assign_advice(
            || format!("assign is account leaf storage codehash c"),
            self.is_account_leaf_storage_codehash_c,
            offset,
            || Ok(F::from_u64(is_account_leaf_storage_codehash_c as u64)),
        )?;

        region.assign_advice(
            || format!("assign s_rlp1"),
            self.s_rlp1,
            offset,
            || Ok(F::from_u64(row[0] as u64)),
        )?;

        region.assign_advice(
            || format!("assign s_rlp2"),
            self.s_rlp2,
            offset,
            || Ok(F::from_u64(row[1] as u64)),
        )?;

        for idx in 0..HASH_WIDTH {
            region.assign_advice(
                || format!("assign s_advice {}", idx),
                self.s_advices[idx],
                offset,
                || Ok(F::from_u64(row[LAYOUT_OFFSET + idx] as u64)),
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

            return val as u64;
        };

        region.assign_advice(
            || format!("assign c_rlp1"),
            self.c_rlp1,
            offset,
            || Ok(F::from_u64(get_val(WITNESS_ROW_WIDTH / 2))),
        )?;
        region.assign_advice(
            || format!("assign c_rlp2"),
            self.c_rlp2,
            offset,
            || Ok(F::from_u64(get_val(WITNESS_ROW_WIDTH / 2 + 1))),
        )?;

        for (idx, _c) in self.c_advices.iter().enumerate() {
            let val = get_val(WITNESS_ROW_WIDTH / 2 + LAYOUT_OFFSET + idx);
            region.assign_advice(
                || format!("assign c_advice {}", idx),
                self.c_advices[idx],
                offset,
                || Ok(F::from_u64(val)),
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
            false, false, false, false, offset,
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
        row: &Vec<u8>,
        s_words: &Vec<u64>,
        c_words: &Vec<u64>,
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
            offset,
        )?;

        for (ind, column) in self.s_keccak.iter().enumerate() {
            region.assign_advice(
                || "Keccak s",
                *column,
                offset,
                || Ok(F::from_u64(s_words[ind])),
            )?;
        }
        for (ind, column) in self.c_keccak.iter().enumerate() {
            region.assign_advice(
                || "Keccak c",
                *column,
                offset,
                || Ok(F::from_u64(c_words[ind])),
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
            || format!("assign acc_s"),
            self.acc_s,
            offset,
            || Ok(acc_s),
        )?;

        region.assign_advice(
            || format!("assign acc_mult_s"),
            self.acc_mult_s,
            offset,
            || Ok(acc_mult_s),
        )?;

        region.assign_advice(
            || format!("assign acc_c"),
            self.acc_c,
            offset,
            || Ok(acc_c),
        )?;

        region.assign_advice(
            || format!("assign acc_mult_c"),
            self.acc_mult_c,
            offset,
            || Ok(acc_mult_c),
        )?;

        Ok(())
    }

    pub(crate) fn assign(
        &self,
        mut layouter: impl Layouter<F>,
        witness: &Vec<Vec<u8>>,
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
                    let mut not_first_level = F::zero();
                    // filter out rows that are just to be hashed
                    for (ind, row) in witness
                        .iter()
                        .filter(|r| {
                            r[r.len() - 1] != 5
                                && r[r.len() - 1] != 4
                                && r[r.len() - 1] != 14
                                && r[r.len() - 1] != 9
                        })
                        .enumerate()
                    {
                        // TODO: what if extension node
                        if ind == 17 as usize && row[row.len() - 1] == 0 {
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

                            // Get the child that is being changed and convert it to words to enable lookups:
                            let s_hash = witness
                                [ind + 1 + modified_node as usize]
                                [S_START..S_START + HASH_WIDTH]
                                .to_vec();
                            let c_hash = witness
                                [ind + 1 + modified_node as usize]
                                [C_START..C_START + HASH_WIDTH]
                                .to_vec();
                            s_words = self.into_words(&s_hash);
                            c_words = self.into_words(&c_hash);

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

                            acc_s = F::from_u64(row[BRANCH_0_S_START] as u64)
                                + F::from_u64(row[BRANCH_0_S_START + 1] as u64)
                                    * self.acc_r;
                            acc_mult_s = self.acc_r * self.acc_r;

                            if row[BRANCH_0_S_START] == 249 {
                                acc_s += F::from_u64(
                                    row[BRANCH_0_S_START + 2] as u64,
                                ) * acc_mult_s;
                                acc_mult_s *= self.acc_r;
                            }

                            acc_c = F::from_u64(row[BRANCH_0_C_START] as u64)
                                + F::from_u64(row[BRANCH_0_C_START + 1] as u64)
                                    * self.acc_r;
                            acc_mult_c = self.acc_r * self.acc_r;

                            if row[BRANCH_0_C_START] == 249 {
                                acc_c += F::from_u64(
                                    row[BRANCH_0_C_START + 2] as u64,
                                ) * acc_mult_c;
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
                                let mut sel1 = F::zero();
                                let mut sel2 = F::zero();
                                if key_rlc_sel {
                                    key_rlc = key_rlc
                                        + F::from_u64(modified_node as u64)
                                            * F::from_u64(16)
                                            * key_rlc_mult;
                                    // key_rlc_mult stays the same
                                    sel1 = F::one();
                                } else {
                                    key_rlc = key_rlc
                                        + F::from_u64(modified_node as u64)
                                            * key_rlc_mult;
                                    key_rlc_mult = key_rlc_mult * self.acc_r;
                                    sel2 = F::one();
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
                                    offset,
                                )?;
                                region.assign_advice(
                                    || format!("assign sel1"),
                                    self.sel1,
                                    offset,
                                    || Ok(sel1),
                                )?;
                                region.assign_advice(
                                    || format!("assign sel2"),
                                    self.sel2,
                                    offset,
                                    || Ok(sel2),
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
                                    offset,
                                )?;
                            }

                            // reassign (it was assigned to 0 in assign_row) branch_acc and branch_mult to proper values

                            // We need to distinguish between empty and non-empty node:
                            // empty node at position 1: 0
                            // non-empty node at position 1: 160

                            let c128 = F::from_u64(128 as u64);
                            let c160 = F::from_u64(160 as u64);

                            let compute_acc_and_mult =
                                |branch_acc: &mut F,
                                 branch_mult: &mut F,
                                 rlp_start: usize,
                                 start: usize| {
                                    if row[rlp_start + 1] == 0 {
                                        *branch_acc += c128 * *branch_mult;
                                        *branch_mult =
                                            *branch_mult * self.acc_r;
                                    } else {
                                        *branch_acc += c160 * *branch_mult;
                                        *branch_mult =
                                            *branch_mult * self.acc_r;
                                        for i in 0..HASH_WIDTH {
                                            *branch_acc += F::from_u64(
                                                row[start + i] as u64,
                                            ) * *branch_mult;
                                            *branch_mult =
                                                *branch_mult * self.acc_r;
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
                                offset,
                            )?;

                            let mut assign_long_short = |long: bool| {
                                let mut is_short = false;
                                let mut is_long = false;
                                if long {
                                    is_long = true;
                                } else {
                                    is_short = true;
                                }
                                region
                                    .assign_advice(
                                        || format!("assign acc_s"),
                                        self.s_keccak[0],
                                        offset,
                                        || Ok(F::from_u64(is_long as u64)),
                                    )
                                    .ok();
                                region
                                    .assign_advice(
                                        || format!("assign acc_c"),
                                        self.s_keccak[1],
                                        offset,
                                        || Ok(F::from_u64(is_short as u64)),
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
                                        if start + i == 70 {
                                            println!("adsf");
                                        }
                                        *acc +=
                                            F::from_u64(row[start + i] as u64)
                                                * *mult;
                                        *mult = *mult * self.acc_r;
                                    }
                                };

                            let compute_key_rlc =
                                |key_rlc: &mut F,
                                 key_rlc_mult: &mut F,
                                 start: usize| {
                                    if !key_rlc_sel {
                                        // That means we had key_rlc_sel=true when setting rlc last time,
                                        // that means we have nibble+48 in s_advices[0].
                                        *key_rlc += F::from_u64(
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
                                assign_long_short(witness[ind][0] == 248);

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
                                let mut key_rlc_new = key_rlc.clone();
                                let mut key_rlc_mult_new = key_rlc_mult.clone();
                                compute_key_rlc(
                                    &mut key_rlc_new,
                                    &mut key_rlc_mult_new,
                                    start,
                                );
                                region.assign_advice(
                                    || format!("assign key_rlc"),
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
                                for i in 0..3 + key_len {
                                    acc_s +=
                                        F::from_u64(row[i] as u64) * acc_mult_s;
                                    acc_mult_s = acc_mult_s * self.acc_r;
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
                                let mut key_rlc_new = key_rlc.clone();
                                let mut key_rlc_mult_new = key_rlc_mult.clone();
                                compute_key_rlc(
                                    &mut key_rlc_new,
                                    &mut key_rlc_mult_new,
                                    S_START,
                                );
                                region.assign_advice(
                                    || format!("assign key_rlc"),
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
                                let acc_mult_tmp = acc_mult_s.clone();
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

                                acc_nonce_balance = acc_s.clone();
                                acc_mult_nonce_balance = acc_mult_s.clone();
                            } else if row[row.len() - 1] == 8
                                || row[row.len() - 1] == 11
                            {
                                if row[row.len() - 1] == 11 {
                                    // Leaf key and nonce/balance for S and C
                                    // are always the same, so we just use
                                    // accumulated value from S.
                                    acc_s = acc_nonce_balance.clone();
                                    acc_mult_s = acc_mult_nonce_balance.clone();
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

        Ok(())
    }

    // see bits_to_u64_words_le
    fn into_words(&self, message: &[u8]) -> Vec<u64> {
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
                        rlc = rlc + F::from_u64(*i as u64) * mult;
                        mult = mult * self.acc_r;
                    }
                    region.assign_fixed(
                        || "Keccak table",
                        self.keccak_table[0],
                        offset,
                        || Ok(rlc),
                    )?;

                    let keccak_output = self.into_words(&hash);

                    for (ind, column) in self.keccak_table.iter().enumerate() {
                        if ind == 0 {
                            continue;
                        }
                        let val = keccak_output[ind - KECCAK_INPUT_WIDTH];
                        region.assign_fixed(
                            || "Keccak table",
                            *column,
                            offset,
                            || Ok(F::from_u64(val)),
                        )?;
                    }
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

    use pasta_curves::{arithmetic::FieldExt, pallas, EqAffine};
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
                let circuit = MyCircuit::<pallas::Base> {
                    _marker: PhantomData,
                    witness: w,
                };

                let prover =
                    MockProver::<pallas::Base>::run(9, &circuit, vec![])
                        .unwrap();
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
