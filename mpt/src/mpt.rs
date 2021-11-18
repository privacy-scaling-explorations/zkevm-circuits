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

use crate::{
    branch_acc::BranchAccChip, key_compr::KeyComprChip, param::LAYOUT_OFFSET,
};
use crate::{branch_acc::BranchAccConfig, param::WITNESS_ROW_WIDTH};
use crate::{
    key_compr::KeyComprConfig,
    param::{
        BRANCH_0_C_START, BRANCH_0_KEY_POS, BRANCH_0_S_START, C_RLP_START,
        C_START, HASH_WIDTH, KECCAK_INPUT_WIDTH, KECCAK_OUTPUT_WIDTH,
        S_RLP_START, S_START,
    },
};

#[derive(Clone, Debug)]
pub struct MPTConfig<F> {
    q_enable: Selector,
    q_not_first: Column<Fixed>,
    is_branch_init: Column<Advice>,
    is_branch_child: Column<Advice>,
    is_last_branch_child: Column<Advice>,
    is_leaf_s: Column<Advice>,
    is_leaf_c: Column<Advice>,
    is_leaf_key: Column<Advice>,
    node_index: Column<Advice>,
    is_modified: Column<Advice>, // whether this branch child is modified
    key: Column<Advice>,
    s_rlp1: Column<Advice>,
    s_rlp2: Column<Advice>,
    c_rlp1: Column<Advice>,
    c_rlp2: Column<Advice>,
    s_advices: [Column<Advice>; HASH_WIDTH],
    c_advices: [Column<Advice>; HASH_WIDTH],
    s_keccak: [Column<Advice>; KECCAK_OUTPUT_WIDTH],
    c_keccak: [Column<Advice>; KECCAK_OUTPUT_WIDTH],
    branch_acc_s: Column<Advice>,
    branch_mult_s: Column<Advice>,
    branch_acc_c: Column<Advice>,
    branch_mult_c: Column<Advice>,
    branch_acc_r: F,
    branch_acc_s_chip: BranchAccConfig,
    branch_acc_c_chip: BranchAccConfig,
    key_compr_chip: KeyComprConfig,
    keccak_table: [Column<Advice>; KECCAK_INPUT_WIDTH + KECCAK_OUTPUT_WIDTH],
    _marker: PhantomData<F>,
}

impl<F: FieldExt> MPTConfig<F> {
    pub(crate) fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let q_enable = meta.selector();
        let q_not_first = meta.fixed_column();

        let branch_acc_r = F::rand(); // TODO: generate from commitments

        let is_branch_init = meta.advice_column();
        let is_branch_child = meta.advice_column();
        let is_last_branch_child = meta.advice_column();
        let is_leaf_s = meta.advice_column();
        let is_leaf_c = meta.advice_column();
        let is_leaf_key = meta.advice_column();
        let node_index = meta.advice_column();
        let is_modified = meta.advice_column();
        let key = meta.advice_column();

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

        let keccak_table: [Column<Advice>;
            KECCAK_INPUT_WIDTH + KECCAK_OUTPUT_WIDTH] = (0..KECCAK_INPUT_WIDTH
            + KECCAK_OUTPUT_WIDTH)
            .map(|_| meta.advice_column())
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

        let branch_acc_s = meta.advice_column();
        let branch_mult_s = meta.advice_column();
        let branch_acc_c = meta.advice_column();
        let branch_mult_c = meta.advice_column();

        let one = Expression::Constant(F::one());

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
            let is_leaf_c = meta.query_advice(is_leaf_c, Rotation::cur());
            let is_leaf_key_s = meta.query_advice(is_leaf_key, Rotation::cur());

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
            let bool_check_is_leaf_key =
                is_leaf_key_s.clone() * (one.clone() - is_leaf_key_s.clone());

            // TODO: is_last_branch_child followed by is_leaf_s followed by is_leaf_c
            // followed by is_leaf_key

            let node_index_cur = meta.query_advice(node_index, Rotation::cur());
            let key = meta.query_advice(key, Rotation::cur());
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
                "bool check is leaf key",
                q_enable.clone() * bool_check_is_leaf_key,
            ));

            constraints.push((
                "rlp 1",
                q_enable.clone()
                    * is_branch_child_cur.clone()
                    * (s_rlp1 - c_rlp1)
                    * (node_index_cur.clone() - key.clone()),
            ));
            constraints.push((
                "rlp 2",
                q_enable.clone()
                    * is_branch_child_cur.clone()
                    * (s_rlp2 - c_rlp2)
                    * (node_index_cur.clone() - key.clone()),
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
                    * (node_index_cur.clone() - key.clone()),
            ));

            for (ind, col) in s_advices.iter().enumerate() {
                let s = meta.query_advice(*col, Rotation::cur());
                let c = meta.query_advice(c_advices[ind], Rotation::cur());
                constraints.push((
                    "s = c",
                    q_enable.clone()
                        * is_branch_child_cur.clone()
                        * (s - c)
                        * (node_index_cur.clone() - key.clone()),
                ));
            }

            constraints
        });

        meta.create_gate("branch children", |meta| {
            let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());

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

            // key needs to be the same for all branch nodes
            let key_prev = meta.query_advice(key, Rotation::prev());
            let key_cur = meta.query_advice(key, Rotation::cur());
            constraints.push((
                "key the same for branch children",
                q_not_first.clone()
                    * is_branch_child_cur.clone()
                    * node_index_cur.clone() // ignore if node_index = 0
                    * (key_cur - key_prev),
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
            let branch_acc_s_cur =
                meta.query_advice(branch_acc_s, Rotation::cur());
            let branch_acc_c_cur =
                meta.query_advice(branch_acc_c, Rotation::cur());
            let branch_mult_s_cur =
                meta.query_advice(branch_mult_s, Rotation::cur());
            let branch_mult_c_cur =
                meta.query_advice(branch_mult_c, Rotation::cur());

            let two_rlp_bytes = meta.query_advice(s_rlp1, Rotation::cur());
            let three_rlp_bytes = meta.query_advice(s_rlp2, Rotation::cur());

            // TODO: two_rlp_bytes and three_rlp_bytes are bools
            // TODO: two_rlp_bytes + three_rlp_bytes = 1

            // TODO: remove mult_s and mult_c by having big endian

            let s_rlp1 = meta.query_advice(s_advices[0], Rotation::cur());
            let s_rlp2 = meta.query_advice(s_advices[1], Rotation::cur());
            let s_rlp3 = meta.query_advice(s_advices[2], Rotation::cur());

            let c_rlp1 = meta.query_advice(s_advices[3], Rotation::cur());
            let c_rlp2 = meta.query_advice(s_advices[4], Rotation::cur());
            let c_rlp3 = meta.query_advice(s_advices[5], Rotation::cur());

            let acc_s_two = s_rlp1.clone() + s_rlp2.clone() * branch_acc_r;
            constraints.push((
                "branch accumulator S row 0",
                q_enable.clone()
                    * is_branch_init_cur.clone()
                    * two_rlp_bytes.clone()
                    * (acc_s_two - branch_acc_s_cur.clone()),
            ));

            let mult_s_two = Expression::Constant(branch_acc_r * branch_acc_r);
            constraints.push((
                "branch mult S row 0",
                q_enable.clone()
                    * is_branch_init_cur.clone()
                    * two_rlp_bytes.clone()
                    * (mult_s_two - branch_mult_s_cur.clone()),
            ));

            let acc_c_two = c_rlp1.clone() + c_rlp2.clone() * branch_acc_r;
            constraints.push((
                "branch accumulator C row 0",
                q_enable.clone()
                    * is_branch_init_cur.clone()
                    * two_rlp_bytes.clone()
                    * (acc_c_two - branch_acc_c_cur.clone()),
            ));

            let mult_c_two = Expression::Constant(branch_acc_r * branch_acc_r);
            constraints.push((
                "branch mult C row 0",
                q_enable.clone()
                    * is_branch_init_cur.clone()
                    * two_rlp_bytes
                    * (mult_c_two - branch_mult_c_cur.clone()),
            ));

            //

            let acc_s_three = s_rlp1
                + s_rlp2 * branch_acc_r
                + s_rlp3 * branch_acc_r * branch_acc_r;
            constraints.push((
                "branch accumulator S row 0 (3)",
                q_enable.clone()
                    * is_branch_init_cur.clone()
                    * three_rlp_bytes.clone()
                    * (acc_s_three - branch_acc_s_cur),
            ));

            let mult_s_three = Expression::Constant(
                branch_acc_r * branch_acc_r * branch_acc_r,
            );
            constraints.push((
                "branch mult S row 0 (3)",
                q_enable.clone()
                    * is_branch_init_cur.clone()
                    * three_rlp_bytes.clone()
                    * (mult_s_three - branch_mult_s_cur),
            ));

            let acc_c_three = c_rlp1
                + c_rlp2 * branch_acc_r
                + c_rlp3 * branch_acc_r * branch_acc_r;
            constraints.push((
                "branch accumulator C row 0 (3)",
                q_enable.clone()
                    * is_branch_init_cur.clone()
                    * three_rlp_bytes.clone()
                    * (acc_c_three - branch_acc_c_cur),
            ));

            let mult_c_three = Expression::Constant(
                branch_acc_r * branch_acc_r * branch_acc_r,
            );
            constraints.push((
                "branch mult C row 0 (3)",
                q_enable.clone()
                    * is_branch_init_cur.clone()
                    * three_rlp_bytes
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

        // TODO: check transition from compact to keccak leaf (compact leaf as keccak input - 17 cells)

        /*
        // Lookup into RLP circuit for S branch: (accumulated_rlp, hash1, hash2, hash3, hash4)
        meta.lookup(|meta| {
            let q_enable = meta.query_selector(q_enable);

            // We need to do the lookup only if we are in the last branch child.
            let is_last_branch_child =
                meta.query_advice(is_last_branch_child, Rotation::cur());

            // Rotation(-17) can be avoided by inverting the accumulator - having the final
            // value in the branch init (thus only Rotation(-1) would be needed).
            let branch_acc_s = meta.query_advice(branch_acc_s, Rotation::cur());

            let mut constraints = vec![];
            constraints.push((
                q_enable.clone() * is_last_branch_child.clone(),
                branch_acc_s,
            ));

            for column in s_keccak.iter() {
                let s_keccak = meta.query_advice(*column, Rotation(-17));
                constraints.push((
                    q_enable.clone() * is_last_branch_child.clone(),
                    s_keccak,
                ));
            }

            constraints
        });

        // Lookup into RLP circuit for C branch: (accumulated_rlp, hash1, hash2, hash3, hash4)
        meta.lookup(|meta| {
            let q_enable = meta.query_selector(q_enable);

            // We need to do the lookup only if we are in the last branch child.
            let is_last_branch_child =
                meta.query_advice(is_last_branch_child, Rotation::cur());

            // Rotation(-17) can be avoided by inverting the accumulator - having the final
            // value in the branch init (thus only Rotation(-1) would be needed).
            let branch_acc_c = meta.query_advice(branch_acc_c, Rotation::cur());

            let mut constraints = vec![];
            constraints.push((
                q_enable.clone() * is_last_branch_child.clone(),
                branch_acc_c,
            ));

            for column in c_keccak.iter() {
                let c_keccak = meta.query_advice(*column, Rotation(-17));
                constraints.push((
                    q_enable.clone() * is_last_branch_child.clone(),
                    c_keccak,
                ));
            }

            constraints
        });
        */

        let branch_acc_s_chip = BranchAccChip::<F>::configure(
            meta,
            |meta| {
                let q_not_first =
                    meta.query_fixed(q_not_first, Rotation::cur());
                let is_branch_child =
                    meta.query_advice(is_branch_child, Rotation::cur());

                q_not_first * is_branch_child
            },
            branch_acc_r,
            s_rlp2,
            s_advices,
            branch_acc_s,
            branch_mult_s,
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
            branch_acc_r,
            c_rlp2,
            c_advices,
            branch_acc_c,
            branch_mult_c,
        );

        /*
        // hash of leaf s is in the parent branch
        meta.lookup(|meta| {
            let q_enable = meta.query_selector(q_enable);
            let is_leaf_s =
                meta.query_advice(is_leaf_s, Rotation::cur());

            // lookup using (RLC for leaf_s, s_keccak::prev(-2)[0], ..., s_keccak::prev(-2)[3])

            let mut constraints = vec![];
            constraints.push((
                    q_enable.clone() * is_leaf_s.clone() * rlc,
                    keccak_table_i,
                ))
            for i in 0..KECCAK_OUTPUT_WIDTH {
                let k = meta.query_advice(s_keccak[i], Rotation(-2));
                let keccak_table_i =
                    meta.query_advice(keccak_table[i], Rotation::cur());
                constraints.push((
                    q_enable.clone() * is_leaf_s.clone() * k,
                    keccak_table_i,
                ))
            }

            constraints
        });
        */

        /*
        // hash of leaf c is in the parent branch
        meta.lookup(|meta| {
            let q_enable = meta.query_selector(q_enable);
            let is_leaf_c =
                meta.query_advice(is_leaf_c, Rotation::cur());

            // lookup using (RLC for leaf_c, c_keccak::prev(-4)[0], ..., c_keccak::prev(-4)[3])

            let mut constraints = vec![];
            constraints.push((
                    q_enable.clone() * is_leaf_c.clone() * rlc,
                    keccak_table_i,
                ))
            for i in 0..KECCAK_OUTPUT_WIDTH {
                let k = meta.query_advice(c_keccak[i], Rotation(-4));
                let keccak_table_i =
                    meta.query_advice(keccak_table[i], Rotation::cur());
                constraints.push((
                    q_enable.clone() * is_leaf_c.clone() * k,
                    keccak_table_i,
                ))
            }

            constraints
        });
        */

        let key_compr_chip = KeyComprChip::<F>::configure(
            meta,
            |meta| {
                let q_not_first =
                    meta.query_fixed(q_not_first, Rotation::cur());
                let is_leaf_key =
                    meta.query_advice(is_leaf_key, Rotation::cur());

                q_not_first * is_leaf_key
            },
            s_rlp1,
            s_rlp2,
            c_rlp1,
            c_rlp2,
            s_advices,
            c_advices,
        );

        MPTConfig {
            q_enable,
            q_not_first,
            is_branch_init,
            is_branch_child,
            is_last_branch_child,
            is_leaf_s,
            is_leaf_c,
            is_leaf_key,
            node_index,
            is_modified,
            key,
            s_rlp1,
            s_rlp2,
            c_rlp1,
            c_rlp2,
            s_advices,
            c_advices,
            s_keccak,
            c_keccak,
            branch_acc_s,
            branch_mult_s,
            branch_acc_c,
            branch_mult_c,
            branch_acc_r,
            branch_acc_s_chip,
            branch_acc_c_chip,
            key_compr_chip,
            keccak_table,
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
        key: u8,
        is_leaf_s: bool,
        is_leaf_c: bool,
        is_leaf_key: bool,
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
            || format!("assign branch_acc_s"),
            self.branch_acc_s,
            offset,
            || Ok(F::zero()),
        )?;

        region.assign_advice(
            || format!("assign branch_mult_s"),
            self.branch_mult_s,
            offset,
            || Ok(F::zero()),
        )?;

        region.assign_advice(
            || format!("assign branch_acc_c"),
            self.branch_acc_c,
            offset,
            || Ok(F::zero()),
        )?;

        region.assign_advice(
            || format!("assign branch_mult_c"),
            self.branch_mult_c,
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
            || format!("assign key"),
            self.key,
            offset,
            || Ok(F::from_u64(key as u64)),
        )?;

        region.assign_advice(
            || format!("assign is_modified"),
            self.is_modified,
            offset,
            || Ok(F::from_u64((key == node_index) as u64)),
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
            || format!("assign is_leaf_key_s"),
            self.is_leaf_key,
            offset,
            || Ok(F::from_u64(is_leaf_key as u64)),
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
            || Ok(F::from_u64(row[WITNESS_ROW_WIDTH / 2] as u64)),
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

    fn assign_leaf(
        &self,
        region: &mut Region<'_, F>,
        is_leaf_s: bool,
        is_leaf_c: bool,
        is_leaf_key: bool,
        row: &Vec<u8>,
        offset: usize,
    ) -> Result<(), Error> {
        self.assign_row(
            region,
            row,
            false,
            false,
            false,
            0,
            0,
            is_leaf_s,
            is_leaf_c,
            is_leaf_key,
            offset,
        )?;

        Ok(())
    }

    fn assign_branch_init(
        &self,
        region: &mut Region<'_, F>,
        row: &Vec<u8>,
        offset: usize,
    ) -> Result<(), Error> {
        self.assign_row(
            region, row, true, false, false, 0, 0, false, false, false, offset,
        )?;

        Ok(())
    }

    fn assign_branch_row(
        &self,
        region: &mut Region<'_, F>,
        node_index: u8,
        key: u8,
        row: &Vec<u8>,
        s_words: &Vec<u64>,
        c_words: &Vec<u64>,
        offset: usize,
    ) -> Result<(), Error> {
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
            offset,
        )?;

        Ok(())
    }

    fn assign_branch_acc(
        &self,
        region: &mut Region<'_, F>,
        acc_s: F,
        branch_mult_s: F,
        acc_c: F,
        branch_mult_c: F,
        offset: usize,
    ) -> Result<(), Error> {
        region.assign_advice(
            || format!("assign branch_acc_s"),
            self.branch_acc_s,
            offset,
            || Ok(acc_s),
        )?;

        region.assign_advice(
            || format!("assign branch_mult_s"),
            self.branch_mult_s,
            offset,
            || Ok(branch_mult_s),
        )?;

        region.assign_advice(
            || format!("assign branch_acc_c"),
            self.branch_acc_c,
            offset,
            || Ok(acc_c),
        )?;

        region.assign_advice(
            || format!("assign branch_mult_c"),
            self.branch_mult_c,
            offset,
            || Ok(branch_mult_c),
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

                    let mut key = 0;
                    let mut s_words: Vec<u64> = vec![0, 0, 0, 0];
                    let mut c_words: Vec<u64> = vec![0, 0, 0, 0];
                    let mut branch_ind: u8 = 0;
                    let mut branch_acc_s = F::zero();
                    let mut branch_mult_s = F::zero();
                    let mut branch_acc_c = F::zero();
                    let mut branch_mult_c = F::zero();
                    for (ind, row) in witness.iter().enumerate() {
                        if row[row.len() - 1] == 0 {
                            // branch init
                            key = row[BRANCH_0_KEY_POS];
                            branch_ind = 0;

                            // Get the child that is being changed and convert it to words to enable lookups:
                            let s_hash = witness[ind + 1 + key as usize]
                                [S_START..S_START + HASH_WIDTH]
                                .to_vec();
                            let c_hash = witness[ind + 1 + key as usize]
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

                            branch_acc_s =
                                F::from_u64(row[BRANCH_0_S_START] as u64)
                                    + F::from_u64(
                                        row[BRANCH_0_S_START + 1] as u64,
                                    ) * self.branch_acc_r;
                            branch_mult_s =
                                self.branch_acc_r * self.branch_acc_r;

                            if row[BRANCH_0_S_START] == 249 {
                                branch_acc_s += F::from_u64(
                                    row[BRANCH_0_S_START + 2] as u64,
                                ) * branch_mult_s;
                                branch_mult_s *= self.branch_acc_r;
                            }

                            branch_acc_c =
                                F::from_u64(row[BRANCH_0_C_START] as u64)
                                    + F::from_u64(
                                        row[BRANCH_0_C_START + 1] as u64,
                                    ) * self.branch_acc_r;
                            branch_mult_c =
                                self.branch_acc_r * self.branch_acc_r;

                            if row[BRANCH_0_C_START] == 249 {
                                branch_acc_c += F::from_u64(
                                    row[BRANCH_0_C_START + 2] as u64,
                                ) * branch_mult_c;
                                branch_mult_c *= self.branch_acc_r;
                            }

                            self.assign_branch_acc(
                                &mut region,
                                branch_acc_s,
                                branch_mult_s,
                                branch_acc_c,
                                branch_mult_c,
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
                            self.assign_branch_row(
                                &mut region,
                                branch_ind,
                                key,
                                &row[0..row.len() - 1].to_vec(),
                                &s_words,
                                &c_words,
                                offset,
                            )?;

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
                                            *branch_mult * self.branch_acc_r;
                                    } else {
                                        *branch_acc += c160 * *branch_mult;
                                        *branch_mult =
                                            *branch_mult * self.branch_acc_r;
                                        for i in 0..HASH_WIDTH {
                                            *branch_acc += F::from_u64(
                                                row[start + i] as u64,
                                            ) * *branch_mult;
                                            *branch_mult = *branch_mult
                                                * self.branch_acc_r;
                                        }
                                    }
                                };

                            compute_acc_and_mult(
                                &mut branch_acc_s,
                                &mut branch_mult_s,
                                S_RLP_START,
                                S_START,
                            );
                            compute_acc_and_mult(
                                &mut branch_acc_c,
                                &mut branch_mult_c,
                                C_RLP_START,
                                C_START,
                            );
                            self.assign_branch_acc(
                                &mut region,
                                branch_acc_s,
                                branch_mult_s,
                                branch_acc_c,
                                branch_mult_c,
                                offset,
                            )?;

                            offset += 1;
                            branch_ind += 1;
                        } else if row[row.len() - 1] == 2
                            || row[row.len() - 1] == 3
                            || row[row.len() - 1] == 4
                            || row[row.len() - 1] == 5
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
                            let mut is_leaf_c = false;
                            let mut is_leaf_key = false;
                            if row[row.len() - 1] == 2 {
                                is_leaf_s = true;
                            } else if row[row.len() - 1] == 3 {
                                is_leaf_c = true;
                            } else if row[row.len() - 1] == 4 {
                                is_leaf_key = true;
                            }
                            self.assign_leaf(
                                &mut region,
                                is_leaf_s,
                                is_leaf_c,
                                is_leaf_key,
                                &row[0..row.len() - 1].to_vec(),
                                offset,
                            )?;
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
        self.load_keccak_table(_layouter, to_be_hashed);

        Ok(())
    }

    fn pad(&self, input: &[u8]) -> Vec<u8> {
        let rate = 136;
        let padding_total = rate - (input.len() % rate);
        let mut padding: Vec<u8>;

        if padding_total == 1 {
            padding = vec![0x81];
        } else {
            padding = vec![0x01];
            padding.resize(padding_total - 1, 0x00);
            padding.push(0x80);
        }

        let message = [input, &padding].concat();
        message
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
                    let padded = self.pad(t);
                    let keccak_input = self.into_words(&padded);
                    let keccak_output = self.into_words(&hash);

                    for (ind, column) in self.keccak_table.iter().enumerate() {
                        let val: u64;
                        if ind < KECCAK_INPUT_WIDTH {
                            val = keccak_input[ind];
                        } else {
                            val = keccak_output[ind - KECCAK_INPUT_WIDTH];
                        }
                        region.assign_advice(
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
            create_proof, keygen_pk, keygen_vk, Advice, Circuit, Column,
            ConstraintSystem, Error,
        },
        poly::commitment::Params,
        transcript::{Blake2bWrite, Challenge255},
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
                    if row[row.len() - 1] == 2 || row[row.len() - 1] == 3 {
                        // compact leaf or branch RLP
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
                const K: u32 = 6;
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

                println!("{:?}", proof);
                */
            });
    }
}
