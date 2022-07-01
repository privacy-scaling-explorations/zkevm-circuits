use halo2_proofs::{
    circuit::Chip,
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, VirtualCells},
    poly::Rotation,
};
use pairing::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::{
    helpers::{compute_rlc, key_len_lookup, mult_diff_lookup, range_lookups},
    mpt::FixedTableTag,
    param::{
        HASH_WIDTH, IS_BRANCH_C16_POS, IS_BRANCH_C1_POS, LAYOUT_OFFSET, ACCOUNT_NON_EXISTING_IND, BRANCH_ROWS_NUM,
    },
};

#[derive(Clone, Debug)]
pub(crate) struct AccountNonExistingConfig {}

/*
Checks that the address does not exist. There are two versions of proof:
    1. A leaf is returned by getProof that is not at the required address (we call this a wrong leaf).
    2. A branch is the last element of getProof and there is nil object at address position.
       Placeholder account leaf is added in this case.

1. In case of a wrong leaf, non_existing_account_row contains the nibbles of the address that was enquired
while account_leaf_key contains the nibbles of the wrong leaf. We need to prove that the difference is nonzero.
2. In case of nil object, we need to prove that the branch contains nil object (128) at the enquired address.
*/
pub(crate) struct AccountNonExistingChip<F> {
    config: AccountNonExistingConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> AccountNonExistingChip<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: impl Fn(&mut VirtualCells<'_, F>) -> Expression<F> + Copy,
        not_first_level: Column<Advice>,
        s_rlp1: Column<Advice>,
        s_rlp2: Column<Advice>,
        c_rlp1: Column<Advice>,
        c_rlp2: Column<Advice>,
        s_advices: [Column<Advice>; HASH_WIDTH],
        key_rlc: Column<Advice>,
        key_rlc_mult: Column<Advice>,
        acc_s: Column<Advice>,
        sel1: Column<Advice>, // should be the same as sel2 as both parallel proofs are the same for non_existing_account_proof
        r_table: Vec<Expression<F>>,
        fixed_table: [Column<Fixed>; 3],
        address_rlc: Column<Advice>,
    ) -> AccountNonExistingConfig {
        let config = AccountNonExistingConfig {};
        let one = Expression::Constant(F::one());
        let c32 = Expression::Constant(F::from(32));
        // key rlc is in the first branch node
        let rot_into_first_branch_child = -(ACCOUNT_NON_EXISTING_IND - 1 + BRANCH_ROWS_NUM);

        // TODO: zeros after key_len in non_existing_account row

        let add_wrong_leaf_constraints =
            |meta: &mut VirtualCells<F>,
            constraints: &mut Vec<(&str, Expression<F>)>,
            q_enable: Expression<F>,
            c_rlp1_cur: Expression<F>,
            c_rlp2_cur: Expression<F>,
            correct_level: Expression<F>,
            is_wrong_leaf: Expression<F> | {
                let sum = meta.query_advice(key_rlc, Rotation::cur());
                let sum_prev = meta.query_advice(key_rlc_mult, Rotation::cur());
                let diff_inv = meta.query_advice(acc_s, Rotation::cur());

                let c_rlp1_prev = meta.query_advice(c_rlp1, Rotation::prev());
                let c_rlp2_prev = meta.query_advice(c_rlp2, Rotation::prev());

                let mut sum_check = Expression::Constant(F::zero());
                let mut sum_prev_check = Expression::Constant(F::zero());
                let mut mult = r_table[0].clone();
                for ind in 1..HASH_WIDTH {
                    sum_check = sum_check + meta.query_advice(s_advices[ind], Rotation::cur()) * mult.clone();
                    sum_prev_check = sum_prev_check + meta.query_advice(s_advices[ind], Rotation::prev()) * mult.clone();
                    mult = mult * r_table[0].clone();
                }
                sum_check = sum_check + c_rlp1_cur * mult.clone();
                sum_prev_check = sum_prev_check + c_rlp1_prev * mult.clone();
                mult = mult * r_table[0].clone();
                sum_check = sum_check + c_rlp2_cur * mult.clone();
                sum_prev_check = sum_prev_check + c_rlp2_prev * mult.clone();

                constraints.push((
                    "wrong leaf sum check",
                    q_enable.clone()
                        * correct_level.clone()
                        * is_wrong_leaf.clone()
                        * (sum.clone() - sum_check.clone()),
                ));

                constraints.push((
                    "wrong leaf sum_prev check",
                    q_enable.clone()
                        * correct_level.clone()
                        * is_wrong_leaf.clone()
                        * (sum_prev.clone() - sum_prev_check.clone()),
                ));

                constraints.push((
                    "Address of a leaf is different than address being inquired (corresponding to address_rlc)",
                    q_enable.clone()
                        * correct_level.clone()
                        * is_wrong_leaf.clone()
                        * (one.clone() - (sum - sum_prev) * diff_inv),
                ));

            };

        // Checks that account_non_existing_row contains the nibbles that give address_rlc (after considering
        // modified_node in branches/extension nodes above).
        // Note: currently, for non_existing_account proof S and C proofs are the same, thus there is never
        // a placeholder branch.
        meta.create_gate(
            "Non existing account proof leaf address RLC (leaf not in first level, branch not placeholder)",
            |meta| {
                let q_enable = q_enable(meta);
                let mut constraints = vec![];

                let is_leaf_in_first_level =
                    one.clone() - meta.query_advice(not_first_level, Rotation::cur());

                // Wrong leaf has a meaning only for non existing account proof. For this proof, there are two cases:
                // 1. A leaf is returned that is not at the required address (wrong leaf).
                // 2. A branch is returned as the last element of getProof and there is nil object at address position. Placeholder account leaf is added in this case.
                let is_wrong_leaf = meta.query_advice(s_rlp1, Rotation::cur());
                // is_wrong_leaf is checked to be bool in account_leaf_nonce_balance (q_enable in this chip
                // is true only when non_existing_account).

                let key_rlc_acc_start =
                    meta.query_advice(key_rlc, Rotation(rot_into_first_branch_child));
                let key_mult_start =
                    meta.query_advice(key_rlc_mult, Rotation(rot_into_first_branch_child));

                // sel1, sel2 is in init branch
                let c16 = meta.query_advice(
                    s_advices[IS_BRANCH_C16_POS - LAYOUT_OFFSET],
                    Rotation(rot_into_first_branch_child - 1),
                );
                let c1 = meta.query_advice(
                    s_advices[IS_BRANCH_C1_POS - LAYOUT_OFFSET],
                    Rotation(rot_into_first_branch_child - 1),
                );

                let c48 = Expression::Constant(F::from(48));

                // If c16 = 1, we have nibble+48 in s_advices[0].
                let s_advice1 = meta.query_advice(s_advices[1], Rotation::cur());
                let mut key_rlc_acc = key_rlc_acc_start.clone()
                    + (s_advice1.clone() - c48) * key_mult_start.clone() * c16.clone();
                let mut key_mult = key_mult_start.clone() * r_table[0].clone() * c16;
                key_mult = key_mult + key_mult_start.clone() * c1.clone(); // set to key_mult_start if sel2, stays key_mult if sel1

                // If c1 = 1, we have 32 in s_advices[0].
                constraints.push((
                    "Account leaf key acc s_advice1",
                    q_enable.clone()
                        * (one.clone() - is_leaf_in_first_level.clone())
                        * is_wrong_leaf.clone()
                        * (s_advice1 - c32.clone())
                        * c1,
                ));

                let s_advices2 = meta.query_advice(s_advices[2], Rotation::cur());
                key_rlc_acc = key_rlc_acc + s_advices2 * key_mult.clone();

                for ind in 3..HASH_WIDTH {
                    let s = meta.query_advice(s_advices[ind], Rotation::cur());
                    key_rlc_acc = key_rlc_acc + s * key_mult.clone() * r_table[ind - 3].clone();
                }

                let c_rlp1_cur = meta.query_advice(c_rlp1, Rotation::cur());
                let c_rlp2_cur = meta.query_advice(c_rlp2, Rotation::cur());
                key_rlc_acc = key_rlc_acc + c_rlp1_cur.clone() * key_mult.clone() * r_table[29].clone();
                key_rlc_acc = key_rlc_acc + c_rlp2_cur.clone() * key_mult * r_table[30].clone();

                let address_rlc = meta.query_advice(address_rlc, Rotation::cur());

                // Note: key_rlc_acc is computed as in account_leaf_key, but using non_existing_account row.
                constraints.push((
                    "Account address RLC",
                    q_enable.clone()
                        * (one.clone() - is_leaf_in_first_level.clone())
                        * is_wrong_leaf.clone()
                        * (key_rlc_acc.clone() - address_rlc.clone()),
                ));

                add_wrong_leaf_constraints(meta, &mut constraints, q_enable.clone(), c_rlp1_cur,
                    c_rlp2_cur, one.clone() - is_leaf_in_first_level.clone(), is_wrong_leaf.clone());
 
                let is_nil_object = meta.query_advice(sel1, Rotation(rot_into_first_branch_child));
                constraints.push((
                    "Nil object in parent branch",
                    q_enable.clone()
                        * (one.clone() - is_leaf_in_first_level.clone())
                        * (one.clone() - is_wrong_leaf)
                        * (one.clone() - is_nil_object),
                ));

                constraints
            },
        );

        // Proving that some account doesn't exist when there is only one account in the state trie.
        // Note 1: the hash of the only account is checked to be state root in account_leaf_storage_codehash.
        // Note 2: there is no nil_object case checked in this gate, because it is covered in the gate
        // above. That's because when there is a branch (with nil object) in the first level,
        // the account placeholder will be added below it and thus the account level won't be
        // in the first level.
        meta.create_gate("Non existing account proof leaf address RLC (leaf in first level)", |meta| {
            let q_enable = q_enable(meta);
            let mut constraints = vec![];

            let is_leaf_in_first_level =
                one.clone() - meta.query_advice(not_first_level, Rotation::cur());
            
            let is_wrong_leaf = meta.query_advice(s_rlp1, Rotation::cur());

            // Note: when leaf is in the first level, the key stored in the leaf is always of length 33 -
            // the first byte being 32 (when after branch, the information whether there the key is odd or even
            // is in s_advices[IS_BRANCH_C16_POS - LAYOUT_OFFSET] (see sel1/sel2).

            let s_advice1 = meta.query_advice(s_advices[1], Rotation::cur());
            let mut key_rlc_acc = Expression::Constant(F::zero());

            constraints.push((
                "Account leaf key acc s_advice1",
                q_enable.clone()
                * (s_advice1 - c32)
                * is_wrong_leaf.clone()
                * is_leaf_in_first_level.clone(),
            ));

            let s_advices2 = meta.query_advice(s_advices[2], Rotation::cur());
            key_rlc_acc = key_rlc_acc + s_advices2;

            for ind in 3..HASH_WIDTH {
                let s = meta.query_advice(s_advices[ind], Rotation::cur());
                key_rlc_acc = key_rlc_acc + s * r_table[ind - 3].clone();
            }

            let c_rlp1_cur = meta.query_advice(c_rlp1, Rotation::cur());
            let c_rlp2_cur = meta.query_advice(c_rlp2, Rotation::cur());
            key_rlc_acc = key_rlc_acc + c_rlp1_cur.clone() * r_table[29].clone();
            key_rlc_acc = key_rlc_acc + c_rlp2_cur.clone() * r_table[30].clone();

            let address_rlc = meta.query_advice(address_rlc, Rotation::cur());

            constraints.push((
                "Computed account address RLC same as value in address_rlc column",
                q_enable.clone()
                * is_leaf_in_first_level.clone()
                * is_wrong_leaf.clone()
                * (key_rlc_acc.clone() - address_rlc.clone()),
            ));

            add_wrong_leaf_constraints(meta, &mut constraints, q_enable.clone(), c_rlp1_cur,
                c_rlp2_cur, is_leaf_in_first_level.clone(), is_wrong_leaf.clone());

            constraints
        });

        range_lookups(
            meta,
            q_enable,
            s_advices.to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );
        range_lookups(
            meta,
            q_enable,
            [s_rlp2, c_rlp1, c_rlp2].to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );

        config
    }

    pub fn construct(config: AccountNonExistingConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }
}

impl<F: FieldExt> Chip<F> for AccountNonExistingChip<F> {
    type Config = AccountNonExistingConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}
