use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, VirtualCells},
    poly::Rotation,
};
use std::marker::PhantomData;

use crate::{
    mpt_circuit::columns::{AccumulatorCols, MainCols},
    mpt_circuit::helpers::range_lookups,
    mpt_circuit::param::{
        BRANCH_ROWS_NUM, HASH_WIDTH, IS_BRANCH_C16_POS, IS_BRANCH_C1_POS, RLP_NUM,
    },
    mpt_circuit::witness_row::MptWitnessRow,
    mpt_circuit::{
        helpers::key_len_lookup,
        param::{IS_NON_EXISTING_STORAGE_POS, LEAF_KEY_C_IND, LEAF_NON_EXISTING_IND, S_START},
        FixedTableTag, MPTConfig, ProofValues,
    },
};

/*
A storage leaf occupies 6 rows.
Contrary as in the branch rows, the `S` and `C` leaves are not positioned parallel to each other.
The rows are the following:
LEAF_KEY_S
LEAF_VALUE_S
LEAF_KEY_C
LEAF_VALUE_C
LEAF_DRIFTED
LEAF_NON_EXISTING

An example of leaf rows:
[226 160 49 236 194 26 116 94 57 104 160 78 149 112 228 66 91 193 143 168 1 156 104 2 129 150 181 70 209 102 156 32 12 104 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 2]
[1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 13]
[226 160 49 236 194 26 116 94 57 104 160 78 149 112 228 66 91 193 143 168 1 156 104 2 129 150 181 70 209 102 156 32 12 104 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 3]
[1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 14]
[0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 15]
[1 160 58 99 87 1 44 26 58 224 161 125 48 76 153 32 49 3 130 217 104 235 204 75 23 113 244 28 107 48 66 5 181 112 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 19]

In the above example, there is a wrong leaf case (see `s_rlp1` being 1 in the last row).
The constrainst here are analogue to the ones in `account_non_existing.rs`, but here it is for the
non existing storage instead of non existing account. However, more cases need to be handled for storage
because there can appear 1 or 2 RLP bytes (for account there are always 2). Also, the selectors need
to be obtained differently - for example, when we are checking the leaf in the first (storage) level,
we are checking whether we are behind the account leaf (for account proof we are checking whether we
are in the first level).

Lookups:
The `non_existing_storage_proof` lookup is enabled in `LEAF_NON_EXISTING` row.
*/

#[derive(Clone, Debug)]
pub(crate) struct StorageNonExistingConfig<F> {
    _marker: PhantomData<F>,
}

impl<F: FieldExt> StorageNonExistingConfig<F> {
    #[allow(clippy::too_many_arguments)]
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: impl Fn(&mut VirtualCells<'_, F>) -> Expression<F> + Copy,
        s_main: MainCols<F>,
        c_main: MainCols<F>,
        accs: AccumulatorCols<F>,
        sel2: Column<Advice>, /* should be the same as sel1 as both parallel proofs are the same
                               * for non_existing_storage_proof, but we use C for non-existing
                               * storage */
        is_account_leaf_in_added_branch: Column<Advice>,
        power_of_randomness: [Expression<F>; HASH_WIDTH],
        fixed_table: [Column<Fixed>; 3],
        check_zeros: bool,
    ) -> Self {
        let config = StorageNonExistingConfig {
            _marker: PhantomData,
        };
        let one = Expression::Constant(F::one());
        let c32 = Expression::Constant(F::from(32));
        // key rlc is in the first branch node
        let rot_into_first_branch_child = -(LEAF_NON_EXISTING_IND - 1 + BRANCH_ROWS_NUM);

        let add_wrong_leaf_constraints =
            |meta: &mut VirtualCells<F>,
             constraints: &mut Vec<(&str, Expression<F>)>,
             q_enable: Expression<F>,
             is_short: Expression<F>,
             c_rlp1_cur: Expression<F>,
             c_rlp2_cur: Expression<F>,
             correct_level: Expression<F>,
             is_wrong_leaf: Expression<F>| {
                let sum = meta.query_advice(accs.acc_c.rlc, Rotation::cur());
                let sum_prev = meta.query_advice(accs.acc_c.mult, Rotation::cur());
                let diff_inv = meta.query_advice(accs.acc_s.rlc, Rotation::cur());

                let rot = -(LEAF_NON_EXISTING_IND - LEAF_KEY_C_IND);

                let c_rlp1_prev = meta.query_advice(c_main.rlp1, Rotation(rot));
                let c_rlp2_prev = meta.query_advice(c_main.rlp2, Rotation(rot));

                let mut sum_check_short = Expression::Constant(F::zero());
                let mut sum_prev_check_short = Expression::Constant(F::zero());
                let mut mult = power_of_randomness[0].clone();
                for ind in 0..HASH_WIDTH {
                    sum_check_short = sum_check_short
                        + meta.query_advice(s_main.bytes[ind], Rotation::cur()) * mult.clone();
                    sum_prev_check_short = sum_prev_check_short
                        + meta.query_advice(s_main.bytes[ind], Rotation(rot)) * mult.clone();
                    mult = mult * power_of_randomness[0].clone();
                }
                sum_check_short = sum_check_short + c_rlp1_cur.clone() * mult.clone();
                sum_prev_check_short = sum_prev_check_short + c_rlp1_prev.clone() * mult.clone();

                /*
                We compute the RLC of the key bytes in the STORAGE_NON_EXISTING row. We check whether the computed
                value is the same as the one stored in `accs.acc_c.rlc` column.
                */
                constraints.push((
                    "Wrong leaf sum check (short)",
                    q_enable.clone()
                        * correct_level.clone()
                        * is_wrong_leaf.clone()
                        * is_short.clone()
                        * (sum.clone() - sum_check_short),
                ));

                /*
                We compute the RLC of the key bytes in the STORAGE_LEAF_KEY row. We check whether the computed
                value is the same as the one stored in `accs.acc_c.mult` column.
                */
                constraints.push((
                    "Wrong leaf sum_prev check (short)",
                    q_enable.clone()
                        * correct_level.clone()
                        * is_wrong_leaf.clone()
                        * is_short.clone()
                        * (sum_prev.clone() - sum_prev_check_short),
                ));

                let mut sum_check_long = Expression::Constant(F::zero());
                let mut sum_prev_check_long = Expression::Constant(F::zero());
                let mut mult = power_of_randomness[0].clone();
                // When long, the key starts with `s_main.bytes[1]`.
                for ind in 1..HASH_WIDTH {
                    sum_check_long = sum_check_long
                        + meta.query_advice(s_main.bytes[ind], Rotation::cur()) * mult.clone();
                    sum_prev_check_long = sum_prev_check_long
                        + meta.query_advice(s_main.bytes[ind], Rotation(rot)) * mult.clone();
                    mult = mult * power_of_randomness[0].clone();
                }
                sum_check_long = sum_check_long + c_rlp1_cur * mult.clone();
                sum_prev_check_long = sum_prev_check_long + c_rlp1_prev * mult.clone();
                mult = mult * power_of_randomness[0].clone();
                sum_check_long = sum_check_long + c_rlp2_cur * mult.clone();
                sum_prev_check_long = sum_prev_check_long + c_rlp2_prev * mult;

                /*
                We compute the RLC of the key bytes in the STORAGE_NON_EXISTING row. We check whether the computed
                value is the same as the one stored in `accs.acc_c.rlc` column.
                */
                constraints.push((
                    "Wrong leaf sum check (long)",
                    q_enable.clone()
                        * correct_level.clone()
                        * is_wrong_leaf.clone()
                        * (one.clone() - is_short.clone())
                        * (sum.clone() - sum_check_long),
                ));

                /*
                We compute the RLC of the key bytes in the STORAGE_LEAF_KEY row. We check whether the computed
                value is the same as the one stored in `accs.acc_c.mult` column.
                */
                constraints.push((
                    "Wrong leaf sum_prev check (long)",
                    q_enable.clone()
                        * correct_level.clone()
                        * is_wrong_leaf.clone()
                        * (one.clone() - is_short.clone())
                        * (sum_prev.clone() - sum_prev_check_long),
                ));

                /*
                The key in the LEAF_KEY row and the key in the LEAF_NON_EXISTING row
                are different.
                */
                constraints.push((
                    "Key of a leaf is different than key being inquired",
                    q_enable
                        * correct_level
                        * is_wrong_leaf
                        * (one.clone() - (sum - sum_prev) * diff_inv),
                ));
            };

        /*
        Checks that storage_non_existing_row contains the nibbles that give key_rlc (after considering
        modified_node in branches/extension nodes above).
        Note: currently, for non_existing_storage proof S and C proofs are the same, thus there is never
        a placeholder branch.
        */
        meta.create_gate(
            "Non existing storage proof leaf key RLC (leaf not in first level, branch not placeholder)",
            |meta| {
                let q_enable = q_enable(meta);
                let mut constraints = vec![];

                // Check if there is an account above the leaf.
                let rot_into_last_account_row = -LEAF_NON_EXISTING_IND - 1;
                let is_leaf_in_first_storage_level = meta.query_advice(
                    is_account_leaf_in_added_branch,
                    Rotation(rot_into_last_account_row),
                );

                let rot =  - (LEAF_NON_EXISTING_IND - LEAF_KEY_C_IND);
                let flag1 = meta.query_advice(accs.s_mod_node_rlc, Rotation(rot));
                let flag2 = meta.query_advice(accs.c_mod_node_rlc, Rotation(rot));
                let is_long = flag1.clone() * (one.clone() - flag2.clone());
                let is_short = (one.clone() - flag1.clone()) * flag2.clone();

                // Wrong leaf has a meaning only for non existing storage proof. For this proof, there are two cases:
                // 1. A leaf is returned that is not at the required key (wrong leaf).
                // 2. A branch is returned as the last element of getProof and there is nil object at key position.
                //    Placeholder leaf is added in this case.
                let is_wrong_leaf = meta.query_advice(s_main.rlp1, Rotation::cur());
                // is_wrong_leaf is checked to be bool in `leaf_value.rs` (q_enable in this chip
                // is true only when non_existing_storage_proof).

                let key_rlc_acc_start =
                    meta.query_advice(accs.key.rlc, Rotation(rot_into_first_branch_child));
                let key_mult_start =
                    meta.query_advice(accs.key.mult, Rotation(rot_into_first_branch_child));

                // sel1, sel2 is in init branch
                let is_c16 = meta.query_advice(
                    s_main.bytes[IS_BRANCH_C16_POS - RLP_NUM],
                    Rotation(rot_into_first_branch_child - 1),
                );
                let is_c1 = meta.query_advice(
                    s_main.bytes[IS_BRANCH_C1_POS - RLP_NUM],
                    Rotation(rot_into_first_branch_child - 1),
                );

                let c48 = Expression::Constant(F::from(48));

                // If c16 = 1, we have nibble+48 in s_main.bytes[0].
                let s_bytes0 = meta.query_advice(s_main.bytes[0], Rotation::cur());
                let mut key_rlc_acc_short = key_rlc_acc_start.clone()
                    + (s_bytes0.clone() - c48.clone()) * key_mult_start.clone() * is_c16.clone();
                let mut key_mult = key_mult_start.clone() * power_of_randomness[0].clone() * is_c16.clone();
                key_mult = key_mult + key_mult_start.clone() * is_c1.clone(); // set to key_mult_start if sel2, stays key_mult if sel1

                /*
                If there is an even number of nibbles stored in a leaf, `s_bytes0` needs to be 32.
                */
                constraints.push((
                    "Storage leaf key acc s_bytes0 (short)",
                    q_enable.clone()
                        * (one.clone() - is_leaf_in_first_storage_level.clone())
                        * is_wrong_leaf.clone()
                        * is_short.clone()
                        * (s_bytes0.clone() - c32.clone())
                        * is_c1.clone(),
                ));

                let s_bytes1 = meta.query_advice(s_main.bytes[1], Rotation::cur());
                key_rlc_acc_short = key_rlc_acc_short + s_bytes1.clone() * key_mult.clone();

                for ind in 2..HASH_WIDTH {
                    let s = meta.query_advice(s_main.bytes[ind], Rotation::cur());
                    key_rlc_acc_short = key_rlc_acc_short + s * key_mult.clone() * power_of_randomness[ind - 2].clone();
                }

                let c_rlp1_cur = meta.query_advice(c_main.rlp1, Rotation::cur());

                key_rlc_acc_short = key_rlc_acc_short + c_rlp1_cur.clone() * key_mult.clone() * power_of_randomness[30].clone();

                // Note: `accs.key.mult` is used for a lookup.
                let key_rlc = meta.query_advice(accs.key.mult, Rotation::cur());

                /*
                Differently as for the other proofs, the storage-non-existing proof compares `key_rlc`
                with the key stored in `STORAGE_NON_EXISTING` row, not in `LEAF_KEY` row.

                The crucial thing is that we have a wrong leaf at the key (not exactly the same, just some starting
                set of nibbles is the same) where we are proving there is no leaf.
                If there would be a leaf at the specified key, it would be positioned in the branch where
                the wrong leaf is positioned. Note that the position is determined by the starting set of nibbles.
                Once we add the remaining nibbles to the starting ones, we need to obtain the enquired key.
                There is a complementary constraint which makes sure the remaining nibbles are different for wrong leaf
                and the non-existing leaf (in the case of wrong leaf, while the case with nil being in branch
                is different).
                */
                constraints.push((
                    "Storage key RLC (short)",
                    q_enable.clone()
                        * (one.clone() - is_leaf_in_first_storage_level.clone())
                        * is_wrong_leaf.clone()
                        * is_short.clone()
                        * (key_rlc_acc_short - key_rlc.clone()),
                ));

                // Long

                let mut key_rlc_acc_long = key_rlc_acc_start.clone()
                    + (s_bytes1.clone() - c48) * key_mult_start.clone() * is_c16.clone();
                let mut key_mult = key_mult_start.clone() * power_of_randomness[0].clone() * is_c16;
                key_mult = key_mult + key_mult_start * is_c1.clone(); // set to key_mult_start if sel2, stays key_mult if sel1

                /*
                If there is an even number of nibbles stored in a leaf, `s_bytes1` needs to be 32.
                */
                constraints.push((
                    "Storage leaf key acc s_bytes1 (long)",
                    q_enable.clone()
                        * (one.clone() - is_leaf_in_first_storage_level.clone())
                        * is_wrong_leaf.clone()
                        * is_long.clone()
                        * (s_bytes1.clone() - c32.clone())
                        * is_c1,
                ));

                let s_bytes2 = meta.query_advice(s_main.bytes[2], Rotation::cur());
                key_rlc_acc_long = key_rlc_acc_long + s_bytes2 * key_mult.clone();

                for ind in 3..HASH_WIDTH {
                    let s = meta.query_advice(s_main.bytes[ind], Rotation::cur());
                    key_rlc_acc_long = key_rlc_acc_long + s * key_mult.clone() * power_of_randomness[ind - 3].clone();
                }

                let c_rlp2_cur = meta.query_advice(c_main.rlp2, Rotation::cur());

                key_rlc_acc_long = key_rlc_acc_long + c_rlp1_cur.clone() * key_mult.clone() * power_of_randomness[29].clone();
                key_rlc_acc_long = key_rlc_acc_long + c_rlp2_cur.clone() * power_of_randomness[30].clone();

                /*
                Same as for `Storage key RLC (long)`, but here for the cases when there are two RLP bytes.
                */
                constraints.push((
                    "Storage key RLC (long)",
                    q_enable.clone()
                        * (one.clone() - is_leaf_in_first_storage_level.clone())
                        * is_wrong_leaf.clone()
                        * is_long
                        * (key_rlc_acc_long - key_rlc),
                ));

                add_wrong_leaf_constraints(meta, &mut constraints, q_enable.clone(), is_short, c_rlp1_cur,
                    c_rlp2_cur, one.clone() - is_leaf_in_first_storage_level.clone(), is_wrong_leaf.clone());

                let is_nil_object = meta.query_advice(sel2, Rotation(rot_into_first_branch_child));

                /*
                In case when there is no wrong leaf, we need to check there is a nil object in the parent branch.
                Note that the constraints in `branch.rs` ensure that `sel2` is 1 if and only if there is a nil object
                at `modified_node` position. We check that in case of no wrong leaf in
                the non-existing-storage proof, `is_nil_object` is 1.
                */
                constraints.push((
                    "Nil object in parent branch",
                    q_enable
                        * (one.clone() - is_leaf_in_first_storage_level)
                        * (one.clone() - is_wrong_leaf)
                        * (one.clone() - is_nil_object),
                ));

                constraints
            },
        );

        /*
        Ensuring that the storage does not exist when there is only one storage key in the storage trie.
        Note 1: The hash of the only storage is checked to be the storage root in `leaf_value.rs`.
        Note 2: There is no nil_object case checked in this gate, because it is covered in the gate
        above. That is because when there is a branch (with nil object) in the first level,
        it automatically means the leaf is not in the first level.
        */
        meta.create_gate(
            "Non existing storage proof leaf key RLC (leaf in first level)",
            |meta| {
                let q_enable = q_enable(meta);
                let mut constraints = vec![];

                // Check if there is an account above the leaf.
                let rot_into_last_account_row = -LEAF_NON_EXISTING_IND - 1;
                let is_leaf_in_first_storage_level = meta.query_advice(
                    is_account_leaf_in_added_branch,
                    Rotation(rot_into_last_account_row),
                );

                let rot = -(LEAF_NON_EXISTING_IND - LEAF_KEY_C_IND);
                let flag1 = meta.query_advice(accs.s_mod_node_rlc, Rotation(rot));
                let flag2 = meta.query_advice(accs.c_mod_node_rlc, Rotation(rot));
                let is_long = flag1.clone() * (one.clone() - flag2.clone());
                let is_short = (one.clone() - flag1.clone()) * flag2.clone();

                let is_wrong_leaf = meta.query_advice(s_main.rlp1, Rotation::cur());

                // Note: when leaf is in the first level, the key stored in the leaf is always
                // of length 33 - the first byte being 32 (when after branch,
                // the information whether there the key is odd or even
                // is in s_main.bytes[IS_BRANCH_C16_POS - LAYOUT_OFFSET] (see sel1/sel2).

                let s_bytes0 = meta.query_advice(s_main.bytes[0], Rotation::cur());
                let mut key_rlc_acc_short = Expression::Constant(F::zero());

                constraints.push((
                    "Storage leaf key acc s_bytes0 (short)",
                    q_enable.clone()
                        * (s_bytes0 - c32.clone())
                        * is_wrong_leaf.clone()
                        * is_short.clone()
                        * is_leaf_in_first_storage_level.clone(),
                ));

                let s_bytes1 = meta.query_advice(s_main.bytes[1], Rotation::cur());
                key_rlc_acc_short = key_rlc_acc_short + s_bytes1.clone();

                for ind in 2..HASH_WIDTH {
                    let s = meta.query_advice(s_main.bytes[ind], Rotation::cur());
                    key_rlc_acc_short =
                        key_rlc_acc_short + s * power_of_randomness[ind - 2].clone();
                }

                let c_rlp1_cur = meta.query_advice(c_main.rlp1, Rotation::cur());
                key_rlc_acc_short =
                    key_rlc_acc_short + c_rlp1_cur.clone() * power_of_randomness[30].clone();

                // Note: `accs.key.mult` is used for a lookup.
                let key_rlc = meta.query_advice(accs.key.mult, Rotation::cur());

                constraints.push((
                    "Computed key RLC same as value in key_rlc lookup column (short)",
                    q_enable.clone()
                        * is_leaf_in_first_storage_level.clone()
                        * is_wrong_leaf.clone()
                        * is_short.clone()
                        * (key_rlc_acc_short - key_rlc.clone()),
                ));

                let mut key_rlc_acc_long = Expression::Constant(F::zero());

                constraints.push((
                    "Storage leaf key acc s_bytes1 (long)",
                    q_enable.clone()
                        * (s_bytes1.clone() - c32)
                        * is_wrong_leaf.clone()
                        * is_long.clone()
                        * is_leaf_in_first_storage_level.clone(),
                ));

                let s_bytes2 = meta.query_advice(s_main.bytes[2], Rotation::cur());
                key_rlc_acc_long = key_rlc_acc_long + s_bytes2;

                for ind in 3..HASH_WIDTH {
                    let s = meta.query_advice(s_main.bytes[ind], Rotation::cur());
                    key_rlc_acc_long = key_rlc_acc_long + s * power_of_randomness[ind - 3].clone();
                }

                let c_rlp2_cur = meta.query_advice(c_main.rlp2, Rotation::cur());
                key_rlc_acc_long =
                    key_rlc_acc_long + c_rlp1_cur.clone() * power_of_randomness[29].clone();
                key_rlc_acc_long =
                    key_rlc_acc_long + c_rlp2_cur.clone() * power_of_randomness[30].clone();

                constraints.push((
                    "Computed key RLC same as value in key_rlc lookup column (long)",
                    q_enable.clone()
                        * is_leaf_in_first_storage_level.clone()
                        * is_wrong_leaf.clone()
                        * is_long
                        * (key_rlc_acc_long - key_rlc),
                ));

                add_wrong_leaf_constraints(
                    meta,
                    &mut constraints,
                    q_enable,
                    is_short,
                    c_rlp1_cur,
                    c_rlp2_cur,
                    is_leaf_in_first_storage_level,
                    is_wrong_leaf,
                );

                constraints
            },
        );

        meta.create_gate(
            "Key of wrong leaf and the enquired key are of the same length",
            |meta| {
                let q_enable = q_enable(meta);
                let mut constraints = vec![];

                let rot =  - (LEAF_NON_EXISTING_IND - LEAF_KEY_C_IND);
                let flag1 = meta.query_advice(accs.s_mod_node_rlc, Rotation(rot));
                let flag2 = meta.query_advice(accs.c_mod_node_rlc, Rotation(rot));
                let is_long = flag1.clone() * (one.clone() - flag2.clone());
                let is_short = (one.clone() - flag1.clone()) * flag2.clone();

                let is_wrong_leaf = meta.query_advice(s_main.rlp1, Rotation::cur());
                let len_prev_short = meta.query_advice(s_main.rlp2, Rotation(-(LEAF_NON_EXISTING_IND - LEAF_KEY_C_IND)));
                let len_cur_short = meta.query_advice(s_main.rlp2, Rotation::cur());

                /*
                This constraint is to prevent the attacker to prove that some key does not exist by setting
                some arbitrary number of nibbles in the leaf which would lead to a desired RLC.
                */
                constraints.push((
                    "The number of nibbles in the wrong leaf and the enquired key are the same (short)",
                    q_enable.clone() * is_wrong_leaf.clone() * is_short * (len_cur_short - len_prev_short),
                ));

                let len_prev_long = meta.query_advice(s_main.bytes[0], Rotation(-(LEAF_NON_EXISTING_IND - LEAF_KEY_C_IND)));
                let len_cur_long = meta.query_advice(s_main.bytes[0], Rotation::cur());

                /*
                This constraint is to prevent the attacker to prove that some key does not exist by setting
                some arbitrary number of nibbles in the leaf which would lead to a desired RLC.
                */
                constraints.push((
                    "The number of nibbles in the wrong leaf and the enquired key are the same (short)",
                    q_enable * is_wrong_leaf * is_long * (len_cur_long - len_prev_long),
                ));

                constraints
            },
        );

        let sel_short = |meta: &mut VirtualCells<F>| {
            let q_enable = q_enable(meta);
            let rot = -(LEAF_NON_EXISTING_IND - LEAF_KEY_C_IND);
            let flag1 = meta.query_advice(accs.s_mod_node_rlc, Rotation(rot));
            let flag2 = meta.query_advice(accs.c_mod_node_rlc, Rotation(rot));
            let is_short = (one.clone() - flag1.clone()) * flag2.clone();

            q_enable * is_short
        };
        let sel_long = |meta: &mut VirtualCells<F>| {
            let q_enable = q_enable(meta);
            let rot = -(LEAF_NON_EXISTING_IND - LEAF_KEY_C_IND);
            let flag1 = meta.query_advice(accs.s_mod_node_rlc, Rotation(rot));
            let flag2 = meta.query_advice(accs.c_mod_node_rlc, Rotation(rot));
            let is_long = flag1.clone() * (one.clone() - flag2.clone());

            q_enable * is_long
        };

        /*
        Key RLC is computed over all of `(s_main.bytes[0]), s_main.bytes[1], ..., s_main.bytes[31],
        c_main.rlp1, c_main.rlp2`
        because we do not know the key length in advance.
        To prevent changing the key and setting `s_main.bytes[i]` (or `c_main.rlp1/c_main.rlp2`) for
        `i > key_len + 1` to get the desired key RLC, we need to ensure that
        `s_main.bytes[i] = 0` for `i > key_len + 1`.

        Note that the number of the key bytes in the `LEAF_NON_EXISTING` row needs to be the same as
        the number of the key bytes in the `LEAF_KEY` row.
        */
        if check_zeros {
            for ind in 0..HASH_WIDTH {
                key_len_lookup(
                    meta,
                    sel_short,
                    ind + 1,
                    s_main.rlp2,
                    s_main.bytes[ind],
                    128,
                    fixed_table,
                )
            }
            key_len_lookup(
                meta,
                sel_short,
                32,
                s_main.rlp2,
                c_main.rlp1,
                128,
                fixed_table,
            );

            for ind in 1..HASH_WIDTH {
                key_len_lookup(
                    meta,
                    sel_long,
                    ind,
                    s_main.bytes[0],
                    s_main.bytes[ind],
                    128,
                    fixed_table,
                )
            }
            key_len_lookup(
                meta,
                sel_long,
                32,
                s_main.bytes[0],
                c_main.rlp1,
                128,
                fixed_table,
            );
            key_len_lookup(
                meta,
                sel_long,
                33,
                s_main.bytes[0],
                c_main.rlp2,
                128,
                fixed_table,
            );
        }

        /*
        Range lookups ensure that `s_main`, `c_main.rlp1`, `c_main.rlp2` columns are all bytes (between 0 - 255).
        Note that `c_main.bytes` columns are not used.
        */
        range_lookups(
            meta,
            q_enable,
            s_main.bytes.to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );
        range_lookups(
            meta,
            q_enable,
            [s_main.rlp2, c_main.rlp1, c_main.rlp2].to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );

        config
    }

    pub fn assign(
        &self,
        region: &mut Region<'_, F>,
        mpt_config: &MPTConfig<F>,
        pv: &mut ProofValues<F>,
        witness: &[MptWitnessRow<F>],
        offset: usize,
    ) {
        let row = &witness[offset];
        if row.get_byte_rev(IS_NON_EXISTING_STORAGE_POS) == 0 {
            // No need to assign anything when not non-existing-storage proof.
            return;
        }

        let row_key_c = &witness[offset - (LEAF_NON_EXISTING_IND - LEAF_KEY_C_IND) as usize];

        let mut start = S_START - 1;
        if row_key_c.get_byte(0) == 248 {
            start = S_START;
        }

        let key_len = row_key_c.get_byte(start) as usize - 128;
        let mut sum = F::zero();
        let mut sum_prev = F::zero();
        let mut mult = mpt_config.randomness;
        for i in 0..key_len {
            sum += F::from(row.get_byte(start + 1 + i) as u64) * mult;
            sum_prev += F::from(row_key_c.get_byte(start + 1 + i) as u64) * mult;
            mult *= mpt_config.randomness;
        }
        let mut diff_inv = F::zero();
        if sum != sum_prev {
            diff_inv = F::invert(&(sum - sum_prev)).unwrap();
        }

        /*
        In `account_non_existing.rs` we use `accumulators.key.rlc` and `accumulators.key.mult`
        for storing `sum` and `sum_prev`, but for storage leaf we need `key_rlc` as part of the lookup
        and this is exposed in `accumulators.key.mult` column for other lookups. So here we use
        `accumulators.acc_c.rlc` and `accumulators.acc_c.mult` for `sum` and `sum_prev`.
        */
        region
            .assign_advice(
                || "assign sum".to_string(),
                mpt_config.accumulators.acc_c.rlc,
                offset,
                || Value::known(sum),
            )
            .ok();
        region
            .assign_advice(
                || "assign sum prev".to_string(),
                mpt_config.accumulators.acc_c.mult,
                offset,
                || Value::known(sum_prev),
            )
            .ok();
        region
            .assign_advice(
                || "assign diff inv".to_string(),
                mpt_config.accumulators.acc_s.rlc,
                offset,
                || Value::known(diff_inv),
            )
            .ok();

        let mut key_rlc_new = pv.key_rlc;
        let mut key_rlc_mult_new = pv.key_rlc_mult;
        mpt_config.compute_key_rlc(&row.bytes, &mut key_rlc_new, &mut key_rlc_mult_new, start);

        region
            .assign_advice(
                || "assign key_rlc".to_string(),
                mpt_config.accumulators.key.mult, // lookup uses `key.mult`
                offset,
                || Value::known(key_rlc_new),
            )
            .ok();

        if row.get_byte_rev(IS_NON_EXISTING_STORAGE_POS) == 1 {
            region
                .assign_advice(
                    || "assign lookup enabled".to_string(),
                    mpt_config.proof_type.proof_type,
                    offset,
                    || Value::known(F::from(7_u64)), /* non existing storage lookup enabled in
                                                      * this row if it is non_existing_storage
                                                      * proof */
                )
                .ok();
        }
    }
}
