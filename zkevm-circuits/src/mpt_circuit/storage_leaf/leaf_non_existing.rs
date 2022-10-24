use halo2_proofs::{
    circuit::{Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, VirtualCells},
    poly::Rotation,
    arithmetic::FieldExt,
};
use std::marker::PhantomData;

use crate::{
    mpt_circuit::columns::{AccumulatorCols, MainCols},
    mpt_circuit::helpers::range_lookups,
    mpt_circuit::{FixedTableTag, MPTConfig, param::{IS_NON_EXISTING_STORAGE_POS, LEAF_NON_EXISTING_IND, LEAF_KEY_C_IND, S_START}, helpers::key_len_lookup, ProofValues},
    mpt_circuit::param::{
        BRANCH_ROWS_NUM, HASH_WIDTH, IS_BRANCH_C16_POS, IS_BRANCH_C1_POS, RLP_NUM,
    },
    mpt_circuit::witness_row::MptWitnessRow,
};

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
        sel1: Column<Advice>, /* should be the same as sel2 as both parallel proofs are the same
                               * for non_existing_storage_proof */
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
             c_rlp1_cur: Expression<F>,
             c_rlp2_cur: Expression<F>,
             correct_level: Expression<F>,
             is_wrong_leaf: Expression<F>| {
                let sum = meta.query_advice(accs.acc_c.rlc, Rotation::cur());
                let sum_prev = meta.query_advice(accs.acc_c.mult, Rotation::cur());
                let diff_inv = meta.query_advice(accs.acc_s.rlc, Rotation::cur());

                let rot =  - (LEAF_NON_EXISTING_IND - LEAF_KEY_C_IND);

                let c_rlp1_prev = meta.query_advice(c_main.rlp1, Rotation(rot));
                let c_rlp2_prev = meta.query_advice(c_main.rlp2, Rotation(rot));

                let mut sum_check = Expression::Constant(F::zero());
                let mut sum_prev_check = Expression::Constant(F::zero());
                let mut mult = power_of_randomness[0].clone();
                // TODO: long leaf
                for ind in 0..HASH_WIDTH {
                    sum_check = sum_check
                        + meta.query_advice(s_main.bytes[ind], Rotation::cur()) * mult.clone();
                    sum_prev_check = sum_prev_check
                        + meta.query_advice(s_main.bytes[ind], Rotation(rot)) * mult.clone();
                    mult = mult * power_of_randomness[0].clone();
                }
                sum_check = sum_check + c_rlp1_cur * mult.clone();
                sum_prev_check = sum_prev_check + c_rlp1_prev * mult.clone();
                /*
                mult = mult * power_of_randomness[0].clone();
                sum_check = sum_check + c_rlp2_cur * mult.clone();
                sum_prev_check = sum_prev_check + c_rlp2_prev * mult;
                */

                /*
                We compute the RLC of the key bytes in the STORAGE_NON_EXISTING row. We check whether the computed
                value is the same as the one stored in `accs.acc_c.rlc` column.
                */
                constraints.push((
                    "Wrong leaf sum check",
                    q_enable.clone()
                        * correct_level.clone()
                        * is_wrong_leaf.clone()
                        * (sum.clone() - sum_check),
                ));

                /*
                We compute the RLC of the key bytes in the STORAGE_LEAF_KEY row. We check whether the computed
                value is the same as the one stored in `accs.acc_c.mult` column.
                */
                constraints.push((
                    "Wrong leaf sum_prev check",
                    q_enable.clone()
                        * correct_level.clone()
                        * is_wrong_leaf.clone()
                        * (sum_prev.clone() - sum_prev_check),
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

                // Wrong leaf has a meaning only for non existing storage proof. For this proof, there are two cases:
                // 1. A leaf is returned that is not at the required key (wrong leaf).
                // 2. A branch is returned as the last element of getProof and there is nil object at key position.
                //    Placeholder leaf is added in this case.
                let is_wrong_leaf = meta.query_advice(s_main.rlp1, Rotation::cur());
                // TODO: is_wrong_leaf is checked to be bool in account_leaf_nonce_balance (q_enable in this chip
                // is true only when non_existing_account).

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
                let mut key_rlc_acc = key_rlc_acc_start.clone()
                    + (s_bytes0.clone() - c48) * key_mult_start.clone() * is_c16.clone();
                let mut key_mult = key_mult_start.clone() * power_of_randomness[0].clone() * is_c16;
                key_mult = key_mult + key_mult_start * is_c1.clone(); // set to key_mult_start if sel2, stays key_mult if sel1

                /*
                If there is an even number of nibbles stored in a leaf, `s_bytes0` needs to be 32.
                */
                constraints.push((
                    "Storage leaf key acc s_bytes0",
                    q_enable.clone()
                        * (one.clone() - is_leaf_in_first_storage_level.clone())
                        * is_wrong_leaf.clone()
                        * (s_bytes0 - c32.clone())
                        * is_c1,
                ));

                let s_bytes1 = meta.query_advice(s_main.bytes[1], Rotation::cur());
                key_rlc_acc = key_rlc_acc + s_bytes1 * key_mult.clone();

                for ind in 2..HASH_WIDTH {
                    let s = meta.query_advice(s_main.bytes[ind], Rotation::cur());
                    key_rlc_acc = key_rlc_acc + s * key_mult.clone() * power_of_randomness[ind - 2].clone();
                }

                let c_rlp1_cur = meta.query_advice(c_main.rlp1, Rotation::cur());
                let c_rlp2_cur = meta.query_advice(c_main.rlp2, Rotation::cur());

                key_rlc_acc = key_rlc_acc + c_rlp1_cur.clone() * key_mult.clone() * power_of_randomness[30].clone();
                // key_rlc_acc = key_rlc_acc + c_rlp2_cur.clone() * power_of_randomness[31].clone();

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
                    "Storage key RLC",
                    q_enable.clone()
                        * (one.clone() - is_leaf_in_first_storage_level.clone())
                        * is_wrong_leaf.clone()
                        * (key_rlc_acc - key_rlc),
                ));

                add_wrong_leaf_constraints(meta, &mut constraints, q_enable.clone(), c_rlp1_cur,
                    c_rlp2_cur, one.clone() - is_leaf_in_first_storage_level.clone(), is_wrong_leaf.clone());
 
                let is_nil_object = meta.query_advice(sel1, Rotation(rot_into_first_branch_child));

                /*
                In case when there is no wrong leaf, we need to check there is a nil object in the parent branch.
                Note that the constraints in `branch.rs` ensure that `sel1` is 1 if and only if there is a nil object
                at `modified_node` position. We check that in case of no wrong leaf in
                the non-existing-account proof, `sel1` is 1.
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

                let is_wrong_leaf = meta.query_advice(s_main.rlp1, Rotation::cur());

                // Note: when leaf is in the first level, the key stored in the leaf is always
                // of length 33 - the first byte being 32 (when after branch,
                // the information whether there the key is odd or even
                // is in s_main.bytes[IS_BRANCH_C16_POS - LAYOUT_OFFSET] (see sel1/sel2).

                // TODO: long leaf

                let s_bytes0 = meta.query_advice(s_main.bytes[0], Rotation::cur());
                let mut key_rlc_acc = Expression::Constant(F::zero());

                constraints.push((
                    "Storage leaf key acc s_bytes0",
                    q_enable.clone()
                        * (s_bytes0 - c32)
                        * is_wrong_leaf.clone()
                        * is_leaf_in_first_storage_level.clone(),
                ));

                let s_bytes1 = meta.query_advice(s_main.bytes[1], Rotation::cur());
                key_rlc_acc = key_rlc_acc + s_bytes1;

                for ind in 2..HASH_WIDTH {
                    let s = meta.query_advice(s_main.bytes[ind], Rotation::cur());
                    key_rlc_acc = key_rlc_acc + s * power_of_randomness[ind - 2].clone();
                }

                let c_rlp1_cur = meta.query_advice(c_main.rlp1, Rotation::cur());
                let c_rlp2_cur = meta.query_advice(c_main.rlp2, Rotation::cur());
                key_rlc_acc = key_rlc_acc + c_rlp1_cur.clone() * power_of_randomness[30].clone();
                // key_rlc_acc = key_rlc_acc + c_rlp2_cur.clone() * power_of_randomness[31].clone();

                // Note: `accs.key.mult` is used for a lookup.
                let key_rlc = meta.query_advice(accs.key.mult, Rotation::cur());

                constraints.push((
                    "Computed key RLC same as value in key_rlc lookup column",
                    q_enable.clone()
                        * is_leaf_in_first_storage_level.clone()
                        * is_wrong_leaf.clone()
                        * (key_rlc_acc - key_rlc),
                ));

                add_wrong_leaf_constraints(
                    meta,
                    &mut constraints,
                    q_enable,
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

                // TODO: long leaf
                let is_wrong_leaf = meta.query_advice(s_main.rlp1, Rotation::cur());
                let len_prev = meta.query_advice(s_main.rlp2, Rotation(-(LEAF_NON_EXISTING_IND - LEAF_KEY_C_IND)));
                let len_cur = meta.query_advice(s_main.rlp2, Rotation::cur());

                /*
                This constraint is to prevent the attacker to prove that some key does not exist by setting
                some arbitrary number of nibbles in the leaf which would lead to a desired RLC.
                */
                constraints.push((
                    "The number of nibbles in the wrong leaf and the enquired key are the same",
                    q_enable * is_wrong_leaf * (len_cur - len_prev),
                ));

                constraints
            },
        );

        /*
        Key RLC is computed over all of `(s_main.bytes[0]), s_main.bytes[1], ..., s_main.bytes[31],
        c_main.rlp1, c_main.rlp2`
        because we do not know the key length in advance.
        To prevent changing the key and setting `s_main.bytes[i]` (or `c_main.rlp1/c_main.rlp2`) for
        `i > key_len + 1` to get the desired key RLC, we need to ensure that
        `s_main.bytes[i] = 0` for `i > key_len + 1`.

        Note that the number of the key bytes in the `ACCOUNT_NON_EXISTING` row needs to be the same as
        the number of the key bytes in the `ACCOUNT_LEAF_KEY` row.

        Note: the key length is always in s_main.bytes[0] here as opposed to storage
        key leaf where it can appear in `s_rlp2` too. This is because the account
        leaf contains nonce, balance, ... which makes it always longer than 55 bytes,
        which makes a RLP to start with 248 (`s_rlp1`) and having one byte (in `s_rlp2`)
        for the length of the remaining stream.
        */
        // TODO: short/long leaf
        if check_zeros {
            for ind in 1..HASH_WIDTH {
                key_len_lookup(
                    meta,
                    q_enable,
                    ind,
                    s_main.bytes[0],
                    s_main.bytes[ind],
                    128,
                    fixed_table,
                )
            }
            key_len_lookup(meta, q_enable, 32, s_main.bytes[0], c_main.rlp1, 128, fixed_table);
            key_len_lookup(meta, q_enable, 33, s_main.bytes[0], c_main.rlp2, 128, fixed_table);
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
        let row_key_c = &witness[offset - (LEAF_NON_EXISTING_IND - LEAF_KEY_C_IND) as usize];
        let row = &witness[offset];

        // let start = 2; // TODO: handle different cases: short / long / one-nibble / last-level
        let mut start = S_START - 1;
        if row.get_byte(0) == 248 { // TODO: row[0] stores info about wrong leaf
            // long RLP
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

        println!("{:?}", &row.bytes);

        let mut key_rlc_new = pv.key_rlc;
        let mut key_rlc_mult_new = pv.key_rlc_mult;
        // if typ != "last_level" && typ != "one_nibble" {
            // If in last level or having only one nibble,
            // the key RLC is already computed using the first two bytes above.
            mpt_config.compute_key_rlc(&row.bytes, &mut key_rlc_new, &mut key_rlc_mult_new, start);
        // }
    
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
                    || Value::known(F::from(7_u64)), // non existing storage lookup enabled in this row if it is non_existing_storage proof
                )
                .ok();
        }
    }
}
