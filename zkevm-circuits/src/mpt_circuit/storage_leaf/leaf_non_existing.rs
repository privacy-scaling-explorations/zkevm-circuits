use gadgets::util::{not, Expr};
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Region, Value},
    plonk::VirtualCells,
    poly::Rotation,
};
use std::marker::PhantomData;

use crate::{
    circuit,
    evm_circuit::util::rlc,
    mpt_circuit::witness_row::MptWitnessRow,
    mpt_circuit::MPTContext,
    mpt_circuit::{
        helpers::{BaseConstraintBuilder, BranchNodeInfo},
        param::BRANCH_ROWS_NUM,
    },
    mpt_circuit::{
        param::{IS_NON_EXISTING_STORAGE_POS, LEAF_KEY_C_IND, LEAF_NON_EXISTING_IND, S_START},
        MPTConfig, ProofValues,
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

#[derive(Clone, Debug, Default)]
pub(crate) struct StorageNonExistingConfig<F> {
    _marker: PhantomData<F>,
}

impl<F: FieldExt> StorageNonExistingConfig<F> {
    pub fn configure(
        meta: &mut VirtualCells<'_, F>,
        cb: &mut BaseConstraintBuilder<F>,
        ctx: MPTContext<F>,
    ) -> Self {
        let s_main = ctx.s_main;
        let c_main = ctx.c_main;
        let accs = ctx.accumulators;
        // Should be the same as sel1 as both parallel proofs are the same
        // for non_existing_storage_proof, but we use C for non-existing
        // storage
        let sel2 = ctx.denoter.sel2;
        let is_account_leaf_in_added_branch = ctx.account_leaf.is_in_added_branch;
        let r = ctx.r;

        let add_wrong_leaf_constraints =
            |meta: &mut VirtualCells<F>, cb: &mut BaseConstraintBuilder<F>, is_short: bool| {
                circuit!([meta, cb], {
                    let rlc = a!(accs.acc_c.rlc);
                    let rlc_prev = a!(accs.acc_c.mult);
                    let diff_inv = a!(accs.acc_s.rlc);
                    let rot = -(LEAF_NON_EXISTING_IND - LEAF_KEY_C_IND);
                    let start_idx = if is_short { 2 } else { 3 };
                    let end_idx = start_idx + 33;
                    let mut calc_rlc = |rot: i32| {
                        rlc::expr(
                            &[s_main.rlp_bytes(), c_main.rlp_bytes()].concat()[start_idx..end_idx]
                                .iter()
                                .map(|&byte| a!(byte, rot))
                                .collect::<Vec<_>>(),
                            &r,
                        )
                    };
                    // We compute the RLC of the key bytes in the ACCOUNT/STORAGE_NON_EXISTING row.
                    // We check whether the computed value is the same as the
                    // one stored in `accs.key.mult` column.
                    require!(rlc => calc_rlc(0));
                    // We compute the RLC of the key bytes in the ACCOUNT/STORAGE_NON_EXISTING row.
                    // We check whether the computed value is the same as the
                    // one stored in `accs.key.rlc` column.
                    require!(rlc_prev => calc_rlc(rot));
                    // The address in the ACCOUNT/STORAGE_NON_EXISTING row and the address in the
                    // ACCOUNT/STORAGE_NON_EXISTING row are different.
                    // If the difference is 0 there is no inverse.
                    require!((rlc - rlc_prev) * diff_inv => 1);
                });
            };

        circuit!([meta, cb], {
            // key rlc is in the first branch node
            let rot_into_first_branch_child = -(LEAF_NON_EXISTING_IND - 1 + BRANCH_ROWS_NUM);
            let rot_into_branch_init = rot_into_first_branch_child - 1;

            let rot = -(LEAF_NON_EXISTING_IND - LEAF_KEY_C_IND);
            let flag1 = a!(accs.s_mod_node_rlc, rot);
            let flag2 = a!(accs.c_mod_node_rlc, rot);
            let is_long = flag1.clone() * not::expr(flag2.clone());
            let is_short = not::expr(flag1.clone()) * flag2.clone();
            // Wrong leaf has a meaning only for non existing storage proof. For this proof,
            // there are two cases: 1. A leaf is returned that is not at the
            // required key (wrong leaf). 2. A branch is returned as the last
            // element of getProof and there is nil object at key position.
            //    Placeholder leaf is added in this case.
            let is_wrong_leaf = a!(s_main.rlp1);
            // is_wrong_leaf is checked to be bool in `leaf_value.rs`.
            ifx! {is_wrong_leaf => {
                // Check if there is an account above the leaf.
                let rot_into_last_account_row = -LEAF_NON_EXISTING_IND - 1;
                let is_leaf_in_first_storage_level = a!(is_account_leaf_in_added_branch, rot_into_last_account_row);
                ifx!{not::expr(is_leaf_in_first_storage_level.expr()) => {
                    // Checks that storage_non_existing_row contains the nibbles that give key_rlc (after considering
                    // modified_node in branches/extension nodes above).
                    // Note: currently, for non_existing_storage proof S and C proofs are the same, thus there is never
                    // a placeholder branch.

                    let key_rlc_acc_start = a!(accs.key.rlc, rot_into_first_branch_child);
                    let key_mult_start = a!(accs.key.mult, rot_into_first_branch_child);
                    // sel1, sel2 is in init branch
                    let branch = BranchNodeInfo::new(meta, s_main, true, rot_into_branch_init);
                    // Set to key_mult_start * r if is_c16, else key_mult_start
                    let key_mult = key_mult_start.expr() * ifx!{branch.is_c16() => { r[0].expr() } elsex { 1.expr() }};
                    ifx!{is_short => {
                        // If there is an even number of nibbles stored in a leaf, `s_bytes0` needs to be 32.
                        ifx!{branch.is_c1() => {
                            require!(a!(s_main.bytes[0]) => 32);
                        }}
                        // Differently as for the other proofs, the storage-non-existing proof compares `key_rlc`
                        // with the key stored in `STORAGE_NON_EXISTING` row, not in `LEAF_KEY` row.
                        // The crucial thing is that we have a wrong leaf at the key (not exactly the same, just some starting
                        // set of nibbles is the same) where we are proving there is no leaf.
                        // If there would be a leaf at the specified key, it would be positioned in the branch where
                        // the wrong leaf is positioned. Note that the position is determined by the starting set of nibbles.
                        // Once we add the remaining nibbles to the starting ones, we need to obtain the enquired key.
                        // There is a complementary constraint which makes sure the remaining nibbles are different for wrong leaf
                        // and the non-existing leaf (in the case of wrong leaf, while the case with nil being in branch
                        // is different).
                        // If c16 = 1, we have nibble+48 in s_main.bytes[0].
                        let key_rlc = key_rlc_acc_start.expr() + rlc::expr(
                            &[s_main.rlp_bytes(), c_main.rlp_bytes()].concat()[2..35].iter().enumerate().map(|(idx, &byte)|
                                (if idx == 0 { (a!(byte) - 48.expr()) * branch.is_c16() * key_mult_start.expr() } else { a!(byte) * key_mult.expr() })).collect::<Vec<_>>(),
                            &[[1.expr()].to_vec(), r.to_vec()].concat(),
                        );
                        require!(a!(accs.key.mult) => key_rlc);
                        // General wrong leaf constraints
                        add_wrong_leaf_constraints(meta, cb, true);
                    }}
                    ifx!{is_long => {
                        // If there is an even number of nibbles stored in a leaf, `s_bytes1` needs to be 32.
                        ifx!{branch.is_c1() => {
                            require!(a!(s_main.bytes[1]) => 32);
                        }}
                        // Same as for `Storage key RLC (long)`, but here for the cases when there are two RLP bytes.
                        let key_rlc = key_rlc_acc_start.expr() + rlc::expr(
                            &[s_main.rlp_bytes(), c_main.rlp_bytes()].concat()[3..36].iter().enumerate().map(|(idx, &byte)|
                                (if idx == 0 { (a!(byte) - 48.expr()) * branch.is_c16() * key_mult_start.expr() } else { a!(byte) * key_mult.expr() })).collect::<Vec<_>>(),
                            &[[1.expr()].to_vec(), r.to_vec()].concat(),
                        );
                        require!(a!(accs.key.mult) => key_rlc);
                        // General wrong leaf constraints
                        add_wrong_leaf_constraints(meta, cb, false);
                    }}
                } elsex {
                    // Ensuring that the storage does not exist when there is only one storage key in the storage trie.
                    // Note 1: The hash of the only storage is checked to be the storage root in `leaf_value.rs`.
                    // Note 2: There is no nil_object case checked in this gate, because it is covered in the gate
                    // above. That is because when there is a branch (with nil object) in the first level,
                    // it automatically means the leaf is not in the first level.

                    // Note: when leaf is in the first level, the key stored in the leaf is always
                    // of length 33 - the first byte being 32 (when after branch,
                    // the information whether there the key is odd or even
                    // is in s_main.bytes[IS_BRANCH_C16_POS - LAYOUT_OFFSET] (see sel1/sel2).
                    ifx!{is_short => {
                        require!(a!(s_main.bytes[0]) => 32);
                        // RLC check
                        // Note: `accs.key.mult` is used for a lookup.
                        let rlc = rlc::expr(
                            &[s_main.rlp_bytes(), c_main.rlp_bytes()].concat()[3..35].iter().map(|&byte| a!(byte)).collect::<Vec<_>>(),
                            &r,
                        );
                        require!(a!(accs.key.mult) => rlc);
                        // General wrong leaf constraints
                        add_wrong_leaf_constraints(meta, cb, true);
                    }}
                    ifx!{is_long => {
                        require!(a!(s_main.bytes[1]) => 32);
                        // RLC check
                        // Note: `accs.key.mult` is used for a lookup.
                        let rlc = rlc::expr(
                            &[s_main.rlp_bytes(), c_main.rlp_bytes()].concat()[4..36].iter().map(|&byte| a!(byte)).collect::<Vec<_>>(),
                            &r,
                        );
                        require!(a!(accs.key.mult) => rlc);
                        // General wrong leaf constraints
                        add_wrong_leaf_constraints(meta, cb, false);
                    }}
                }}

                // Key of wrong leaf and the enquired key are of the same length
                ifx!{is_short => {
                    // This constraint is to prevent the attacker to prove that some key does not exist by setting
                    // some arbitrary number of nibbles in the leaf which would lead to a desired RLC.
                    let len_prev_short = a!(s_main.rlp2, -(LEAF_NON_EXISTING_IND - LEAF_KEY_C_IND));
                    let len_cur_short = a!(s_main.rlp2);
                    require!(len_cur_short => len_prev_short);
                    // RLC bytes zero check for [s_main.rlp_bytes(), c_main.rlp_bytes()].concat()[2..35].
                    cb.set_range_length(a!(s_main.rlp2) - 128.expr());
                }}
                ifx!{is_long => {
                    // This constraint is to prevent the attacker to prove that some key does not exist by setting
                    // some arbitrary number of nibbles in the leaf which would lead to a desired RLC.
                    let len_prev_long = a!(s_main.bytes[0], -(LEAF_NON_EXISTING_IND - LEAF_KEY_C_IND));
                    let len_cur_long = a!(s_main.bytes[0]);
                    require!(len_cur_long => len_prev_long);
                    // RLC bytes zero check for [s_main.rlp_bytes(), c_main.rlp_bytes()].concat()[3..36]
                    cb.set_range_length(1.expr() + (a!(s_main.bytes[0]) - 128.expr()));
                }}
            } elsex {
                // In case when there is no wrong leaf, we need to check there is a nil object in the parent branch.
                // Note that the constraints in `branch.rs` ensure that `sel2` is 1 if and only if there is a nil object
                // at `modified_node` position. We check that in case of no wrong leaf in
                // the non-existing-storage proof, `is_nil_object` is 1.
                require!(a!(sel2, rot_into_first_branch_child) => true);
            }}
        });

        StorageNonExistingConfig {
            _marker: PhantomData,
        }
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
        let mut mult = F::one();
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
