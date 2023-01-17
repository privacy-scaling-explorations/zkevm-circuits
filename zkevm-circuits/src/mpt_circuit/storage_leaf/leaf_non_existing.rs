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
    mpt_circuit::witness_row::MptWitnessRow,
    mpt_circuit::{helpers::MPTConstraintBuilder, MPTContext},
    mpt_circuit::{
        helpers::{BranchNodeInfo, StorageLeafInfo},
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

Wrong leaf has a meaning only for non existing storage proof. For this proof,
there are two cases: 1. A leaf is returned that is not at the
required key (wrong leaf). 2. A branch is returned as the last
element of getProof and there is nil object at key position.
Placeholder leaf is added in this case.

Ensuring that the storage does not exist when there is only one storage key in the storage trie.
Note 1: The hash of the only storage is checked to be the storage root in `leaf_value.rs`.
Note 2: There is no nil_object case checked in this gate, because it is covered in the gate
above. That is because when there is a branch (with nil object) in the first level,
it automatically means the leaf is not in the first level.

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

#[derive(Clone, Debug, Default)]
pub(crate) struct StorageNonExistingConfig<F> {
    _marker: PhantomData<F>,
}

impl<F: FieldExt> StorageNonExistingConfig<F> {
    pub fn configure(
        meta: &mut VirtualCells<'_, F>,
        cb: &mut MPTConstraintBuilder<F>,
        ctx: MPTContext<F>,
    ) -> Self {
        let proof_type = ctx.proof_type;
        let s_main = ctx.s_main;
        let accs = ctx.accumulators;
        // Should be the same as sel1 as both parallel proofs are the same
        // for non_existing_storage_proof, but we use C for non-existing
        // storage
        let is_modified_node_empty = ctx.denoter.sel2;

        let rot_key_c = -(LEAF_NON_EXISTING_IND - LEAF_KEY_C_IND);
        let rot_first_child = -(LEAF_NON_EXISTING_IND - 1 + BRANCH_ROWS_NUM);
        let rot_branch_init = rot_first_child - 1;
        let rot_last_account_row = -LEAF_NON_EXISTING_IND - 1;

        let add_wrong_leaf_constraints =
            |meta: &mut VirtualCells<F>, cb: &mut MPTConstraintBuilder<F>, is_short: bool| {
                circuit!([meta, cb.base], {
                    let rlc = a!(accs.acc_c.rlc);
                    let rlc_prev = a!(accs.acc_c.mult);
                    let diff_inv = a!(accs.acc_s.rlc);
                    let rot = -(LEAF_NON_EXISTING_IND - LEAF_KEY_C_IND);
                    let start_idx = if is_short { 2 } else { 3 };
                    let end_idx = start_idx + 33;
                    // We compute the RLC of the key bytes in the ACCOUNT/STORAGE_NON_EXISTING row.
                    // We check whether the computed value is the same as the
                    // one stored in `accs.key.mult` column.
                    require!(rlc => ctx.rlc(meta, start_idx..end_idx, 0));
                    // We compute the RLC of the key bytes in the ACCOUNT/STORAGE_NON_EXISTING row.
                    // We check whether the computed value is the same as the
                    // one stored in `accs.key.rlc` column.
                    require!(rlc_prev => ctx.rlc(meta, start_idx..end_idx, rot));
                    // The address in the ACCOUNT/STORAGE_NON_EXISTING row and the address in the
                    // ACCOUNT/STORAGE_NON_EXISTING row are different.
                    // If the difference is 0 there is no inverse.
                    require!((rlc - rlc_prev) * diff_inv => 1);
                });
            };

        circuit!([meta, cb.base], {
            //let leaf = StorageLeafInfo::new(meta, ctx.clone(), 0);
            let leaf_prev = StorageLeafInfo::new(meta, ctx.clone(), true, rot_key_c);

            let is_wrong_leaf = a!(s_main.rlp1);
            // Make sure is_wrong_leaf is boolean
            require!(is_wrong_leaf => bool);

            ifx! {a!(proof_type.is_non_existing_storage_proof) => {
                ifx! {is_wrong_leaf => {
                    // Get the previous RLC data
                    let (key_rlc_prev, key_mult_prev, is_key_odd) = ifx!{not!(ctx.is_account(meta, rot_last_account_row)) => {
                        let branch = BranchNodeInfo::new(meta, ctx.clone(), true, rot_branch_init);
                        (a!(accs.key.rlc, rot_first_child), a!(accs.key.mult, rot_first_child), branch.is_key_odd())
                    } elsex {
                        (0.expr(), 1.expr(), false.expr())
                    }};
                    // Check that the stored RLC is correct
                    let key_rlc = leaf_prev.key_rlc(meta, &mut cb.base, ctx.clone(), key_mult_prev, is_key_odd.expr(), 1.expr(), false);
                    require!(a!(accs.key.mult) => key_rlc_prev.expr() + key_rlc);

                    // TODO(Brecht): Somehow we need to use the flags on the key_c row to calculate these and the RLC
                    // (instead of just using the flags on the current row).
                    let (len_prev, len) = matchx! {
                        leaf_prev.is_short() => {
                            // Key RLC needs to be different
                            add_wrong_leaf_constraints(meta, cb, true);
                            (a!(s_main.rlp2, rot_key_c), a!(s_main.rlp2))
                        },
                        leaf_prev.is_long() => {
                            // Key RLC needs to be different
                            add_wrong_leaf_constraints(meta, cb, false);
                            (a!(s_main.bytes[0], rot_key_c), a!(s_main.bytes[0]))
                        },
                    };

                    // Key of wrong leaf and the enquired key are of the same length.
                    // This constraint is to prevent the attacker to prove that some key does not exist by setting
                    // some arbitrary number of nibbles in the leaf which would lead to a desired RLC.
                    //let len = leaf.key_len(meta, &mut cb.base, ctx.clone());
                    //let len_prev = leaf_prev.key_len(meta, &mut cb.base, ctx.clone());
                    require!(len => len_prev);
                    // RLC bytes zero check (subtract 2 for first two RLP bytes)
                    let num_rlp_bytes = leaf_prev.num_rlp_bytes(meta, &mut cb.base);
                    cb.set_length(num_rlp_bytes + (len - 128.expr()) - 2.expr());
                } elsex {
                    // In case when there is no wrong leaf, we need to check there is a nil object in the parent branch.
                    // Note that the constraints in `branch.rs` ensure that `sel2` is 1 if and only if there is a nil object
                    // at `modified_node` position. We check that in case of no wrong leaf in
                    // the non-existing-storage proof, `is_nil_object` is 1.
                    require!(a!(is_modified_node_empty, rot_first_child) => true);
                }}
            } elsex {
                // is_wrong_leaf needs to be false when not in non_existing_account proof
                require!(is_wrong_leaf => false);
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
