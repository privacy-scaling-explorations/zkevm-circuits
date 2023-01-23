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

        let rot_key_c = -(LEAF_NON_EXISTING_IND - LEAF_KEY_C_IND);
        let rot_first_child = -(LEAF_NON_EXISTING_IND - 1 + BRANCH_ROWS_NUM);
        let rot_branch_init = rot_first_child - 1;
        let rot_last_account_row = -LEAF_NON_EXISTING_IND - 1;

        circuit!([meta, cb.base], {
            let storage = StorageLeafInfo::new(meta, ctx.clone(), true, rot_key_c);
            let is_wrong_leaf = a!(s_main.rlp1);

            // Make sure is_wrong_leaf is boolean
            require!(is_wrong_leaf => bool);

            ifx! {a!(proof_type.is_non_existing_storage_proof) => {
                ifx! {is_wrong_leaf => {
                    // Get the previous key RLC data
                    let (key_rlc_prev, key_mult_prev, is_key_odd) = ifx!{not!(ctx.is_account(meta, rot_last_account_row)) => {
                        let branch = BranchNodeInfo::new(meta, ctx.clone(), true, rot_branch_init);
                        (a!(accs.key.rlc, rot_first_child), a!(accs.key.mult, rot_first_child), branch.is_key_odd())
                    } elsex {
                        (0.expr(), 1.expr(), false.expr())
                    }};
                    // Calculate the key and check it's the address as requested in the lookup
                    let key_rlc_wrong = key_rlc_prev + storage.key_rlc(meta, &mut cb.base, key_mult_prev.expr(), is_key_odd.expr(), 1.expr(), false);
                    require!(a!(accs.key.mult) => key_rlc_wrong);
                    // Now make sure this address is different than the one of the leaf
                    let diff_inv = a!(accs.acc_s.rlc);
                    require!((a!(accs.key.mult) - a!(accs.key.rlc, rot_key_c)) * diff_inv => 1);
                    // Make sure the lengths of the keys are the same
                    let mut storage_wrong = StorageLeafInfo::new(meta, ctx.clone(), true, rot_key_c);
                    storage_wrong.set_rot_key(0);
                    require!(storage_wrong.key_len(meta) => storage.key_len(meta));
                    // RLC bytes zero check
                    let num_bytes = storage.num_bytes_on_key_row(meta);
                    cb.set_length(num_bytes);
                } elsex {
                    // In case when there is no wrong leaf, we need to check there is a nil object in the parent branch.
                    let branch = BranchNodeInfo::new(meta, ctx.clone(), false, rot_branch_init);
                    require!(branch.contains_placeholder_leaf(meta, false) => true);
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

        let diff_inv = (key_rlc_new - pv.storage_key_rlc)
            .invert()
            .unwrap_or(F::zero());
        region
            .assign_advice(
                || "assign diff inv".to_string(),
                mpt_config.accumulators.acc_s.rlc,
                offset,
                || Value::known(diff_inv),
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
