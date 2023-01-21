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
    mpt_circuit::{
        helpers::{bytes_into_rlc, BranchNodeInfo},
        param::{ACCOUNT_NON_EXISTING_IND, BRANCH_ROWS_NUM},
        ProofValues,
    },
    mpt_circuit::{
        helpers::{AccountLeafInfo, MPTConstraintBuilder},
        MPTContext,
    },
    mpt_circuit::{param::IS_NON_EXISTING_ACCOUNT_POS, MPTConfig},
};

/*
An account leaf occupies 8 rows.
Contrary as in the branch rows, the `S` and `C` leaves are not positioned parallel to each other.
The rows are the following:
ACCOUNT_LEAF_KEY_S
ACCOUNT_LEAF_KEY_C
ACCOUNT_NON_EXISTING
ACCOUNT_LEAF_NONCE_BALANCE_S
ACCOUNT_LEAF_NONCE_BALANCE_C
ACCOUNT_LEAF_STORAGE_CODEHASH_S
ACCOUNT_LEAF_STORAGE_CODEHASH_C
ACCOUNT_DRIFTED_LEAF

The constraints in this file apply to ACCOUNT_NON_EXISTING.

For example, the row might be:
[0,0,0,32,252,237,52,8,133,130,180,167,143,97,28,115,102,25,94,62,148,249,8,6,55,244,16,75,187,208,208,127,251,120,61,73,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

We are proving that there is no account at the specified address. There are two versions of proof:
    1. A leaf is returned by getProof that is not at the required address (we call this a wrong leaf).
    In this case, the `ACCOUNT_NON_EXISTING` row contains the nibbles of the address (the nibbles that remain
    after the nibbles used for traversing through the branches are removed) that was enquired
    while `ACCOUNT_LEAF_KEY` row contains the nibbles of the wrong leaf. We need to prove that
    the difference is nonzero. This way we prove that there exists some account which has some
    number of the starting nibbles the same as the enquired address (the path through branches
    above the leaf), but at the same time the full address is not the same - the nibbles stored in a leaf differ.
    2. A branch is the last element of the getProof response and there is a nil object
    at the address position. Placeholder account leaf is added in this case.
    In this case, the `ACCOUNT_NON_EXISTING` row contains the same nibbles as `ACCOUNT_LEAF_KEY` and it is
    not needed. We just need to prove that the branch contains nil object (128) at the enquired address.

The whole account leaf looks like:
[248,106,161,32,252,237,52,8,133,130,180,167,143,97,28,115,102,25,94,62,148,249,8,6,55,244,16,75,187,208,208,127,251,120,61,73,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
[248,106,161,32,252,237,52,8,133,130,180,167,143,97,28,115,102,25,94,62,148,249,8,6,55,244,16,75,187,208,208,127,251,120,61,73,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
[0,0,0,32,252,237,52,8,133,130,180,167,143,97,28,115,102,25,94,62,148,249,8,6,55,244,16,75,187,208,208,127,251,120,61,73,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
[184,70,128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,248,68,128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
[184,70,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,248,68,128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
[0,160,86,232,31,23,27,204,85,166,255,131,69,230,146,192,248,110,91,72,224,27,153,108,173,192,1,98,47,181,227,99,180,33,0,160,197,210,70,1,134,247,35,60,146,126,125,178,220,199,3,192,229,0,182,83,202,130,39,59,123,250,216,4,93,133,164,122]
[0,160,86,232,31,23,27,204,85,166,255,131,69,230,146,192,248,110,91,72,224,27,153,108,173,192,1,98,47,181,227,99,180,33,0,160,197,210,70,1,134,247,35,60,146,126,125,178,220,199,3,192,229,0,182,83,202,130,39,59,123,250,216,4,93,133,164,122]
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

We can observe that the example account leaf above is not for non-existing account proof as the first and third
rows contain the same nibbles (the difference is solely in RLP specific bytes which are not needed
in `ACCOUNT_NON_EXISTING` row).

For the example of non-existing account proof account leaf see below:

[248 102 157 55 236 125 29 155 142 209 241 75 145 144 143 254 65 81 209 56 13 192 157 236 195 213 73 132 11 251 149 241 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 6]
[248 102 157 55 236 125 29 155 142 209 241 75 145 144 143 254 65 81 209 56 13 192 157 236 195 213 73 132 11 251 149 241 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 4]
[1 0 157 56 133 130 180 167 143 97 28 115 102 25 94 62 148 249 8 6 55 244 16 75 187 208 208 127 251 120 61 73 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 18]
[184 70 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 248 68 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 7]
[184 70 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 248 68 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 8]
[0 160 112 158 181 221 162 20 124 79 184 25 162 13 167 162 146 25 237 242 59 120 184 154 118 137 92 181 187 152 115 82 223 48 0 160 7 190 1 231 231 32 111 227 30 206 233 26 215 93 173 166 90 214 186 67 58 230 71 161 185 51 4 105 247 198 103 124 0 9]
[0 160 112 158 181 221 162 20 124 79 184 25 162 13 167 162 146 25 237 242 59 120 184 154 118 137 92 181 187 152 115 82 223 48 0 160 7 190 1 231 231 32 111 227 30 206 233 26 215 93 173 166 90 214 186 67 58 230 71 161 185 51 4 105 247 198 103 124 0 11]
[0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 10]

In this case, the nibbles in the third row are different from the nibbles in the first or second row. Here, we are
proving that the account does not exist at the address which starts with the same nibbles as the leaf that is
in the rows above (except for the `ACCOUNT_NON_EXISTING` row) and continues with nibbles `ACCOUNT_NON_EXISTING` row.

Note that the selector (being 1 in this case) at `s_main.rlp1` specifies whether it is wrong leaf or nil case.

Lookups:
The `non_existing_account_proof` lookup is enabled in `ACCOUNT_NON_EXISTING` row.

Differently than for the other proofs, the account-non-existing proof compares `address_rlc`
with the address stored in `ACCOUNT_NON_EXISTING` row, not in `ACCOUNT_LEAF_KEY` row.
The crucial thing is that we have a wrong leaf at the address (not exactly the same, just some starting
set of nibbles is the same) where we are proving there is no account.
If there would be an account at the specified address, it would be positioned in the branch where
the wrong account is positioned. Note that the position is determined by the starting set of nibbles.
Once we add the remaining nibbles to the starting ones, we need to obtain the enquired address.

/* Non existing account proof leaf address RLC (leaf in first level) */
Ensuring that the account does not exist when there is only one account in the state trie.
Note 1: The hash of the only account is checked to be the state root.
Note 2: There is no nil_object case checked in this gate, because it is covered in the gate
above. That is because when there is a branch (with nil object) in the first level,
it automatically means the account leaf is not in the first level.

*/

#[derive(Clone, Debug, Default)]
pub(crate) struct AccountNonExistingConfig<F> {
    _marker: PhantomData<F>,
}

impl<F: FieldExt> AccountNonExistingConfig<F> {
    pub fn configure(
        meta: &mut VirtualCells<'_, F>,
        cb: &mut MPTConstraintBuilder<F>,
        ctx: MPTContext<F>,
    ) -> Self {
        let proof_type = ctx.proof_type;
        let not_first_level = ctx.position_cols.not_first_level;
        let accs = ctx.accumulators;
        let address_rlc = ctx.address_rlc;

        let rot_key_s = -ACCOUNT_NON_EXISTING_IND;
        let rot_first_branch = -(ACCOUNT_NON_EXISTING_IND - 1 + BRANCH_ROWS_NUM);
        let rot_branch_init = rot_first_branch - 1;

        circuit!([meta, cb.base], {
            let account = AccountLeafInfo::new(meta, ctx.clone(), rot_key_s);

            // Make sure is_wrong_leaf is boolean
            require!(account.is_wrong_leaf(meta, true) => bool);

            ifx! {a!(proof_type.is_non_existing_account_proof) => {
                ifx! {account.is_wrong_leaf(meta, true) => {
                    // Note: currently, for non_existing_account proof S and C
                    // proofs are the same, thus there is never a placeholder branch.
                    let (key_rlc_prev, key_mult_prev, is_key_odd) = ifx! {a!(not_first_level) => {
                        let branch = BranchNodeInfo::new(meta, ctx.clone(), true, rot_branch_init);
                        (a!(accs.key.rlc, rot_first_branch), a!(accs.key.mult, rot_first_branch), branch.is_key_odd())
                    } elsex {
                        (0.expr(), 1.expr(), false.expr())
                    }};
                    // Calculate the key and check it's the address as requested in the lookup
                    let key_rlc_wrong = key_rlc_prev + account.key_rlc(meta, &mut cb.base, key_mult_prev, is_key_odd, 1.expr());
                    require!(a!(address_rlc) => key_rlc_wrong);
                    // Now make sure this address is different than the one of the leaf
                    let diff_inv = a!(accs.acc_s.rlc);
                    require!((a!(address_rlc) - a!(accs.key.rlc, rot_key_s)) * diff_inv => 1);
                    // Make sure the lengths of the keys are the same
                    let account_wrong = AccountLeafInfo::new(meta, ctx.clone(), 0);
                    require!(account_wrong.key_len(meta) => account.key_len(meta));
                    // RLC bytes zero check
                    let leaf = AccountLeafInfo::new(meta, ctx.clone(), 0);
                    let num_bytes = leaf.num_bytes_on_key_row(meta);
                    cb.set_length(num_bytes - 2.expr());
                } elsex {
                    // In case when there is no wrong leaf, we need to check there is a nil object in the parent branch.
                    let branch = BranchNodeInfo::new(meta, ctx.clone(), true, rot_branch_init);
                    require!(branch.contains_placeholder_leaf(meta, true) => true);
                }}
            } elsex {
                // is_wrong_leaf needs to be false when not in non_existing_account proof
                require!(account.is_wrong_leaf(meta, true) => false);
            }};
        });

        AccountNonExistingConfig {
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
        let address_rlc = bytes_into_rlc(row.address_bytes(), mpt_config.randomness);
        let diff_inv = (address_rlc - pv.account_key_rlc)
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

        if row.get_byte_rev(IS_NON_EXISTING_ACCOUNT_POS) == 1 {
            region
                .assign_advice(
                    || "assign lookup enabled".to_string(),
                    mpt_config.proof_type.proof_type,
                    offset,
                    || Value::known(F::from(4_u64)), /* non existing account lookup enabled in
                                                      * this row if it is non_existing_account
                                                      * proof */
                )
                .ok();
        }
    }
}
