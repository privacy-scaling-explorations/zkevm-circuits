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
    circuit_tools::DataTransition,
    evm_circuit::util::rlc,
    mpt_circuit::{
        helpers::{accumulate_rand, BranchNodeInfo, MPTConstraintBuilder},
        param::{
            ACCOUNT_LEAF_KEY_C_IND, ACCOUNT_LEAF_KEY_S_IND, ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND,
            ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND, ACCOUNT_NON_EXISTING_IND, BRANCH_ROWS_NUM,
            C_START, HASH_WIDTH, IS_CODEHASH_MOD_POS, S_START,
        },
        MPTContext,
    },
    mpt_circuit::{
        param::ARITY,
        witness_row::{MptWitnessRow, MptWitnessRowType},
    },
    mpt_circuit::{MPTConfig, ProofValues},
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

The constraints in this file apply to ACCOUNT_LEAF_STORAGE_CODEHASH_S and
ACCOUNT_LEAF_STORAGE_CODEHASH_C rows.

For example, the two rows might be:
[0,160,86,232,31,23,27,204,85,166,255,131,69,230,146,192,248,110,91,72,224,27,153,108,173,192,1,98,47,181,227,99,180,33,0,160,197,210,70,1,134,247,35,60,146,126,125,178,220,199,3,192,229,0,182,83,202,130,39,59,123,250,216,4,93,133,164,122]
[0,160,86,232,31,23,27,204,85,166,255,131,69,230,146,192,248,110,91,72,224,27,153,108,173,192,1,98,47,181,227,99,180,33,0,160,197,210,70,1,134,247,35,60,146,126,125,178,220,199,3,192,229,0,182,83,202,130,39,59,123,250,216,4,93,133,164,122]

Here, in `ACCOUNT_LEAF_STORAGE_CODEHASH_S` example row, there is `S` storage root stored in `s_main.bytes`
and `S` codehash in `c_main.bytes`. Both these values are hash outputs.
We can see `s_main.rlp2 = 160` which specifies that the length of the following string is `32 = 160 - 128`
(which is hash output). Similarly, `c_main.rlp2 = 160`.

In `ACCOUNT_LEAF_STORAGE_CODEHASH_C` example row, there is `C` storage root stored in `s_main.bytes`
and `C` codehash in `c_main.bytes`. Both these values are hash outputs.

The whole account leaf looks like:
[248,106,161,32,252,237,52,8,133,130,180,167,143,97,28,115,102,25,94,62,148,249,8,6,55,244,16,75,187,208,208,127,251,120,61,73,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
[248,106,161,32,252,237,52,8,133,130,180,167,143,97,28,115,102,25,94,62,148,249,8,6,55,244,16,75,187,208,208,127,251,120,61,73,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
[0,0,0,32,252,237,52,8,133,130,180,167,143,97,28,115,102,25,94,62,148,249,8,6,55,244,16,75,187,208,208,127,251,120,61,73,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
[184,70,128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,248,68,128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
[184,70,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,248,68,128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
[0,160,86,232,31,23,27,204,85,166,255,131,69,230,146,192,248,110,91,72,224,27,153,108,173,192,1,98,47,181,227,99,180,33,0,160,197,210,70,1,134,247,35,60,146,126,125,178,220,199,3,192,229,0,182,83,202,130,39,59,123,250,216,4,93,133,164,122]
[0,160,86,232,31,23,27,204,85,166,255,131,69,230,146,192,248,110,91,72,224,27,153,108,173,192,1,98,47,181,227,99,180,33,0,160,197,210,70,1,134,247,35,60,146,126,125,178,220,199,3,192,229,0,182,83,202,130,39,59,123,250,216,4,93,133,164,122]
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

Lookups:
The `is_codehash_mod` lookup is enabled in `ACCOUNT_LEAF_STORAGE_CODEHASH_C` row.
*/

#[derive(Clone, Debug, Default)]
pub(crate) struct AccountLeafStorageCodehashConfig<F> {
    _marker: PhantomData<F>,
}

impl<F: FieldExt> AccountLeafStorageCodehashConfig<F> {
    pub fn configure(
        meta: &mut VirtualCells<'_, F>,
        cb: &mut MPTConstraintBuilder<F>,
        ctx: MPTContext<F>,
        is_s: bool,
    ) -> Self {
        let proof_type = ctx.proof_type;
        let inter_root = ctx.inter_root(is_s);
        let position_cols = ctx.position_cols;
        let s_main = ctx.s_main;
        let c_main = ctx.c_main;
        let r = ctx.r;
        let accs = ctx.accumulators;
        let value_prev = ctx.value_prev;
        let value = ctx.value;
        let denoter = ctx.denoter;

        let rot_non_existing = -(if is_s {
            ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND
        } else {
            ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND
        } - ACCOUNT_NON_EXISTING_IND);
        let rot_nonce_balance = -2;
        let rot_key = -if is_s {
            ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND - ACCOUNT_LEAF_KEY_S_IND
        } else {
            ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND - ACCOUNT_LEAF_KEY_C_IND
        };
        let rot_branch_init = if is_s {
            -ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND
        } else {
            -ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND
        } - BRANCH_ROWS_NUM;
        let rot_last_child = rot_branch_init + (ARITY as i32);
        let rot_last_child_prev = rot_last_child - BRANCH_ROWS_NUM;

        // Note: We do not need to check `acc_mult` because it is not used after this
        // row. Note: differently as in storage leaf value (see empty_trie
        // there), the placeholder leaf never appears in the first level here,
        // because there is always at least a genesis account.
        circuit!([meta, cb.base], {
            ifx! {f!(position_cols.q_not_first), a!(ctx.account_leaf.is_storage_codehash(is_s)) => {
                // When non_existing_account_proof and not wrong leaf there is only a placeholder account leaf
                // and the constraints in this gate are not triggered. In that case it is checked
                // that there is nil in the parent branch at the proper position (see `account_non_existing.rs`), note
                // that we need (placeholder) account leaf for lookups and to know when to check that parent branch
                // has a nil.
                // Note: `(is_non_existing_account_proof.clone() - is_wrong_leaf.clone() - one.clone())`
                // cannot be 0 when `is_non_existing_account_proof = 0` (see `account_leaf_nonce_balance.rs`).
                let is_wrong_leaf = a!(s_main.rlp1, rot_non_existing);
                // TODO(Brecht): Can we remove this if by just making this pass in this special case?
                ifx! {not!(and::expr(&[a!(proof_type.is_non_existing_account_proof), not!(is_wrong_leaf)])) => {
                    // Storage root and codehash are always 32byte hashes, so rlp2 is `160 = 128 + 32`.
                    require!(a!(s_main.rlp2) => 160);
                    require!(a!(c_main.rlp2) => 160);
                }}

                // RLC calculation
                let storage_root = DataTransition::new(meta, accs.s_mod_node_rlc);
                let codehash = DataTransition::new(meta, accs.c_mod_node_rlc);
                let storage_root_rlc = rlc::expr(
                    &s_main.bytes.iter().map(|&byte| a!(byte)).collect::<Vec<_>>(),
                    &r,
                );
                require!(storage_root_rlc => storage_root);
                let codehash_rlc = rlc::expr(
                    &c_main.bytes.iter().map(|&byte| a!(byte)).collect::<Vec<_>>(),
                    &r,
                );
                require!(codehash_rlc => codehash);
                // Calculate the full account leaf RLC using the intermediate data in nonce/balance and adding the final data here.
                let acc_prev = a!(accs.acc_s.rlc, rot_nonce_balance);
                let acc_mult_prev = a!(accs.acc_s.mult, rot_nonce_balance);
                let rlc = acc_prev.expr() + rlc::expr(
                    &[
                        a!(s_main.rlp2),
                        storage_root_rlc.expr(),
                        a!(c_main.rlp2),
                        codehash_rlc.expr(),
                    ].map(|v| v * acc_mult_prev.expr()),
                    &accumulate_rand(&[r[0].expr(), r[31].expr(), r[0].expr()]),
                );
                require!(a!(accs.acc_s.rlc) => rlc);
                let rlc = a!(accs.acc_s.rlc);

                // Check if the account is in the branch above.
                let root = a!(inter_root);
                let account_len = a!(s_main.rlp2, rot_key) + 2.expr();
                let (do_lookup, hash_rlc) = ifx!{a!(position_cols.not_first_level) => {
                    let branch = BranchNodeInfo::new(meta, s_main, is_s, rot_branch_init);
                    ifx!{branch.is_placeholder() => {
                        ifx!{a!(position_cols.not_first_level, rot_last_child) => {
                            /* Hash of an account leaf when branch placeholder */
                            // When there is a placeholder branch above the account leaf (it means the account leaf
                            // drifted into newly added branch, this branch did not exist in `S` proof), the hash of the leaf
                            // needs to be checked to be at the proper position in the branch above the placeholder branch.
                            // Note: a placeholder leaf cannot appear when there is a branch placeholder
                            // (a placeholder leaf appears when there is no leaf at certain position, while branch placeholder
                            // appears when there is a leaf and it drifts down into a newly added branch).
                            (true.expr(), a!(accs.mod_node_rlc(is_s), rot_last_child_prev))
                        } elsex {
                            /* Hash of an account leaf compared to root when branch placeholder in the first level */
                            // When there is a placeholder branch above the account leaf (it means the account leaf
                            // drifted into newly added branch, this branch did not exist in `S` proof) in the first level,
                            // the hash of the leaf needs to be checked to be the state root.
                            (true.expr(), root.expr())
                        }}
                    } elsex {
                        /* Hash of an account leaf in a branch */
                        // Hash of an account leaf needs to appear (when not in first level) at the proper position in the
                        // parent branch.
                        // Note: the placeholder leaf appears when a new account is created (in this case there was
                        // no leaf before and we add a placeholder). There are no constraints for
                        // a placeholder leaf, it is added only to maintain the parallel layout.
                        // Rotate into any of the branch children rows:
                        let is_placeholder_leaf = a!(denoter.sel(is_s), rot_last_child);
                        ifx!{not!(is_placeholder_leaf) => {
                            (true.expr(), a!(accs.mod_node_rlc(is_s), rot_last_child))
                        }}
                    }}
                } elsex {
                    /* Account first level leaf without branch - compared to state root */
                    // Check hash of an account leaf to be state root when the leaf is without a branch (the leaf
                    // is in the first level).
                    (true.expr(), root.expr())
                }};
                // Do the lookup
                ifx!{do_lookup => {
                    require!((1, rlc, account_len, hash_rlc) => @"keccak");
                }}

                if !is_s {
                    // To enable lookup for codehash modification we need to have S codehash
                    // and C codehash in the same row.
                    // For this reason, S codehash RLC is copied to `value_prev` column in C row.
                    require!(a!(value_prev) => codehash.prev());
                    // To enable lookup for codehash modification we need to have S codehash
                    // and C codehash in the same row (`value_prev`, `value` columns).
                    // C codehash RLC is copied to `value` column in C row.
                    require!(a!(value) => codehash);
                    // Note: we do not check whether codehash is copied properly as only one of the
                    // `S` or `C` proofs are used for a lookup.
                    // TODO(Brecht): Is the note above true? This is done for nonce/balance

                    // Check that there is only one modification.
                    // Note: For `is_non_existing_account_proof` we do not need this constraint,
                    // `S` and `C` proofs are the same and we need to do a lookup into only one
                    // (the other one could really be whatever).
                    // TODO(Brecht): I think should be able to remove this if by changing the
                    // witness
                    ifx!{not!(a!(proof_type.is_account_delete_mod)) => {
                        // Storage root needs to remain the same when not modifying the storage root
                        ifx!{not!(a!(proof_type.is_storage_mod)) => {
                            require!(storage_root => storage_root.prev());
                        }}
                        // Codehash root needs to remain the same when not modifying the codehash
                        ifx!{not!(a!(proof_type.is_codehash_mod)) => {
                            require!(codehash => codehash.prev());
                        }}
                    }}
                }
            }}
        });

        AccountLeafStorageCodehashConfig {
            _marker: PhantomData,
        }
    }

    pub fn assign(
        &self,
        region: &mut Region<'_, F>,
        mpt_config: &MPTConfig<F>,
        pv: &mut ProofValues<F>,
        row: &MptWitnessRow<F>,
        offset: usize,
    ) {
        if row.get_type() == MptWitnessRowType::AccountLeafRootCodehashS {
            pv.acc_s = pv.acc_nonce_balance_s;
            pv.acc_mult_s = pv.acc_mult_nonce_balance_s;

            // storage root RLC and code hash RLC
            pv.rlc1 = F::zero();
            pv.rlc2 = F::zero();
            mpt_config
                .compute_rlc_and_assign(
                    region,
                    &row.bytes,
                    pv,
                    offset,
                    (S_START, HASH_WIDTH),
                    (C_START, HASH_WIDTH),
                )
                .ok();
        } else {
            pv.acc_s = pv.acc_nonce_balance_c;
            pv.acc_mult_s = pv.acc_mult_nonce_balance_c;

            // assign code hash S
            region
                .assign_advice(
                    || "assign value prev".to_string(),
                    mpt_config.value_prev,
                    offset,
                    || Value::known(pv.rlc2),
                )
                .ok();

            // assign storage root RLC and code hash RLC for this row
            pv.rlc1 = F::zero();
            pv.rlc2 = F::zero();
            mpt_config
                .compute_rlc_and_assign(
                    region,
                    &row.bytes,
                    pv,
                    offset,
                    (S_START, HASH_WIDTH),
                    (C_START, HASH_WIDTH),
                )
                .ok();

            // assign code hash C in value column
            region
                .assign_advice(
                    || "assign value".to_string(),
                    mpt_config.value,
                    offset,
                    || Value::known(pv.rlc2),
                )
                .ok();

            if row.get_byte_rev(IS_CODEHASH_MOD_POS) == 1 {
                region
                    .assign_advice(
                        || "assign lookup enabled".to_string(),
                        mpt_config.proof_type.proof_type,
                        offset,
                        || Value::known(F::from(3_u64)), // codehash mod lookup enabled in this row if it is is_codehash_mod proof
                    )
                    .ok();
            }
        }
        // storage
        mpt_config.compute_acc_and_mult(
            &row.bytes,
            &mut pv.acc_s,
            &mut pv.acc_mult_s,
            S_START - 1,
            HASH_WIDTH + 1,
        );
        // code hash
        mpt_config.compute_acc_and_mult(
            &row.bytes,
            &mut pv.acc_s,
            &mut pv.acc_mult_s,
            C_START - 1,
            HASH_WIDTH + 1,
        );
        mpt_config
            .assign_acc(
                region,
                pv.acc_s,
                pv.acc_mult_s,
                F::zero(),
                F::zero(),
                offset,
            )
            .ok();
    }
}
