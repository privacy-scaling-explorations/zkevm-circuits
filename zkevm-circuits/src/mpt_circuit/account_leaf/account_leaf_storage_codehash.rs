use gadgets::util::{and, not, Expr};
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, VirtualCells},
    poly::Rotation,
};
use std::marker::PhantomData;

use crate::{
    constraints,
    evm_circuit::util::rlc,
    mpt_circuit::columns::{AccumulatorCols, DenoteCols, MainCols, PositionCols, ProofTypeCols},
    mpt_circuit::helpers::range_lookups,
    mpt_circuit::{
        helpers::BaseConstraintBuilder,
        witness_row::{MptWitnessRow, MptWitnessRowType},
    },
    mpt_circuit::{
        helpers::{accumulate_rand, generate_keccak_lookups},
        param::{
            ACCOUNT_LEAF_KEY_C_IND, ACCOUNT_LEAF_KEY_S_IND, ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND,
            ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND, ACCOUNT_NON_EXISTING_IND, BRANCH_ROWS_NUM,
            C_START, EXTENSION_ROWS_NUM, HASH_WIDTH, IS_BRANCH_C_PLACEHOLDER_POS,
            IS_BRANCH_S_PLACEHOLDER_POS, IS_CODEHASH_MOD_POS, RLP_NUM, S_START,
        },
    },
    mpt_circuit::{FixedTableTag, MPTConfig, ProofValues},
    table::KeccakTable,
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

#[derive(Clone, Debug)]
pub(crate) struct AccountLeafStorageCodehashConfig<F> {
    _marker: PhantomData<F>,
}

impl<F: FieldExt> AccountLeafStorageCodehashConfig<F> {
    #[allow(clippy::too_many_arguments)]
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        proof_type: ProofTypeCols<F>,
        inter_root: Column<Advice>,
        position_cols: PositionCols<F>,
        is_account_leaf_storage_codehash: Column<Advice>,
        s_main: MainCols<F>,
        c_main: MainCols<F>,
        r: [Expression<F>; HASH_WIDTH],
        accs: AccumulatorCols<F>,
        value_prev: Column<Advice>,
        value: Column<Advice>,
        fixed_table: [Column<Fixed>; 3],
        denoter: DenoteCols<F>,
        keccak_table: KeccakTable,
        is_s: bool,
    ) -> Self {
        // Note: We do not need to check `acc_mult` because it is not used after this
        // row.
        // Note: differently as in storage leaf value (see empty_trie there), the
        // placeholder leaf never appears in the first level here, because there
        // is always at least a genesis account.
        let mut cb = BaseConstraintBuilder::default();
        meta.create_gate("Account leaf storage codehash", |meta| {
        constraints!{[meta, cb], {
            let q_not_first = f!(position_cols.q_not_first);
            let q_enable = q_not_first * a!(is_account_leaf_storage_codehash);

            // We have storage length in `s_rlp2` (which is 160 presenting `128 + 32`).
            // We have storage hash in `s_main.bytes`.
            // We have codehash length in `c_rlp2` (which is 160 presenting `128 + 32`).
            // We have codehash in `c_main.bytes`.

            let rot_into_non_existing = -(if is_s {ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND} else {ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND} - ACCOUNT_NON_EXISTING_IND);

            // When non_existing_account_proof and not wrong leaf there is only a placeholder account leaf
            // and the constraints in this gate are not triggered. In that case it is checked
            // that there is nil in the parent branch at the proper position (see `account_non_existing.rs`), note
            // that we need (placeholder) account leaf for lookups and to know when to check that parent branch
            // has a nil.
            // Note: `(is_non_existing_account_proof.clone() - is_wrong_leaf.clone() - one.clone())`
            // cannot be 0 when `is_non_existing_account_proof = 0` (see `account_leaf_nonce_balance.rs`).

            let is_wrong_leaf = a!(s_main.rlp1, rot_into_non_existing);
            let is_non_existing_account_proof = a!(proof_type.is_non_existing_account_proof);

            let rot = -2;
            let acc_prev = a!(accs.acc_s.rlc, rot);
            let acc_mult_prev = a!(accs.acc_s.mult, rot);
            let s_rlp2 = a!(s_main.rlp2);
            let c_rlp2 = a!(c_main.rlp2);

            ifx!{q_enable => {
                ifx!{is_non_existing_account_proof.expr() - is_wrong_leaf.expr() - 1.expr() => {
                    // `s_main.rlp2` stores the RLP length of the hash of storage root. The hash output length is 32
                    // and thus `s_main.rlp2` needs to be `160 = 128 + 32`.
                    require!(s_rlp2 => 160);

                    // `c_main.rlp2` stores the RLP length of the codehash. The hash output length is 32
                    // and thus `c_main.rlp2` needs to be `160 = 128 + 32`.
                    require!(c_rlp2 => 160);
                }}

                // `s_main.bytes` contain storage root hash, but to simplify lookups we need to have
                // the RLC of storage root hash stored in some column too. The RLC is stored in
                // `s_mod_node_hash_rlc`. We need to ensure that this value corresponds to the RLC
                // of `s_main.bytes`.
                let storage_root_rlc = rlc::expr(
                    &s_main.bytes.iter().map(|&byte| a!(byte)).collect::<Vec<_>>(),
                    &r,
                );
                let storage_root_stored = a!(accs.s_mod_node_rlc);
                require!(storage_root_rlc => storage_root_stored);

                // `c_main.bytes` contain codehash, but to simplify lookups we need to have
                // the RLC of the codehash stored in some column too. The RLC is stored in
                // `c_mod_node_hash_rlc`. We need to ensure that this value corresponds to the RLC
                // of `c_main.bytes`.
                let codehash_rlc = rlc::expr(
                    &c_main.bytes.iter().map(|&byte| a!(byte)).collect::<Vec<_>>(),
                    &r,
                );
                let codehash_stored = a!(accs.c_mod_node_rlc);
                require!(codehash_rlc => codehash_stored);

                if !is_s {
                    let codehash_s_from_prev = a!(accs.c_mod_node_rlc, -1);
                    let storage_root_s_from_prev = a!(accs.s_mod_node_rlc, -1);
                    let codehash_s_from_cur = a!(value_prev);
                    let codehash_c_in_value = a!(value);

                    // To enable lookup for codehash modification we need to have S codehash
                    // and C codehash in the same row.
                    // For this reason, S codehash RLC is copied to `value_prev` column in C row.
                    require!(codehash_s_from_prev => codehash_s_from_cur);

                    // To enable lookup for codehash modification we need to have S codehash
                    // and C codehash in the same row (`value_prev`, `value` columns).
                    // C codehash RLC is copied to `value` column in C row.
                    require!(codehash_stored => codehash_c_in_value);

                    // Note: we do not check whether codehash is copied properly as only one of the
                    // `S` or `C` proofs are used for a lookup.

                    // Check there is only one modification at once:
                    let is_storage_mod = a!(proof_type.is_storage_mod);
                    let is_nonce_mod = a!(proof_type.is_nonce_mod);
                    let is_balance_mod = a!(proof_type.is_balance_mod);
                    let is_codehash_mod = a!(proof_type.is_codehash_mod);
                    let is_account_delete_mod = a!(proof_type.is_account_delete_mod);

                    ifx!{not::expr(is_account_delete_mod.expr()) => {
                        // If the modification is nonce or balance modification, the storage root needs to
                        // stay the same.
                        // Note: For `is_non_existing_account_proof` we do not need this constraint,
                        // `S` and `C` proofs are the same and we need to do a lookup into only one
                        // (the other one could really be whatever).
                        ifx!{is_nonce_mod.expr() + is_balance_mod.expr() + is_codehash_mod => {
                            require!(storage_root_s_from_prev => storage_root_stored);
                        }}

                        // If the modification is nonce or balance or storage modification (that means
                        // always except for `is_account_delete_mod` and `is_non_existing_account_proof`),
                        // the storage root needs to stay the same.
                        // Note: For `is_non_existing_account_proof` we do not need this constraint,
                        // `S` and `C` proofs are the same and we need to do a lookup into only one
                        // (the other one could really be whatever).
                        ifx!{is_nonce_mod.expr() + is_balance_mod.expr() + is_storage_mod => {
                            require!(codehash_s_from_cur => codehash_stored);
                        }}
                    }}
                }

                // The RLC of the account leaf needs to be properly computed. We take the intermediate RLC
                // computed in the `ACCOUNT_LEAF_NONCE_BALANCE_*` row and add the bytes from the current row.
                // The computed RLC needs to be the same as the stored value in `acc_s` row.
                let rlc = acc_prev.expr() + rlc::expr(
                    &[
                        s_rlp2.expr(),
                        storage_root_rlc.expr(),
                        c_rlp2.expr(),
                        codehash_rlc.expr(),
                    ].map(|v| v * acc_mult_prev.expr()),
                    &accumulate_rand(&[r[0].expr(), r[31].expr(), r[0].expr()]),
                );
                require!(a!(accs.acc_s.rlc) => rlc);
            }}

            ifx!{a!(is_account_leaf_storage_codehash) => {
                let rlc = a!(accs.acc_s.rlc);
                let root = a!(inter_root);
                let rot = -if is_s {ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND - ACCOUNT_LEAF_KEY_S_IND} else {ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND - ACCOUNT_LEAF_KEY_C_IND};
                let account_len = a!(s_main.rlp2, rot) + 2.expr();

                ifx!{a!(position_cols.not_first_level) => {
                    // Rotate into branch init:
                    let is_branch_placeholder = if is_s {
                        a!(s_main.bytes[IS_BRANCH_S_PLACEHOLDER_POS - RLP_NUM], -ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND - BRANCH_ROWS_NUM)
                    } else {
                        a!(s_main.bytes[IS_BRANCH_C_PLACEHOLDER_POS - RLP_NUM], -ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND - BRANCH_ROWS_NUM)
                    };
                    ifx!{is_branch_placeholder => {
                        // When branch_placeholder_not_in_first_level
                        ifx!{a!(position_cols.not_first_level, -17) => {
                            /* Hash of an account leaf when branch placeholder */
                            // When there is a placeholder branch above the account leaf (it means the account leaf
                            // drifted into newly added branch, this branch did not exist in `S` proof), the hash of the leaf
                            // needs to be checked to be at the proper position in the branch above the placeholder branch.
                            // Note: a placeholder leaf cannot appear when there is a branch placeholder
                            // (a placeholder leaf appears when there is no leaf at certain position, while branch placeholder
                            // appears when there is a leaf and it drifts down into a newly added branch).
                            // Any rotation that lands into branch can be used instead of -17.
                            let mod_node_hash_rlc_cur_prev = a!(if is_s {accs.s_mod_node_rlc} else {accs.c_mod_node_rlc}, -17 - BRANCH_ROWS_NUM);
                            // Note about rlc: accumulated in s (not in c) for c:
                            require!((rlc, account_len, mod_node_hash_rlc_cur_prev) => @keccak);
                        } elsex {
                            /* Hash of an account leaf compared to root when branch placeholder in the first level */
                            // When there is a placeholder branch above the account leaf (it means the account leaf
                            // drifted into newly added branch, this branch did not exist in `S` proof) in the first level,
                            // the hash of the leaf needs to be checked to be the state root.
                            // Any rotation that lands into branch can be used instead of -17.
                            // Note about rlc: accumulated in s (not in c) for c:
                            require!((rlc, account_len, root) => @keccak);
                        }}
                    } elsex {
                        /* Hash of an account leaf in a branch */
                        // Hash of an account leaf needs to appear (when not in first level) at the proper position in the
                        // parent branch.
                        // Note: the placeholder leaf appears when a new account is created (in this case there was
                        // no leaf before and we add a placeholder). There are no constraints for
                        // a placeholder leaf, it is added only to maintain the parallel layout.
                        // Rotate into any of the brach children rows:
                        let is_placeholder_leaf = if is_s {
                            a!(denoter.sel1, -ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND - EXTENSION_ROWS_NUM - 1)
                        } else {
                            a!(denoter.sel2, -ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND - EXTENSION_ROWS_NUM - 1)
                        };
                        ifx!{not::expr(is_placeholder_leaf.expr()) => {
                            // Any rotation that lands into branch can be used instead of -17.
                            let mod_node_hash_rlc_cur = a!(if is_s {accs.s_mod_node_rlc} else {accs.c_mod_node_rlc}, -17);
                            // Note about rlc: accumulated in s (not in c) for c:
                            require!((rlc, account_len, mod_node_hash_rlc_cur) => @keccak);
                        }}
                    }}
                } elsex {
                    /* Account first level leaf without branch - compared to state root */
                    // Check hash of an account leaf to be state root when the leaf is without a branch (the leaf
                    // is in the first level).
                    // Note: the constraints for the first level branch to be compared to the state root
                    // are in `branch_hash_in_parent`.
                    ifx!{f!(position_cols.q_not_first) => {
                        require!((rlc, account_len, root) => @keccak);
                    }}
                }}
            }}
            }}

            cb.gate(1.expr())
        });

        let sel = |meta: &mut VirtualCells<F>| {
            let q_not_first = meta.query_fixed(position_cols.q_not_first, Rotation::cur());
            q_not_first * meta.query_advice(is_account_leaf_storage_codehash, Rotation::cur())
        };

        /*
        Range lookups ensure that `s_main` and `c_main` columns are all bytes (between 0 - 255).

        Note: `s_main.rlp1` and `c_main.rlp1` are not used.
         */
        range_lookups(
            meta,
            sel,
            s_main.bytes.to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );
        range_lookups(
            meta,
            sel,
            c_main.bytes.to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );
        range_lookups(
            meta,
            sel,
            [s_main.rlp2, c_main.rlp2].to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );

        generate_keccak_lookups(meta, keccak_table, cb.keccak_lookups);

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
