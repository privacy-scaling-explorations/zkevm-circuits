use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, VirtualCells},
    poly::Rotation,
};
use std::marker::PhantomData;

use crate::{
    mpt_circuit::columns::{AccumulatorCols, DenoteCols, MainCols, PositionCols, ProofTypeCols},
    mpt_circuit::helpers::{range_lookups, get_is_inserted_extension_node},
    mpt_circuit::param::{
        ACCOUNT_LEAF_KEY_C_IND, ACCOUNT_LEAF_KEY_S_IND, ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND,
        ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND, ACCOUNT_NON_EXISTING_IND, BRANCH_ROWS_NUM, C_START,
        EXTENSION_ROWS_NUM, HASH_WIDTH, IS_BRANCH_C_PLACEHOLDER_POS, IS_BRANCH_S_PLACEHOLDER_POS,
        IS_CODEHASH_MOD_POS, RLP_NUM, S_START,
    },
    mpt_circuit::witness_row::{MptWitnessRow, MptWitnessRowType},
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
        randomness: Expression<F>,
        accs: AccumulatorCols<F>,
        value_prev: Column<Advice>,
        value: Column<Advice>,
        fixed_table: [Column<Fixed>; 3],
        denoter: DenoteCols<F>,
        keccak_table: KeccakTable,
        is_s: bool,
    ) -> Self {
        let config = AccountLeafStorageCodehashConfig {
            _marker: PhantomData,
        };
        let one = Expression::Constant(F::one());
        let mut rot_into_branch_init = -ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND - BRANCH_ROWS_NUM;
        if !is_s {
            rot_into_branch_init = -ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND - BRANCH_ROWS_NUM;
        }

        // Note: We do not need to check `acc_mult` because it is not used after this
        // row.

        /*
        Note: differently as in storage leaf value (see empty_trie there), the placeholder
        leaf never appears in the first level here, because there is always
        at least a genesis account.
        */
        meta.create_gate("Account leaf storage codehash", |meta| {
            let q_not_first = meta.query_fixed(position_cols.q_not_first, Rotation::cur());
            let q_enable =
                q_not_first * meta.query_advice(is_account_leaf_storage_codehash, Rotation::cur());

            let mut constraints = vec![];

            /*
            We have storage length in `s_rlp2` (which is 160 presenting `128 + 32`).
            We have storage hash in `s_main.bytes`.
            We have codehash length in `c_rlp2` (which is 160 presenting `128 + 32`).
            We have codehash in `c_main.bytes`.
            */

            let mut rot_into_non_existing =
                -(ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND - ACCOUNT_NON_EXISTING_IND);
            if !is_s {
                rot_into_non_existing =
                    -(ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND - ACCOUNT_NON_EXISTING_IND);
            }

            /*
            When non_existing_account_proof and not wrong leaf there is only a placeholder account leaf
            and the constraints in this gate are not triggered. In that case it is checked
            that there is nil in the parent branch at the proper position (see `account_non_existing.rs`), note
            that we need (placeholder) account leaf for lookups and to know when to check that parent branch
            has a nil.

            Note: `(is_non_existing_account_proof.clone() - is_wrong_leaf.clone() - one.clone())`
            cannot be 0 when `is_non_existing_account_proof = 0` (see `account_leaf_nonce_balance.rs`).
            */

            let is_wrong_leaf = meta.query_advice(s_main.rlp1, Rotation(rot_into_non_existing));
            let is_non_existing_account_proof =
                meta.query_advice(proof_type.is_non_existing_account_proof, Rotation::cur());

            let c160 = Expression::Constant(F::from(160));
            let rot = -2;
            let acc_prev = meta.query_advice(accs.acc_s.rlc, Rotation(rot));
            let acc_mult_prev = meta.query_advice(accs.acc_s.mult, Rotation(rot));
            let s_rlp2 = meta.query_advice(s_main.rlp2, Rotation::cur());
            let c_rlp2 = meta.query_advice(c_main.rlp2, Rotation::cur());

            /*
            `s_main.rlp2` stores the RLP length of the hash of storage root. The hash output length is 32
            and thus `s_main.rlp2` needs to be `160 = 128 + 32`.
            */
            constraints.push((
                "Account leaf storage codehash s_main.rlp2 = 160",
                q_enable.clone()
                    * (is_non_existing_account_proof.clone() - is_wrong_leaf.clone() - one.clone())
                    * (s_rlp2.clone() - c160.clone()),
            ));

            /*
            `c_main.rlp2` stores the RLP length of the codehash. The hash output length is 32
            and thus `c_main.rlp2` needs to be `160 = 128 + 32`.
            */
            constraints.push((
                "Account leaf storage codehash c_main.rlp2 = 160",
                q_enable.clone()
                    * (is_non_existing_account_proof - is_wrong_leaf - one.clone())
                    * (c_rlp2.clone() - c160),
            ));

            let mut expr = acc_prev + s_rlp2 * acc_mult_prev.clone();

            let mut storage_root_rlc = Expression::Constant(F::zero());
            let mut curr_r = one.clone();
            for col in s_main.bytes.iter() {
                let s = meta.query_advice(*col, Rotation::cur());
                storage_root_rlc = storage_root_rlc + s * curr_r.clone();
                curr_r = curr_r * randomness.clone();
            }
            let storage_root_stored = meta.query_advice(accs.s_mod_node_rlc, Rotation::cur());

            /*
            `s_main.bytes` contain storage root hash, but to simplify lookups we need to have
            the RLC of storage root hash stored in some column too. The RLC is stored in
            `s_mod_node_hash_rlc`. We need to ensure that this value corresponds to the RLC
            of `s_main.bytes`.
            */
            constraints.push((
                "Storage root RLC",
                q_enable.clone() * (storage_root_rlc.clone() - storage_root_stored.clone()),
            ));

            expr = expr + storage_root_rlc * acc_mult_prev.clone() * randomness.clone();

            curr_r = curr_r * acc_mult_prev * randomness.clone();

            expr = expr + c_rlp2 * curr_r.clone();
            let old_curr_r = curr_r * randomness.clone();

            curr_r = one.clone();
            let mut codehash_rlc = Expression::Constant(F::zero());
            for col in c_main.bytes.iter() {
                let c = meta.query_advice(*col, Rotation::cur());
                codehash_rlc = codehash_rlc + c * curr_r.clone();
                curr_r = curr_r * randomness.clone();
            }
            let codehash_stored = meta.query_advice(accs.c_mod_node_rlc, Rotation::cur());

            /*
            `c_main.bytes` contain codehash, but to simplify lookups we need to have
            the RLC of the codehash stored in some column too. The RLC is stored in
            `c_mod_node_hash_rlc`. We need to ensure that this value corresponds to the RLC
            of `c_main.bytes`.
            */
            constraints.push((
                "Codehash RLC",
                q_enable.clone() * (codehash_rlc.clone() - codehash_stored.clone()),
            ));

            if !is_s {
                let codehash_s_from_prev = meta.query_advice(accs.c_mod_node_rlc, Rotation::prev());
                let storage_root_s_from_prev =
                    meta.query_advice(accs.s_mod_node_rlc, Rotation::prev());
                let codehash_s_from_cur = meta.query_advice(value_prev, Rotation::cur());
                let codehash_c_in_value = meta.query_advice(value, Rotation::cur());

                /*
                To enable lookup for codehash modification we need to have S codehash
                and C codehash in the same row.
                For this reason, S codehash RLC is copied to `value_prev` column in C row.
                */
                constraints.push((
                    "S codehash RLC is correctly copied to C row",
                    q_enable.clone() * (codehash_s_from_prev - codehash_s_from_cur.clone()),
                ));

                /*
                To enable lookup for codehash modification we need to have S codehash
                and C codehash in the same row (`value_prev`, `value` columns).
                C codehash RLC is copied to `value` column in C row.
                */
                constraints.push((
                    "C codehash RLC is correctly copied to value row",
                    q_enable.clone() * (codehash_stored.clone() - codehash_c_in_value),
                ));

                // Note: we do not check whether codehash is copied properly as only one of the
                // `S` or `C` proofs are used for a lookup.

                // Check there is only one modification at once:
                let is_storage_mod = meta.query_advice(proof_type.is_storage_mod, Rotation::cur());
                let is_nonce_mod = meta.query_advice(proof_type.is_nonce_mod, Rotation::cur());
                let is_balance_mod = meta.query_advice(proof_type.is_balance_mod, Rotation::cur());
                let is_codehash_mod =
                    meta.query_advice(proof_type.is_codehash_mod, Rotation::cur());
                let is_account_delete_mod =
                    meta.query_advice(proof_type.is_account_delete_mod, Rotation::cur());

                /*
                If the modification is nonce or balance modification, the storage root needs to
                stay the same.

                Note: For `is_non_existing_account_proof` we do not need this constraint,
                `S` and `C` proofs are the same and we need to do a lookup into only one
                (the other one could really be whatever).
                */
                constraints.push((
                    "If nonce or balance or codehash modification: storage_root_s = storage_root_c",
                    q_enable.clone()
                        * (is_nonce_mod.clone() + is_balance_mod.clone() + is_codehash_mod)
                        * (one.clone() - is_account_delete_mod.clone())
                        * (storage_root_s_from_prev - storage_root_stored),
                ));

                /*
                If the modification is nonce or balance or storage modification (that means
                always except for `is_account_delete_mod` and `is_non_existing_account_proof`),
                the storage root needs to stay the same.

                Note: For `is_non_existing_account_proof` we do not need this constraint,
                `S` and `C` proofs are the same and we need to do a lookup into only one
                (the other one could really be whatever).
                */
                constraints.push((
                    "If nonce or balance or storage modification: codehash_s = codehash_c",
                    q_enable.clone()
                        * (is_nonce_mod + is_balance_mod + is_storage_mod)
                        * (one.clone() - is_account_delete_mod)
                        * (codehash_s_from_cur - codehash_stored),
                ));
            }

            expr = expr + codehash_rlc * old_curr_r;

            let acc = meta.query_advice(accs.acc_s.rlc, Rotation::cur());

            /*
            The RLC of the account leaf needs to be properly computed. We take the intermediate RLC
            computed in the `ACCOUNT_LEAF_NONCE_BALANCE_*` row and add the bytes from the current row.
            The computed RLC needs to be the same as the stored value in `acc_s` row.
            */
            constraints.push(("Account leaf storage codehash RLC", q_enable * (expr - acc)));

            constraints
        });

        /*
        Check hash of an account leaf to be state root when the leaf is without a branch (the leaf
        is in the first level).

        Note: the constraints for the first level branch to be compared to the state root
        are in `branch_hash_in_parent`.
        */
        meta.lookup_any(
            "Account first level leaf without branch - compared to state root",
            |meta| {
                let q_not_first = meta.query_fixed(position_cols.q_not_first, Rotation::cur());
                let not_first_level =
                    meta.query_advice(position_cols.not_first_level, Rotation::cur());

                let is_account_leaf_storage_codehash =
                    meta.query_advice(is_account_leaf_storage_codehash, Rotation::cur());

                let rlc = meta.query_advice(accs.acc_s.rlc, Rotation::cur());
                let root = meta.query_advice(inter_root, Rotation::cur());

                let selector = q_not_first
                    * is_account_leaf_storage_codehash
                    * (one.clone() - not_first_level);

                let mut table_map = Vec::new();
                let keccak_is_enabled = meta.query_advice(keccak_table.is_enabled, Rotation::cur());
                table_map.push((selector.clone(), keccak_is_enabled));

                let keccak_input_rlc = meta.query_advice(keccak_table.input_rlc, Rotation::cur());
                table_map.push((selector.clone() * rlc, keccak_input_rlc));

                let mut account_len = meta.query_advice(
                    s_main.rlp2,
                    Rotation(-(ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND - ACCOUNT_LEAF_KEY_S_IND)),
                ) + one.clone()
                    + one.clone();
                if !is_s {
                    account_len = meta.query_advice(
                        s_main.rlp2,
                        Rotation(-(ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND - ACCOUNT_LEAF_KEY_C_IND)),
                    ) + one.clone()
                        + one.clone();
                }
                let keccak_input_len = meta.query_advice(keccak_table.input_len, Rotation::cur());
                table_map.push((selector.clone() * account_len, keccak_input_len));

                let keccak_output_rlc = meta.query_advice(keccak_table.output_rlc, Rotation::cur());
                table_map.push((selector * root, keccak_output_rlc));

                table_map
            },
        );

        /*
        Hash of an account leaf needs to appear (when not in first level) at the proper position in the
        parent branch.

        Note: the placeholder leaf appears when a new account is created (in this case there was
        no leaf before and we add a placeholder). There are no constraints for
        a placeholder leaf, it is added only to maintain the parallel layout.
        */
        meta.lookup_any("Hash of an account leaf in a branch", |meta| {
            let not_first_level = meta.query_advice(position_cols.not_first_level, Rotation::cur());

            let is_account_leaf_storage_codehash =
                meta.query_advice(is_account_leaf_storage_codehash, Rotation::cur());

            // Rotate into any of the brach children rows:
            let mut is_placeholder_leaf = meta.query_advice(
                denoter.sel1,
                Rotation(-ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND - EXTENSION_ROWS_NUM - 1),
            );
            if !is_s {
                is_placeholder_leaf = meta.query_advice(
                    denoter.sel2,
                    Rotation(-ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND - EXTENSION_ROWS_NUM - 1),
                );
            }

            // Rotate into branch init:
            let mut is_branch_placeholder = meta.query_advice(
                s_main.bytes[IS_BRANCH_S_PLACEHOLDER_POS - RLP_NUM],
                Rotation(rot_into_branch_init),
            );
            if !is_s {
                is_branch_placeholder = meta.query_advice(
                    s_main.bytes[IS_BRANCH_C_PLACEHOLDER_POS - RLP_NUM],
                    Rotation(rot_into_branch_init),
                );
            }

            // Note: accumulated in s (not in c) for c:
            let acc_s = meta.query_advice(accs.acc_s.rlc, Rotation::cur());
            // Any rotation that lands into branch can be used instead of -17.
            let mut mod_node_hash_rlc_cur = meta.query_advice(accs.s_mod_node_rlc, Rotation(-17));
            if !is_s {
                mod_node_hash_rlc_cur = meta.query_advice(accs.c_mod_node_rlc, Rotation(-17));
            }

            let selector = not_first_level
                * (one.clone() - is_branch_placeholder)
                * (one.clone() - is_placeholder_leaf)
                * is_account_leaf_storage_codehash;

            let mut table_map = Vec::new();
            let keccak_is_enabled = meta.query_advice(keccak_table.is_enabled, Rotation::cur());
            table_map.push((selector.clone(), keccak_is_enabled));

            let keccak_input_rlc = meta.query_advice(keccak_table.input_rlc, Rotation::cur());
            table_map.push((selector.clone() * acc_s, keccak_input_rlc));

            let mut account_len = meta.query_advice(
                s_main.rlp2,
                Rotation(-(ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND - ACCOUNT_LEAF_KEY_S_IND)),
            ) + one.clone()
                + one.clone();
            if !is_s {
                account_len = meta.query_advice(
                    s_main.rlp2,
                    Rotation(-(ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND - ACCOUNT_LEAF_KEY_C_IND)),
                ) + one.clone()
                    + one.clone();
            }

            let keccak_input_len = meta.query_advice(keccak_table.input_len, Rotation::cur());
            table_map.push((selector.clone() * account_len, keccak_input_len));

            let keccak_output_rlc = meta.query_advice(keccak_table.output_rlc, Rotation::cur());
            table_map.push((selector * mod_node_hash_rlc_cur, keccak_output_rlc));

            table_map
        });

        /*
        When there is a placeholder branch above the account leaf (it means the account leaf
        drifted into newly added branch, this branch did not exist in `S` proof), the hash of the leaf
        needs to be checked to be at the proper position in the branch above the placeholder branch.

        Note: a placeholder leaf cannot appear when there is a branch placeholder
        (a placeholder leaf appears when there is no leaf at certain position, while branch placeholder
        appears when there is a leaf and it drifts down into a newly added branch).
        */
        meta.lookup_any("Hash of an account leaf when branch placeholder", |meta| {
            let account_not_first_level =
                meta.query_advice(position_cols.not_first_level, Rotation::cur());
            // Any rotation that lands into branch can be used instead of -17.
            let branch_placeholder_not_in_first_level =
                meta.query_advice(position_cols.not_first_level, Rotation(-17));

            let is_account_leaf_storage_codehash =
                meta.query_advice(is_account_leaf_storage_codehash, Rotation::cur());

            // Rotate into branch init:
            let mut is_branch_placeholder = meta.query_advice(
                s_main.bytes[IS_BRANCH_S_PLACEHOLDER_POS - RLP_NUM],
                Rotation(rot_into_branch_init),
            );
            if !is_s {
                is_branch_placeholder = meta.query_advice(
                    s_main.bytes[IS_BRANCH_C_PLACEHOLDER_POS - RLP_NUM],
                    Rotation(rot_into_branch_init),
                );
            }
    
            /*
            When extension node is inserted, the leaf is only a placeholder (as well as branch) -
            the constraints for this case are in `extension_node_inserted.rs`.
            */
            let is_inserted_ext_node = get_is_inserted_extension_node(
                meta, c_main.rlp1, c_main.rlp2, rot_into_branch_init, is_s);

            let selector = account_not_first_level
                * branch_placeholder_not_in_first_level
                * is_branch_placeholder
                * (one.clone() - is_inserted_ext_node)
                * is_account_leaf_storage_codehash;

            // Note: accumulated in s (not in c) for c:
            let acc_s = meta.query_advice(accs.acc_s.rlc, Rotation::cur());

            // Any rotation that lands into branch can be used instead of -17.
            let mut mod_node_hash_rlc_cur_prev =
                meta.query_advice(accs.s_mod_node_rlc, Rotation(-17 - BRANCH_ROWS_NUM));
            if !is_s {
                mod_node_hash_rlc_cur_prev =
                    meta.query_advice(accs.c_mod_node_rlc, Rotation(-17 - BRANCH_ROWS_NUM));
            }

            let mut table_map = Vec::new();
            let keccak_is_enabled = meta.query_advice(keccak_table.is_enabled, Rotation::cur());
            table_map.push((selector.clone(), keccak_is_enabled));

            let keccak_input_rlc = meta.query_advice(keccak_table.input_rlc, Rotation::cur());
            table_map.push((selector.clone() * acc_s, keccak_input_rlc));

            let mut account_len = meta.query_advice(
                s_main.rlp2,
                Rotation(-(ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND - ACCOUNT_LEAF_KEY_S_IND)),
            ) + one.clone()
                + one.clone();
            if !is_s {
                account_len = meta.query_advice(
                    s_main.rlp2,
                    Rotation(-(ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND - ACCOUNT_LEAF_KEY_C_IND)),
                ) + one.clone()
                    + one.clone();
            }

            let keccak_input_len = meta.query_advice(keccak_table.input_len, Rotation::cur());
            table_map.push((selector.clone() * account_len, keccak_input_len));

            let keccak_output_rlc = meta.query_advice(keccak_table.output_rlc, Rotation::cur());
            table_map.push((selector * mod_node_hash_rlc_cur_prev, keccak_output_rlc));

            table_map
        });

        /*
        When there is a placeholder branch above the account leaf (it means the account leaf
        drifted into newly added branch, this branch did not exist in `S` proof) in the first level,
        the hash of the leaf needs to be checked to be the state root.
        */
        meta.lookup_any(
            "Hash of an account leaf compared to root when branch placeholder in the first level",
            |meta| {
                let account_not_first_level =
                    meta.query_advice(position_cols.not_first_level, Rotation::cur());
                // Any rotation that lands into branch can be used instead of -17.
                let branch_placeholder_in_first_level =
                    one.clone() - meta.query_advice(position_cols.not_first_level, Rotation(-17));

                let is_account_leaf_storage_codehash =
                    meta.query_advice(is_account_leaf_storage_codehash, Rotation::cur());

                // Rotate into branch init:
                let mut is_branch_placeholder = meta.query_advice(
                    s_main.bytes[IS_BRANCH_S_PLACEHOLDER_POS - RLP_NUM],
                    Rotation(rot_into_branch_init),
                );
                if !is_s {
                    is_branch_placeholder = meta.query_advice(
                        s_main.bytes[IS_BRANCH_C_PLACEHOLDER_POS - RLP_NUM],
                        Rotation(rot_into_branch_init),
                    );
                }
                
                /*
                When extension node is inserted, the leaf is only a placeholder (as well as branch) -
                the constraints for this case are in `extension_node_inserted.rs`.
                */
                let is_inserted_ext_node = get_is_inserted_extension_node(
                    meta, c_main.rlp1, c_main.rlp2, rot_into_branch_init, is_s);

                let selector = account_not_first_level
                    * branch_placeholder_in_first_level
                    * is_branch_placeholder
                    * (one.clone() - is_inserted_ext_node)
                    * is_account_leaf_storage_codehash;

                // Note: accumulated in s (not in c) for c:
                let acc_s = meta.query_advice(accs.acc_s.rlc, Rotation::cur());

                let root = meta.query_advice(inter_root, Rotation::cur());

                let mut table_map = Vec::new();
                let keccak_is_enabled = meta.query_advice(keccak_table.is_enabled, Rotation::cur());
                table_map.push((selector.clone(), keccak_is_enabled));

                let keccak_input_rlc = meta.query_advice(keccak_table.input_rlc, Rotation::cur());
                table_map.push((selector.clone() * acc_s, keccak_input_rlc));

                let mut account_len = meta.query_advice(
                    s_main.rlp2,
                    Rotation(-(ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND - ACCOUNT_LEAF_KEY_S_IND)),
                ) + one.clone()
                    + one.clone();
                if !is_s {
                    account_len = meta.query_advice(
                        s_main.rlp2,
                        Rotation(-(ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND - ACCOUNT_LEAF_KEY_C_IND)),
                    ) + one.clone()
                        + one.clone();
                }

                let keccak_input_len = meta.query_advice(keccak_table.input_len, Rotation::cur());
                table_map.push((selector.clone() * account_len, keccak_input_len));

                let keccak_output_rlc = meta.query_advice(keccak_table.output_rlc, Rotation::cur());
                table_map.push((selector * root, keccak_output_rlc));

                table_map
            },
        );

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

        config
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
