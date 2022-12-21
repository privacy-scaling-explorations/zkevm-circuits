use gadgets::util::{and, not, select, Expr};
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, VirtualCells},
    poly::Rotation,
};
use itertools::Itertools;
use std::marker::PhantomData;

use crate::{
    constraints,
    evm_circuit::util::rlc,
    mpt_circuit::columns::{AccumulatorCols, DenoteCols, MainCols, ProofTypeCols},
    mpt_circuit::helpers::{compute_rlc, get_bool_constraint, mult_diff_lookup, range_lookups},
    mpt_circuit::witness_row::{MptWitnessRow, MptWitnessRowType},
    mpt_circuit::{
        helpers::key_len_lookup,
        param::{IS_BALANCE_MOD_POS, IS_NONCE_MOD_POS},
        FixedTableTag, MPTConfig, ProofValues,
    },
    mpt_circuit::{
        helpers::BaseConstraintBuilder,
        param::{
            ACCOUNT_LEAF_KEY_C_IND, ACCOUNT_LEAF_KEY_S_IND, ACCOUNT_LEAF_NONCE_BALANCE_C_IND,
            ACCOUNT_LEAF_NONCE_BALANCE_S_IND, ACCOUNT_NON_EXISTING_IND, C_START, HASH_WIDTH,
            S_START,
        },
    },
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

The constraints in this file apply to ACCOUNT_LEAF_NONCE_BALANCE_S and
ACCOUNT_LEAF_NONCE_BALANCE_C rows.

For example, the two rows might be:
[184,70,128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,248,68,128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
[184,70,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,248,68,128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

Here, in `ACCOUNT_LEAF_NONCE_BALANCE_S` example row, there is `S` nonce stored in `s_main` and `S` balance
in `c_main`. We can see nonce in `S` proof is `0 = 128 - 128`.

In `ACCOUNT_LEAF_NONCE_BALANCE_C` example row, there is `C` nonce stored in `s_main` and `C` balance in
`c_main`. We can see nonce in `C` proof is `1`.

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
We have nonce and balance in the same row - to enable lookups into the same columns (`value_prev`, `value`),
we enable nonce lookup in `ACCOUNT_LEAF_NONCE_BALANCE_S` row and balance lookup in `ACCOUNT_LEAF_NONCE_BALANCE_C` row.
This means we copy nonce C RLC to `ACCOUNT_LEAF_NONCE_BALANCE_S` row,
and balance S RLC to `ACCOUNT_LEAF_NONCE_BALANCE_C` row.
Constraints are added to ensure everything is properly copied.
*/
#[derive(Clone, Debug)]
pub(crate) struct AccountLeafNonceBalanceConfig<F> {
    _marker: PhantomData<F>,
}

impl<F: FieldExt> AccountLeafNonceBalanceConfig<F> {
    #[allow(clippy::too_many_arguments)]
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        proof_type: ProofTypeCols<F>,
        q_enable: impl Fn(&mut VirtualCells<'_, F>) -> Expression<F> + Copy,
        s_main: MainCols<F>,
        c_main: MainCols<F>,
        accs: AccumulatorCols<F>, /* accs.acc_c.rlc contains mult_diff_nonce; accs.key.mult for
                                   * mult_diff_balance */
        value_prev: Column<Advice>,
        value: Column<Advice>,
        r: [Expression<F>; HASH_WIDTH],
        denoter: DenoteCols<F>,
        fixed_table: [Column<Fixed>; 3],
        is_s: bool,
        check_zeros: bool,
    ) -> Self {
        let mut cb = BaseConstraintBuilder::default();
        meta.create_gate("Account leaf nonce balance RLC & RLP", |meta| {
        constraints!{[meta, cb], {
            let q_enable = q_enable(meta);

            // [248,112,157,59,158,160,175,159,65,212,107,23,98,208,38,205,150,63,244,2,185,236,246,95,240,224,191,229,27,102,202,231,184,80
            // There are 112 bytes after the first two bytes.
            // 157 means the key is 29 (157 - 128) bytes long.

            // Nonce, balance, storage, codehash are string in RLP: s_rlp1 and s_rlp2
            // contains the length of this string, for example 184 80 means the second
            // part is of length 1 (183 + 1 = 184) and there are 80 bytes in this string.
            // Then there is a list rlp meta data 248 78 where (this is stored in c_rlp1 and
            // c_rlp2) 78 = 3 (nonce) + 9 (balance) + 33 (storage) + 33
            // (codehash). We have nonce in s_main.bytes and balance in c_main.bytes.
            // s_rlp1  s_rlp2  c_rlp1  c_rlp2  s_main.bytes  c_main.bytes
            // 184     80      248     78      nonce      balance

            let rot = if is_s {-(ACCOUNT_LEAF_NONCE_BALANCE_S_IND - ACCOUNT_LEAF_KEY_S_IND)} else {-(ACCOUNT_LEAF_NONCE_BALANCE_C_IND - ACCOUNT_LEAF_KEY_C_IND)};
            let rot_into_non_existing = if is_s {-(ACCOUNT_LEAF_NONCE_BALANCE_S_IND - ACCOUNT_NON_EXISTING_IND)} else {-(ACCOUNT_LEAF_NONCE_BALANCE_C_IND - ACCOUNT_NON_EXISTING_IND)};

            let acc_prev = a!(accs.acc_s.rlc, rot);
            let acc_mult_prev = a!(accs.acc_s.mult, rot);
            let is_nonce_long = a!(denoter.sel1, rot);
            let is_balance_long = a!(denoter.sel2, rot);

            let acc_mult_after_nonce = a!(accs.acc_c.mult);
            let mult_diff_nonce = a!(accs.acc_c.rlc);
            let mult_diff_balance = a!(accs.key.mult);

            ifx!{q_enable => {
                // If nonce (same holds for balance) is smaller or equal to 128, then it will occupy only one byte:
                // `s_main.bytes[0]` (`c_main.bytes[0]` for balance).
                // For example, the row [184,70,128,0,...,0] holds 128 in bytes[0] which means nonce = 128 - 128 = 0.
                // For example, the row [184,70,1,0,...,0] holds 1 in bytes[0] which means nonce = 1.

                // In case nonce (same for balance) is bigger than 128, it will occupy more than 1 byte.
                // The example row below shows nonce value 142, while 129 means there is a nonce of byte
                // length `1 = 129 - 128`.
                // Balance in the example row below is: 28 + 5 * 256 + 107 * 256^2 + ... + 59 * 256^6, while
                // 135 means there are 7 = 135 - 128 bytes.
                // ```
                // [rlp1 rlp2 bytes[0] bytes[1]]           rlp1 rlp2 bytes[0] bytes[1]   ...    ]
                // [184  78   129      142       0 0 ... 0 248  76   135      28       5 107 201 118 120 59 0 0 ... 0]

                // The `sel1` column in the `ACCOUNT_LEAF_KEY_S` or `ACCOUNT_LEAF_KEY_C` row
                // is used to mark whether nonce is of 1 byte (short) or more than 1 byte (long).
                // `sel1 = 1` means long, `sel1 = 0` means short.
                // `Bool check is_nonce_long` constraint ensures the `sel1` value is boolean.

                // Analogously, `sel2` holds the information whether balance is long or short.
                // `Bool check is_balance_long` constraint ensures the `sel2` value is boolean.
                require!(is_nonce_long => bool);
                require!(is_balance_long => bool);

                // It is important that there are 0s in `s_main.bytes` after the nonce bytes end.
                // When nonce is short (1 byte), like in `[184,70,1,0,...]`, the constraint is simple:
                // `s_main.bytes[i] = 0` for all `i > 0`.
                // When nonce is long, the constraints need to be written differently because we do not
                // know the length of nonce in advance.
                // The row below holds nonce length specification in `s_main.bytes[0]`.
                // The length in the example below is `1 = 129 - 128`,
                // so the constraint needs to be `s_main.bytes[i] = 0` for
                // all `i > 1` (note that the actual value is in `s_main.bytes[1]`).
                // ```
                // [184  78   129      142       0 0 ... 0 248  76   135      28       5 107 201 118 120 59 0 0 ... 0]
                // ```
                // But instead of 129 we could have 130 or some other value in `s_main.bytes[0]`. For this
                // reason, the constraints are implemented using `key_len_lookup` (see below).
                for (nonce_byte, balance_byte) in s_main.bytes.iter().skip(1).zip(c_main.bytes.iter().skip(1)) {
                    // s_main.bytes[i] = 0 for i > 0 when is_nonce_short
                    ifx!{not::expr(is_nonce_long.expr()) => {
                        require!(a!(nonce_byte) => 0);
                    }}
                    // c_main.bytes[i] = 0 for i > 0 when is_balance_short
                    ifx!{not::expr(is_balance_long.expr()) => {
                        require!(a!(balance_byte) => 0);
                    }}
                }

                // When `non_existing_account_proof` proof type (which can be of two subtypes: with wrong leaf
                // and without wrong leaf, more about it below), the `is_wrong_leaf` flag specifies whether
                // the subtype is with wrong leaf or not.
                // When `non_existing_account_proof` without wrong leaf
                // the proof contains only branches and a placeholder account leaf.
                // In this case, it is checked that there is nil in the parent branch
                // at the proper position (see `account_non_existing`). Note that we need (placeholder) account
                // leaf for lookups and to know when to check that parent branch has a nil.

                // In `is_wrong_leaf is bool` we only check that `is_wrong_leaf` is a boolean values.
                // Other wrong leaf related constraints are in other gates.
                let is_wrong_leaf = a!(s_main.rlp1, rot_into_non_existing);
                let is_non_existing_account_proof = a!(proof_type.is_non_existing_account_proof);
                require!(is_wrong_leaf => bool);

                // Note: some is_wrong_leaf constraints are in this config because
                // account_non_existing config only triggers constraints for
                // non_existing_account proof (see q_enable).
                // is_wrong_leaf needs to be 0 when not in non_existing_account proof
                ifx!{not::expr(is_non_existing_account_proof.expr()) => {
                    require!(is_wrong_leaf => false);
                }};

                let nonce_value_long_rlc = rlc::expr(
                    &s_main.bytes[1..].iter().map(|&byte| a!(byte)).collect::<Vec<_>>(),
                    &r,
                );
                let nonce_rlc = a!(s_main.bytes[0]) + selectx!{is_nonce_long => {
                    nonce_value_long_rlc.expr() * r[0].expr()
                }};

                let nonce_stored = a!(accs.s_mod_node_rlc);
                ifx!{is_nonce_long => {
                    // Besides having nonce (its bytes) stored in `s_main.bytes`, we also have the RLC
                    // of nonce bytes stored in `s_mod_node_hash_rlc` column. The value in this column
                    // is to be used by lookups.
                    // This constraint ensures the RLC of a nonce is computed properly when nonce is long.
                    require!(nonce_stored => nonce_value_long_rlc);
                } elsex {
                    // Similarly as in `Nonce RLP long` constraint, this constraint ensures the RLC of a nonce
                    // is computed properly when nonce is short.
                    require!(nonce_stored => a!(s_main.bytes[0]));
                }}

                // Note: (is_non_existing_account_proof.clone() - is_wrong_leaf.clone() -
                // one.clone()) cannot be 0 when is_non_existing_account_proof = 0.
                let s_rlp1 = a!(s_main.rlp1);
                let s_rlp2 = a!(s_main.rlp2);
                let c_rlp1 = a!(c_main.rlp1);
                let c_rlp2 = a!(c_main.rlp2);

                let c_bytes0 = a!(c_main.bytes[0]);
                let balance_stored = a!(accs.c_mod_node_rlc);

                let balance_value_long_rlc = rlc::expr(
                    &c_main.bytes[1..].iter().map(|&byte| a!(byte)).collect::<Vec<_>>(),
                    &r,
                );
                let balance_rlc = c_bytes0.clone() + selectx!{is_balance_long => {
                    balance_value_long_rlc.clone() * r[0].clone()
                }};

                // Besides having balance (its bytes) stored in `c_main.bytes`, we also have the RLC
                // of nonce bytes stored in `c_mod_node_hash_rlc` column. The value in this column
                // is to be used by lookups.
                // `Balance RLP long` constraint ensures the RLC of a balance is computed properly when
                // balance is long.
                ifx!{is_balance_long => {
                    require!(balance_stored => balance_value_long_rlc);
                } elsex {
                    // Similarly as in `Balance RLP long` constraint,
                    // `Balance RLP short` constraint ensures the RLC of a balance is computed properly when
                    // balance is short.
                    require!(balance_stored => c_bytes0);
                }}

                if is_s {
                    // To enable lookup for nonce modification we need to have S nonce and C nonce in the same row.
                    // For this reason, S nonce RLC is copied to `value_prev` column.
                    require!(nonce_stored => a!(value_prev));
                } else {
                    let nonce_s_stored = a!(accs.s_mod_node_rlc, -1);
                    let balance_s_from_prev = a!(accs.c_mod_node_rlc, -1);
                    let balance_s_from_cur = a!(value_prev);
                    let balance_c_in_value = a!(value);

                    // Note: when nonce or balance is 0, the actual value in the RLP encoding is
                    // 128! TODO: when finalizing lookups, having 128 instead of 0
                    // needs to be taken into account.

                    let nonce_c_from_lookup_row = a!(value, -(ACCOUNT_LEAF_NONCE_BALANCE_C_IND - ACCOUNT_LEAF_NONCE_BALANCE_S_IND));

                    // To enable lookup for nonce modification we need to have S nonce and C nonce in the same row.
                    // For this reason, C nonce RLC is copied to `value` column in `ACCOUNT_LEAF_NONCE_BALANCE_S` row.
                    require!(nonce_stored => nonce_c_from_lookup_row);

                    // To enable lookup for balance modification we need to have S balance and C balance in the same row.
                    // For this reason, S balance RLC is copied to `value_prev` column in C row.
                    require!(balance_s_from_prev => balance_s_from_cur);

                    // To enable lookup for balance modification we need to have S balance and C balance in the same row.
                    // For this reason, C balance RLC is copied to `value` column in C row.
                    require!(balance_c_in_value => balance_stored);

                    // Check there is only one modification at once:
                    let is_storage_mod = a!(proof_type.is_storage_mod);
                    let is_nonce_mod = a!(proof_type.is_nonce_mod);
                    let is_balance_mod = a!(proof_type.is_balance_mod);
                    let is_codehash_mod = a!(proof_type.is_codehash_mod);
                    let is_account_delete_mod = a!(proof_type.is_account_delete_mod);

                    // We need to ensure there is only one modification at a time. If there is storage or
                    // balance modification, we need to ensure `S` nonce and `C` nonce are the same.
                    // Note: For `is_non_existing_account_proof` we do not need this constraint,
                    // `S` and `C` proofs are the same and we need to do a lookup into only one
                    // (the other one could really be whatever).
                    let is_mod = is_storage_mod.expr() + is_balance_mod.expr() + is_codehash_mod.expr();
                    ifx!{is_mod, not::expr(is_account_delete_mod.expr()) => {
                        require!(nonce_stored => nonce_s_stored);
                    }}

                    // We need to ensure there is only one modification at a time. If there is storage or
                    // nonce or codehash modification, we need to ensure `S` balance and `C` balance are the same.
                    // Note: For `is_non_existing_account_proof` we do not need this constraint,
                    // `S` and `C` proofs are the same and we need to do a lookup into only one
                    // (the other one could really be whatever).
                    let is_mod = is_storage_mod.expr() + is_nonce_mod.expr() + is_codehash_mod.expr();
                    ifx!{is_mod, not::expr(is_account_delete_mod.expr()) => {
                        require!(balance_stored => balance_s_from_cur);
                    }}
                }

                // Computed RLC after nonce balance row is the same as the stored RLC value.
                let rlc = acc_prev.expr() + rlc::expr(
                    &[s_rlp1.expr(), s_rlp2.expr(), c_rlp1.expr(), c_rlp2.expr(), nonce_rlc].into_iter().map(|value| value * acc_mult_prev.expr()).collect::<Vec<_>>(),
                    &r,
                ) + balance_rlc * acc_mult_after_nonce.clone();
                require!(a!(accs.acc_s.rlc) => rlc);

                // When adding nonce bytes to the account leaf RLC we do:
                // `rlc_after_nonce = rlc_tmp + s_main.bytes[0] * mult_tmp + s_main.bytes[1] * mult_tmp * r
                //     + ... + s_main.bytes[k] * mult_tmp * r^k`
                // Note that `rlc_tmp` means the RLC after the previous row, while `mult_tmp` means the multiplier
                // (power of randomness `r`) that needs to be used for the first byte in the current row.

                // In this case we assumed there are `k + 1` nonce bytes. After this we continue adding bytes:
                // `rlc_after_nonce + b1 * mult_tmp * r^{k+1} + b2 * mult_tmp * r^{k+1} * r + ...
                // Note that `b1` and `b2` are the first two bytes that need to used next (balance bytes).

                // The problem is `k` can be different from case to case. For this reason, we store `r^{k+1}` in
                // `mult_diff_nonce` (which is actually `acc_c`).
                // That means we can compute the expression above as:
                // `rlc_after_nonce + b1 * mult_tmp * mult_diff_nonce + b2 * mult_tmp * mult_diff_nonce * r + ...

                // However, we need to ensure that `mult_diff_nonce` corresponds to `s_main.bytes[0]` where the length
                // of the nonce is specified. This is done using `key_len_lookup` below.

                // There is one more detail: when computing RLC after nonce, we compute also the bytes that come before
                // nonce bytes in the row. These are: `s_main.rlp1`, `s_main.rlp2`, `c_main.rlp1`, `c_main.rlp2`.
                // It is a bit confusing (we are limited with layout), but `c_main.rlp1` and `c_main.rlp2`
                // are bytes that actually appear in the account leaf RLP stream before `s_main.bytes`.
                // So we have:
                // `rlc_after_nonce = rlc_tmp + s_main.rlp1 * mult_tmp + s_main.rlp2 * mult_tmp * r
                //     + c_main.rlp1 * mult_tmp * r^2 + c_main.rlp2 * mult_tmp * r^3 + s_main.bytes[0] * mult_tmp * r^4 + ...
                //     + s_main.bytes[k] * mult_tmp * r^4 * r^k`
                // That means `mult_diff_nonce` needs to store `r^4 * r^{k+1}` and we continue computing the RLC
                // as mentioned above:
                // `rlc_after_nonce + b1 * mult_tmp * mult_diff_nonce + b2 * mult_tmp * mult_diff_nonce * r + ...

                // Let us observe the following example.
                // [184  78   129      142       0 0 ... 0 248  76   135      28       5 107 201 118 120 59 0 0 ... 0]
                // Here:
                // `rlc_after_nonce = rlc_tmp + 184 * mult_tmp + 78 * mult_tmp * r + 248 * mult_tmp * r^2
                //     + 76 * mult_tmp * r^3 + 129 * mult_tmp * r^4 + 142 * mult_tmp * r^5`
                // And we continue computing the RLC:
                // `rlc_after_nonce + 135 * mult_tmp * mult_diff_nonce + 28 + mult_tmp * mult_diff_nonce * r + ... `
                ifx!{is_nonce_long => {
                    require!(acc_mult_after_nonce => acc_mult_prev.expr() * mult_diff_nonce.expr());
                } elsex {
                    // When nonce is short (occupying only one byte), we know in advance that `mult_diff_nonce = r^5`
                    // as there are `s_main.rlp1`, `s_main.rlp2`, `c_main.rlp1`, `c_main.rlp2`, and `s_main.bytes[0]` bytes
                    // to be taken into account.
                    // r[4] because of s_rlp1, s_rlp2, c_rlp1, c_rlp2, and 1 for nonce_len = 1
                    require!(acc_mult_after_nonce => acc_mult_prev.expr() * r[4].expr());
                }}

                // We need to prepare the multiplier that will be needed in the next row: `acc_mult_final`.
                // We have the multiplier after nonce bytes were added to the RLC: `acc_mult_after_nonce`.
                // Now, `acc_mult_final` depends on the number of balance bytes.
                // `rlc_after_balance = rlc_after_nonce + b1 * acc_mult_after_nonce + ...
                //     + bl * acc_mult_after_nonce * r^{l-1}`
                // Where `b1,...,bl` are `l` balance bytes. As with nonce, we do not know the length of balance bytes
                // in advance. For this reason, we store `r^l` in `mult_diff_balance` and check whether:
                // `acc_mult_final = acc_mult_after_nonce * mult_diff_balance`.
                // Note that `mult_diff_balance` is not the last multiplier in this row, but the first in
                // the next row (this is why there is `r^l` instead of `r^{l-1}`).
                let acc_mult_final = a!(accs.acc_s.mult);
                ifx!{is_balance_long => {
                    require!(acc_mult_final => acc_mult_after_nonce.expr() * mult_diff_balance.expr());
                } elsex {
                    // When balance is short, there is only one balance byte and we know in advance that the
                    // multiplier changes only by factor `r`.
                    require!(acc_mult_final => acc_mult_after_nonce.expr() * r[0].expr());
                }}

                ifx!{is_non_existing_account_proof.expr() - is_wrong_leaf.expr() - 1.expr() => {
                    // RLP:
                    // s_rlp1  s_rlp2  c_rlp1  c_rlp2  s_main.bytes  c_main.bytes
                    // 184     80      248     78      nonce         balance

                    // Or:
                    // s_rlp1  s_rlp2  c_rlp1  c_rlp2  s_main.bytes                         c_main.bytes
                    // 248     109     157     (this is key row, 157 means key of length 29)
                    // 184     77      248     75      7 (short nonce , only one byte)      135 (means balance is of length 7) 28 ... 59

                    let nonce_long_len = a!(s_main.bytes[0]) - 128.expr() + 1.expr();
                    let nonce_len = nonce_long_len * is_nonce_long.clone() + not::expr(is_nonce_long.expr());

                    let balance_long_len = c_bytes0 - 128.expr() + 1.expr();
                    let balance_len = balance_long_len * is_balance_long.clone() + not::expr(is_balance_long);

                    // `s_main.rlp1` always needs to be 184. This is RLP byte meaning that behind this byte
                    // there is a string of length more than 55 bytes and that only `1 = 184 - 183` byte is reserved
                    // for length (`s_main.rlp2`). The string is always of length greater than 55 because there
                    // are codehash (32 bytes) and storage root (32 bytes) in the next row as part of this string.

                    // The only exception is when `is_non_existing_account_proof = 1` & `is_wrong_leaf = 0`.
                    // In this case the value does not matter as the account leaf is only a placeholder and
                    // does not use `s_main.rlp1` and `s_main.rlp2`. Note that it uses `s_main` for nibbles
                    // because the account address is computed using nibbles and this account address needs
                    // to be as required by a lookup.
                    require!(s_rlp1 => 184);

                    // `c_main.rlp1` needs to always be 248. This is RLP byte meaning that behind this byte
                    // there is a list which has one byte that specifies the length - `at c_main.rlp2`.

                    // The only exception is when `is_non_existing_account_proof = 1` & `is_wrong_leaf = 0`.
                    // In this case the value does not matter as the account leaf is only a placeholder and
                    // does not use `c_main`. Note that it uses `s_main` for nibbles because the account address
                    // is computed using nibbles and this account address needs to be as required by a lookup.
                    // That means there is an account leaf which is just a placeholder but it still has the
                    // correct address.
                    require!(c_rlp1 => 248);

                    // `c_main.rlp2` specifies the length of the remaining RLP string. Note that the string
                    // is `s_main.rlp1`, `s_main.rlp2`, `c_main.rlp1`, `c_main.rlp2`, nonce bytes, balance bytes.
                    // Thus, `c_main.rlp2 = #(nonce bytes) + #(balance bytes) + 32 + 32`.
                    // `s_main.rlp2` - `c_main.rlp2` = 2 because of two bytes difference: `c_main.rlp1` and c_main.rlp2`.
                    // Example:
                    // [184  78   129      142       0 0 ... 0 248  76   135      28       5 107 201 118 120 59 0 0 ... 0]
                    // We can see: `78 - 76 - 1 - 1 = 0`.
                    require!(s_rlp2 => c_rlp2.expr() + 2.expr());

                    // `c_main.rlp2 = #(nonce bytes) + #(balance bytes) + 32 + 32`.
                    // Note that `32 + 32` means the number of codehash bytes + the number of storage root bytes.
                    require!(c_rlp2 => nonce_len.expr() + balance_len.expr() + 66.expr());

                    // The whole RLP length of the account leaf is specified in the account leaf key row with
                    // `s_main.rlp1 = 248` and `s_main.rlp2`. `s_main.rlp2` in key row actually specifies the length.
                    // `s_main.rlp2` in nonce balance row specifies the length of the remaining string in nonce balance
                    // row, so we need to check that `s_main.rlp2` corresponds to the key length (in key row) and
                    // `s_main.rlp2` in nonce balance row. However, we need to take into account also the bytes
                    // where the lengths are stored:
                    // `s_main.rlp2 (key row) - key_len - 1 (because key_len is stored in 1 byte)
                    //     - s_main.rlp2 (nonce balance row) - 1 (because of s_main.rlp1)
                    //     - 1 (because of s_main.rlp2) = 0`
                    // Example:
                    // [248,106,161,32,252,237,52,8,133,130,180,167,143,97,28,115,102,25,94,62,148,249,8,6,55,244,16,75,187,208,208,127,251,120,61,73,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
                    // [184,70,128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,248,68,128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
                    // We can see: `106 - 33 - 1 - 70 - 1 - 1 = 0`.
                    let rlp_len = a!(s_main.rlp2, rot);
                    let key_len = a!(s_main.bytes[0], rot) - 128.expr();
                    require!(rlp_len => key_len.expr() + 1.expr() + s_rlp2.expr() + 2.expr());
                }}
                }}
            }}

            cb.gate(1.expr())
        });

        let q_enable_nonce_long = |meta: &mut VirtualCells<F>| {
            let q_enable = q_enable(meta);
            let mut is_nonce_long = meta.query_advice(
                denoter.sel1,
                Rotation(-(ACCOUNT_LEAF_NONCE_BALANCE_S_IND - ACCOUNT_LEAF_KEY_S_IND)),
            );
            if !is_s {
                is_nonce_long = meta.query_advice(
                    denoter.sel1,
                    Rotation(-(ACCOUNT_LEAF_NONCE_BALANCE_C_IND - ACCOUNT_LEAF_KEY_C_IND)),
                );
            }

            q_enable * is_nonce_long
        };

        /*
        `mult_diff_nonce` needs to correspond to nonce length + 5 bytes:
        `s_main.rlp1,` `s_main.rlp2`, `c_main.rlp1`, `c_main.rlp1`, 1 for byte with nonce length (`s_main.bytes[0]`).
        That means `mult_diff_nonce` needs to be `r^{nonce_len+5}` where `nonce_len = s_main.bytes[0] - 128`.

        Note that when nonce is short, `mult_diff_nonce` is not used (see the constraint above).
        */
        mult_diff_lookup(
            meta,
            q_enable_nonce_long, /* mult_diff_nonce is acc_r when is_nonce_short (mult_diff
                                  * doesn't need to be checked
                                  * as it's not used) */
            5, /* 4 for s_rlp1, s_rlp2, c_rlp1, c_rlp1; 1 for byte with length
                * info */
            s_main.bytes[0],
            accs.acc_c.rlc,
            128,
            fixed_table,
        );

        // There are zeros in s_main.bytes after nonce length:
        /*
        Nonce RLC is computed over `s_main.bytes[1]`, ..., `s_main.bytes[31]` because we do not know
        the nonce length in advance. To prevent changing the nonce and setting `s_main.bytes[i]` for
        `i > nonce_len + 1` to get the correct nonce RLC, we need to ensure that
        `s_main.bytes[i] = 0` for `i > nonce_len + 1`.
        */
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
        }

        let q_enable_balance_long = |meta: &mut VirtualCells<F>| {
            let q_enable = q_enable(meta);
            let mut is_balance_long = meta.query_advice(
                denoter.sel1,
                Rotation(-(ACCOUNT_LEAF_NONCE_BALANCE_S_IND - ACCOUNT_LEAF_KEY_S_IND)),
            );
            if !is_s {
                is_balance_long = meta.query_advice(
                    denoter.sel1,
                    Rotation(-(ACCOUNT_LEAF_NONCE_BALANCE_C_IND - ACCOUNT_LEAF_KEY_C_IND)),
                );
            }

            q_enable * is_balance_long
        };

        /*
        `mult_diff_balance` needs to correspond to balance length + 1 byte for byte that contains balance length.
        That means `mult_diff_balance` needs to be `r^{balance_len+1}` where `balance_len = c_main.bytes[0] - 128`.

        Note that when balance is short, `mult_diff_balance` is not used (see the constraint above).
        */
        mult_diff_lookup(
            meta,
            q_enable_balance_long,
            1, // 1 for byte with length info
            c_main.bytes[0],
            accs.key.mult,
            128,
            fixed_table,
        );

        /*
        Balance RLC is computed over `c_main.bytes[1]`, ..., `c_main.bytes[31]` because we do not know
        the balance length in advance. To prevent changing the balance and setting `c_main.bytes[i]` for
        `i > balance_len + 1` to get the correct balance RLC, we need to ensure that
        `c_main.bytes[i] = 0` for `i > balance_len + 1`.
        */
        if check_zeros {
            for ind in 1..HASH_WIDTH {
                key_len_lookup(
                    meta,
                    q_enable,
                    ind,
                    c_main.bytes[0],
                    c_main.bytes[ind],
                    128,
                    fixed_table,
                )
            }
        }

        /*
        Range lookups ensure that `s_main` and `c_main` columns are all bytes (between 0 - 255).
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
            c_main.bytes.to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );
        // c_rlp1 is always 248 (checked above)
        range_lookups(
            meta,
            q_enable,
            [s_main.rlp1, s_main.rlp2, c_main.rlp2].to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );

        AccountLeafNonceBalanceConfig {
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
        let mut nonce_len: usize = 1;
        // Note: when nonce or balance is 0, the actual value stored in RLP encoding is
        // 128.
        if row.get_byte(S_START) > 128 {
            nonce_len = row.get_byte(S_START) as usize - 128 + 1; // +1 for byte with length info
            region
                .assign_advice(
                    || "assign sel1".to_string(),
                    mpt_config.denoter.sel1,
                    offset - (ACCOUNT_LEAF_NONCE_BALANCE_S_IND - ACCOUNT_LEAF_KEY_S_IND) as usize,
                    || Value::known(F::one()),
                )
                .ok();
        } else {
            region
                .assign_advice(
                    || "assign sel1".to_string(),
                    mpt_config.denoter.sel1,
                    offset - (ACCOUNT_LEAF_NONCE_BALANCE_C_IND - ACCOUNT_LEAF_KEY_C_IND) as usize,
                    || Value::known(F::zero()),
                )
                .ok();
        }

        let mut balance_len: usize = 1;
        if row.get_byte(C_START) > 128 {
            balance_len = row.get_byte(C_START) as usize - 128 + 1; // +1 for byte with length info
            region
                .assign_advice(
                    || "assign sel2".to_string(),
                    mpt_config.denoter.sel2,
                    offset - (ACCOUNT_LEAF_NONCE_BALANCE_S_IND - ACCOUNT_LEAF_KEY_S_IND) as usize,
                    || Value::known(F::one()),
                )
                .ok();
        } else {
            region
                .assign_advice(
                    || "assign sel2".to_string(),
                    mpt_config.denoter.sel2,
                    offset - (ACCOUNT_LEAF_NONCE_BALANCE_C_IND - ACCOUNT_LEAF_KEY_C_IND) as usize,
                    || Value::known(F::zero()),
                )
                .ok();
        }

        // nonce value RLC and balance value RLC:
        pv.rlc1 = F::zero();
        pv.rlc2 = F::zero();
        // Note: Below, it first computes and assigns the nonce RLC and balance RLC
        // without RLP specific byte (there is a RLP specific byte when
        // nonce/balance RLP length > 1).
        if nonce_len == 1 && balance_len == 1 {
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
        } else if nonce_len > 1 && balance_len == 1 {
            mpt_config
                .compute_rlc_and_assign(
                    region,
                    &row.bytes,
                    pv,
                    offset,
                    (S_START + 1, HASH_WIDTH - 1),
                    (C_START, HASH_WIDTH),
                )
                .ok();
        } else if nonce_len == 1 && balance_len > 1 {
            mpt_config
                .compute_rlc_and_assign(
                    region,
                    &row.bytes,
                    pv,
                    offset,
                    (S_START, HASH_WIDTH),
                    (C_START + 1, HASH_WIDTH - 1),
                )
                .ok();
        } else if nonce_len > 1 && balance_len > 1 {
            mpt_config
                .compute_rlc_and_assign(
                    region,
                    &row.bytes,
                    pv,
                    offset,
                    (S_START + 1, HASH_WIDTH - 1),
                    (C_START + 1, HASH_WIDTH - 1),
                )
                .ok();
        }

        let mut acc_account;
        let mut acc_mult_account;
        if row.get_type() == MptWitnessRowType::AccountLeafNonceBalanceS {
            pv.nonce_value_s = pv.rlc1;
            pv.balance_value_s = pv.rlc2;

            acc_account = pv.acc_account_s;
            acc_mult_account = pv.acc_mult_account_s;

            // assign nonce S RLC in ACCOUNT_LEAF_NONCE_BALANCE_S row.
            region
                .assign_advice(
                    || "assign value_prev".to_string(),
                    mpt_config.value_prev,
                    offset,
                    || Value::known(pv.rlc1),
                )
                .ok();

            if row.get_byte_rev(IS_NONCE_MOD_POS) == 1 {
                region
                    .assign_advice(
                        || "assign which lookup type enabled".to_string(),
                        mpt_config.proof_type.proof_type,
                        offset,
                        || Value::known(F::from(1_u64)),
                    )
                    .ok();
            }
        } else {
            acc_account = pv.acc_account_c;
            acc_mult_account = pv.acc_mult_account_c;

            // Assign nonce C RLC in ACCOUNT_LEAF_NONCE_BALANCE_S row.
            region
                .assign_advice(
                    || "assign nonce C".to_string(),
                    mpt_config.value,
                    offset
                        - (ACCOUNT_LEAF_NONCE_BALANCE_C_IND - ACCOUNT_LEAF_NONCE_BALANCE_S_IND)
                            as usize,
                    || Value::known(pv.rlc1), // rlc1 is nonce
                )
                .ok();

            // assign balance S RLC in ACCOUNT_LEAF_NONCE_BALANCE_C row.
            region
                .assign_advice(
                    || "assign value_prev".to_string(),
                    mpt_config.value_prev,
                    offset,
                    || Value::known(pv.balance_value_s),
                )
                .ok();

            // Assign balance C RLC in ACCOUNT_LEAF_NONCE_BALANCE_C row.
            region
                .assign_advice(
                    || "assign balance C".to_string(),
                    mpt_config.value,
                    offset,
                    || Value::known(pv.rlc2), // rlc2 is balance
                )
                .ok();

            if row.get_byte_rev(IS_BALANCE_MOD_POS) == 1 {
                region
                    .assign_advice(
                        || "assign which lookup type enabled".to_string(),
                        mpt_config.proof_type.proof_type,
                        offset,
                        || Value::known(F::from(2_u64)),
                    )
                    .ok();
            }
        }

        // s_rlp1, s_rlp2
        mpt_config.compute_acc_and_mult(
            &row.bytes,
            &mut acc_account,
            &mut acc_mult_account,
            S_START - 2,
            2,
        );
        // c_rlp1, c_rlp2
        mpt_config.compute_acc_and_mult(
            &row.bytes,
            &mut acc_account,
            &mut acc_mult_account,
            C_START - 2,
            2,
        );
        // nonce contribution to leaf RLC:
        /*
        If nonce stream length is 1, it doesn't have
        the first byte with length info. Same for balance.
        There are four possibilities:
            - nonce is short (length 1), balance is short (length 1)
            - nonce is short, balance is long
            - nonce is long, balance is short
            - nonce is long, balance is long
        We put this info in sel1/sel2 in the key row (sel1/sel2 are
            already used for other purposes in nonce balance row):
            - sel1/sel2: 0/0 (how to check: (1-sel1)*(1-sel2))
            - sel1/sel2: 0/1 (how to check: (1-sel1)*sel2)
            - sel1/sel2: 1/0 (how to check: sel1*(1-sel2))
            - sel1/sel2: 1/1 (how to check: sel1*sel2)
        */

        mpt_config.compute_acc_and_mult(
            &row.bytes,
            &mut acc_account,
            &mut acc_mult_account,
            S_START,
            nonce_len,
        );

        let mut mult_diff_s = F::one();
        for _ in 0..nonce_len + 4 {
            // + 4 because of s_rlp1, s_rlp2, c_rlp1, c_rlp2
            mult_diff_s *= mpt_config.randomness;
        }

        // It's easier to constrain (in account_leaf_nonce_balance.rs)
        // the multiplier if we store acc_mult both after nonce and after
        // balance.
        let acc_mult_tmp = acc_mult_account;

        // balance contribution to leaf RLC
        mpt_config.compute_acc_and_mult(
            &row.bytes,
            &mut acc_account,
            &mut acc_mult_account,
            C_START,
            balance_len,
        );

        let mut mult_diff_c = F::one();
        for _ in 0..balance_len {
            mult_diff_c *= mpt_config.randomness;
        }

        mpt_config
            .assign_acc(
                region,
                acc_account,
                acc_mult_account,
                F::zero(),
                acc_mult_tmp,
                offset,
            )
            .ok();

        region
            .assign_advice(
                || "assign mult diff".to_string(),
                mpt_config.accumulators.acc_c.rlc, /* assigning key_rlc leads into
                                                    * PoisonedConstraint */
                offset,
                || Value::known(mult_diff_s),
            )
            .ok();
        region
            .assign_advice(
                || "assign mult diff".to_string(),
                mpt_config.accumulators.key.mult,
                offset,
                || Value::known(mult_diff_c),
            )
            .ok();
        if row.get_type() == MptWitnessRowType::AccountLeafNonceBalanceS {
            pv.acc_nonce_balance_s = acc_account;
            pv.acc_mult_nonce_balance_s = acc_mult_account;
        } else {
            pv.acc_nonce_balance_c = acc_account;
            pv.acc_mult_nonce_balance_c = acc_mult_account;
        }
    }
}
