use gadgets::util::{not, Expr};
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Region, Value},
    plonk::{Expression, VirtualCells},
    poly::Rotation,
};
use std::marker::PhantomData;

use crate::{
    circuit,
    evm_circuit::util::rlc,
    mpt_circuit::witness_row::{MptWitnessRow, MptWitnessRowType},
    mpt_circuit::FixedTableTag,
    mpt_circuit::{
        helpers::BaseConstraintBuilder,
        param::{
            ACCOUNT_LEAF_KEY_C_IND, ACCOUNT_LEAF_KEY_S_IND, ACCOUNT_LEAF_NONCE_BALANCE_C_IND,
            ACCOUNT_LEAF_NONCE_BALANCE_S_IND, ACCOUNT_NON_EXISTING_IND, C_START, HASH_WIDTH,
            S_START,
        },
    },
    mpt_circuit::{helpers::ColumnTransition, MPTContext},
    mpt_circuit::{
        param::{IS_BALANCE_MOD_POS, IS_NONCE_MOD_POS},
        MPTConfig, ProofValues,
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


[248,112,157,59,158,160,175,159,65,212,107,23,98,208,38,205,150,63,244,2,185,
236,246,95,240,224,191,229,27,102,202,231,184,80 There are 112
bytes after the first two bytes. 157 means the key is 29 (157 -
128) bytes long. Nonce, balance, storage, codehash are string in
RLP: s_rlp1 and s_rlp2 contains the length of this string, for
example 184 80 means the second part is of length 1 (183 + 1 =
184) and there are 80 bytes in this string. Then there is a list
rlp meta data 248 78 where (this is stored in c_rlp1 and
c_rlp2) 78 = 3 (nonce) + 9 (balance) + 33 (storage) + 33
(codehash). We have nonce in s_main.bytes and balance in c_main.bytes.
s_rlp1  s_rlp2  c_rlp1  c_rlp2  s_main.bytes  c_main.bytes
184     80      248     78      nonce      balance

If nonce (same holds for balance) is smaller or equal to 128, then it will
occupy only one byte: `s_main.bytes[0]` (`c_main.bytes[0]` for
balance). For example, the row [184,70,128,0,...,0] holds 128 in
bytes[0] which means nonce = 128 - 128 = 0. For example, the row
[184,70,1,0,...,0] holds 1 in bytes[0] which means nonce = 1.
In case nonce (same for balance) is bigger than 128, it will occupy more than
1 byte. The example row below shows nonce value 142, while 129
means there is a nonce of byte length `1 = 129 - 128`.
Balance in the example row below is: 28 + 5 * 256 + 107 * 256^2 + ... + 59 *
256^6, while 135 means there are 7 = 135 - 128 bytes.
```
[rlp1 rlp2 bytes[0] bytes[1]]           rlp1 rlp2 bytes[0] bytes[1]   ...    ]
[184  78   129      142       0 0 ... 0 248  76   135      28       5 107 201 118 120 59 0 0 ... 0]
The `sel1` column in the `ACCOUNT_LEAF_KEY_S` or `ACCOUNT_LEAF_KEY_C` row
is used to mark whether nonce is of 1 byte (short) or more than 1 byte (long).
`sel1 = 1` means long, `sel1 = 0` means short.
`Bool check is_nonce_long` constraint ensures the `sel1` value is boolean.
Analogously, `sel2` holds the information whether balance is long or short.
`Bool check is_balance_long` constraint ensures the `sel2` value is boolean.


Lookups:
We have nonce and balance in the same row - to enable lookups into the same columns (`value_prev`, `value`),
we enable nonce lookup in `ACCOUNT_LEAF_NONCE_BALANCE_S` row and balance lookup in `ACCOUNT_LEAF_NONCE_BALANCE_C` row.
This means we copy nonce C RLC to `ACCOUNT_LEAF_NONCE_BALANCE_S` row,
and balance S RLC to `ACCOUNT_LEAF_NONCE_BALANCE_C` row.
Constraints are added to ensure everything is properly copied.
*/
#[derive(Clone, Debug, Default)]
pub(crate) struct AccountLeafNonceBalanceConfig<F> {
    _marker: PhantomData<F>,
}

impl<F: FieldExt> AccountLeafNonceBalanceConfig<F> {
    pub fn configure(
        meta: &mut VirtualCells<'_, F>,
        cb: &mut BaseConstraintBuilder<F>,
        ctx: MPTContext<F>,
        is_s: bool,
    ) -> Self {
        let proof_type = ctx.proof_type;
        let s_main = ctx.s_main;
        let c_main = ctx.c_main;
        let accs = ctx.accumulators;
        let value_prev = ctx.value_prev;
        let value = ctx.value;
        let denoter = ctx.denoter;
        let r = ctx.r.clone();

        let rot_key = if is_s {
            -(ACCOUNT_LEAF_NONCE_BALANCE_S_IND - ACCOUNT_LEAF_KEY_S_IND)
        } else {
            -(ACCOUNT_LEAF_NONCE_BALANCE_C_IND - ACCOUNT_LEAF_KEY_C_IND)
        };
        let rot_non_existing = if is_s {
            -ACCOUNT_LEAF_NONCE_BALANCE_S_IND
        } else {
            -ACCOUNT_LEAF_NONCE_BALANCE_C_IND
        } + ACCOUNT_NON_EXISTING_IND;
        let rot_s = if is_s {
            0
        } else {
            -(ACCOUNT_LEAF_NONCE_BALANCE_C_IND - ACCOUNT_LEAF_NONCE_BALANCE_S_IND)
        };

        circuit!([meta, cb], {
            // When `non_existing_account_proof` proof type (which can be of two subtypes:
            // with wrong leaf and without wrong leaf, more about it below), the
            // `is_wrong_leaf` flag specifies whether the subtype is with wrong
            // leaf or not. When `non_existing_account_proof` without wrong leaf
            // the proof contains only branches and a placeholder account leaf.
            // In this case, it is checked that there is nil in the parent branch
            // at the proper position (see `account_non_existing`). Note that we need
            // (placeholder) account leaf for lookups and to know when to check
            // that parent branch has a nil.
            // In `is_wrong_leaf is bool` we only check that `is_wrong_leaf` is a boolean
            // values. Other wrong leaf related constraints are in other gates.
            let is_wrong_leaf = a!(s_main.rlp1, rot_non_existing);
            require!(is_wrong_leaf => bool);
            // Note: some is_wrong_leaf constraints are in this config because
            // account_non_existing config only triggers constraints for
            // non_existing_account proof (see q_enable).
            // is_wrong_leaf needs to be 0 when not in non_existing_account proof
            ifx! {not!(a!(proof_type.is_non_existing_account_proof)) => {
                require!(is_wrong_leaf => false);
            }};

            // RLC calculation
            let nonce = ColumnTransition::new(meta, accs.s_mod_node_rlc);
            let balance = ColumnTransition::new(meta, accs.c_mod_node_rlc);
            let is_nonce_long = a!(denoter.sel1, rot_key);
            let is_balance_long = a!(denoter.sel2, rot_key);
            let mult_diff_nonce = a!(accs.acc_c.rlc);
            let mult_diff_balance = a!(accs.key.mult);

            let mut calc_rlc = |data: Expression<F>,
                                is_long: Expression<F>,
                                mult_diff: Expression<F>,
                                mult_offset: u64,
                                is_s: bool| {
                // The is_long selector needs to be boolean
                require!(is_long => bool);
                // Calculate the RLC
                let (len, rlc) = ifx! {is_long => {
                    let num_bytes = 1.expr() + (a!(ctx.main(is_s).bytes[0]) - 128.expr());
                    let rlc = rlc::expr(
                        &ctx.main(is_s).bytes[1..]
                            .iter()
                            .map(|&byte| a!(byte))
                            .collect::<Vec<_>>(),
                        &r,
                    );
                    (num_bytes, rlc)
                } elsex {
                    (1.expr(), a!(ctx.main(is_s).bytes[0]))
                }};
                require!(data => rlc);
                // RLC bytes zero check
                cb.set_range_length_sc(is_s, len.expr());
                // Get the correct multiploer for the length
                require!((FixedTableTag::RMult, len.expr() + mult_offset.expr(), mult_diff) => @format!("mult{}", if is_s {""} else {"2"}));

                // Go from the value rlc to the full rlc
                let rlc = ifx! {is_long => {
                    a!(ctx.main(is_s).bytes[0]) + rlc.expr() * r[0].expr()
                } elsex {
                    rlc
                }};
                (rlc, len)
            };
            // `mult_diff_nonce` needs to correspond to nonce length + 4 bytes (s_rlp1,
            // s_rlp2, c_rlp1, c_rlp1)
            let (nonce_rlc, nonce_len) =
                calc_rlc(nonce.expr(), is_nonce_long, mult_diff_nonce.expr(), 4, true);
            let (balance_rlc, balance_len) = calc_rlc(
                balance.expr(),
                is_balance_long,
                mult_diff_balance.expr(),
                0,
                false,
            );

            // Calculate and store the combined nonce + balance multipliers
            let acc_mult_prev = a!(accs.acc_s.mult, rot_key);
            let acc_mult_after_nonce = a!(accs.acc_c.mult);
            let mult_diff_balance = a!(accs.key.mult);
            let acc_mult_final = a!(accs.acc_s.mult);
            require!(acc_mult_after_nonce => acc_mult_prev.expr() * mult_diff_nonce.expr());
            require!(acc_mult_final => acc_mult_after_nonce.expr() * mult_diff_balance.expr());
            // Store the combined nonce + balance RLC.
            let acc_prev = a!(accs.acc_s.rlc, rot_key);
            let rlc = acc_prev.expr()
                + rlc::expr(
                    &[
                        a!(s_main.rlp1),
                        a!(s_main.rlp2),
                        a!(c_main.rlp1),
                        a!(c_main.rlp2),
                        nonce_rlc,
                    ]
                    .into_iter()
                    .map(|value| value * acc_mult_prev.expr())
                    .collect::<Vec<_>>(),
                    &r,
                )
                + balance_rlc * acc_mult_after_nonce.clone();
            require!(a!(accs.acc_s.rlc) => rlc);

            // Check the RLP encoding consistency.
            // The only exception is when `is_non_existing_account_proof = 1` &
            // `is_wrong_leaf = 0`. In this case the value does not matter as
            // the account leaf is only a placeholder and does not use
            // `s_main.rlp1` and `s_main.rlp2`.
            //  TODO(Brecht): Can we remove this if by just making this pass in this special
            // case?
            ifx! {not!(and::expr(&[a!(proof_type.is_non_existing_account_proof), not!(is_wrong_leaf)])) => {
                // `s_main.rlp1` always needs to be 184. This is RLP byte meaning that behind this byte
                // there is a string of length more than 55 bytes and that only `1 = 184 - 183` byte is reserved
                // for length (`s_main.rlp2`). The string is always of length greater than 55 because there
                // are codehash (32 bytes) and storage root (32 bytes) in the next row as part of this string.
                // Note that it uses `s_main` for nibbles because the account address is computed using nibbles
                // and this account address needs to be as required by a lookup.
                require!(a!(s_main.rlp1) => 184);
                // `c_main.rlp1` needs to always be 248. This is RLP byte meaning that behind this byte
                // there is a list which has one byte that specifies the length at `c_main.rlp2`.
                // The only exception is when `is_non_existing_account_proof = 1` & `is_wrong_leaf = 0`.
                // In this case the value does not matter as the account leaf is only a placeholder and
                // does not use `c_main`. Note that it uses `s_main` for nibbles because the account address
                // is computed using nibbles and this account address needs to be as required by a lookup.
                // That means there is an account leaf which is just a placeholder but it still has the
                // correct address.
                require!(a!(c_main.rlp1) => 248);
                // `c_main.rlp2` specifies the length of the remaining RLP string. Note that the string
                // is `s_main.rlp1`, `s_main.rlp2`, `c_main.rlp1`, `c_main.rlp2`, nonce bytes, balance bytes.
                // Thus, `c_main.rlp2 = #(nonce bytes) + #(balance bytes) + 32 + 32`.
                // `s_main.rlp2` - `c_main.rlp2` = 2 because of two bytes difference: `c_main.rlp1` and c_main.rlp2`.
                // Example:
                // [184  78   129      142       0 0 ... 0 248  76   135      28       5 107 201 118 120 59 0 0 ... 0]
                // We can see: `78 - 76 - 1 - 1 = 0`.
                require!(a!(s_main.rlp2) => a!(c_main.rlp2) + 2.expr());
                // `c_main.rlp2 = #(nonce bytes) + #(balance bytes) + 32 + 32`.
                // Note that `32 + 32` means the number of codehash bytes + the number of storage root bytes.
                require!(a!(c_main.rlp2) => nonce_len.expr() + balance_len.expr() + (2 + 32 + 32).expr());
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
                let rlp_len = a!(s_main.rlp2, rot_key);
                let key_len = a!(s_main.bytes[0], rot_key) - 128.expr();
                require!(rlp_len => key_len.expr() + 1.expr() + a!(s_main.rlp2) + 2.expr());
            }}

            // Verify data consistency for lookup data.
            // To enable lookup for balance modification we need to have S balance and C
            // balance in the same row.
            if is_s {
                // Copy S nonce RLC to `value_prev` column.
                require!(a!(value_prev) => nonce);
            } else {
                // Note: when nonce or balance is 0, the actual value in the RLP encoding is
                // 128! TODO: when finalizing lookups, having 128 instead of 0
                // needs to be taken into account.
                // Copy C nonce RLC to `value` column in `ACCOUNT_LEAF_NONCE_BALANCE_S` row.
                require!(a!(value, rot_s) => nonce);
                // Copy S balance RLC to `value_prev` column in C row.
                require!(a!(value_prev) => balance.prev());
                // Copy C balance RLC to `value` column in C row.
                require!(a!(value) => balance);
            }

            // Check that there is only one modification.
            if !is_s {
                // Note: For `is_non_existing_account_proof` we do not need this constraint,
                // `S` and `C` proofs are the same and we need to do a lookup into only one
                // (the other one could really be whatever).
                // TODO(Brecht): I think should be able to remove this if by changing the
                // witness
                ifx! {not!(a!(proof_type.is_account_delete_mod)) => {
                    // Nonce needs to remain the same when not modifying the nonce
                    ifx!{not!(a!(proof_type.is_nonce_mod)) => {
                        require!(nonce => nonce.prev());
                    }}
                    // Balance needs to remain the same when not modifying the balance
                    ifx!{not!(a!(proof_type.is_balance_mod)) => {
                        require!(balance => balance.prev());
                    }}
                }}
            }
        });

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
