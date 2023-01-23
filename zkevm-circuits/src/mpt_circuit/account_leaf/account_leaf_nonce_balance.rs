use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Region, Value},
    plonk::{Expression, VirtualCells},
    poly::Rotation,
};
use std::marker::PhantomData;

use crate::{
    circuit,
    circuit_tools::{DataTransition, LRCable},
    mpt_circuit::MPTContext,
    mpt_circuit::{helpers::get_num_bytes_short, FixedTableTag},
    mpt_circuit::{
        helpers::AccountLeafInfo,
        param::{
            ACCOUNT_LEAF_KEY_C_IND, ACCOUNT_LEAF_KEY_S_IND, ACCOUNT_LEAF_NONCE_BALANCE_C_IND,
            ACCOUNT_LEAF_NONCE_BALANCE_S_IND, C_START, HASH_WIDTH, RLP_LIST_LONG, RLP_LONG,
            S_START,
        },
    },
    mpt_circuit::{
        helpers::MPTConstraintBuilder,
        witness_row::{MptWitnessRow, MptWitnessRowType},
    },
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

Note: when nonce or balance is 0, the actual value in the RLP encoding is
128! TODO: when finalizing lookups, having 128 instead of 0
needs to be taken into account.

*/
#[derive(Clone, Debug, Default)]
pub(crate) struct AccountLeafNonceBalanceConfig<F> {
    _marker: PhantomData<F>,
}

impl<F: FieldExt> AccountLeafNonceBalanceConfig<F> {
    pub fn configure(
        meta: &mut VirtualCells<'_, F>,
        cb: &mut MPTConstraintBuilder<F>,
        ctx: MPTContext<F>,
        is_s: bool,
    ) -> Self {
        let proof_type = ctx.proof_type;
        let s_main = ctx.s_main;
        let c_main = ctx.c_main;
        let accs = ctx.accumulators;
        let value_prev = ctx.value_prev;
        let value = ctx.value;
        let r = ctx.r.clone();

        let rot_key = if is_s {
            -(ACCOUNT_LEAF_NONCE_BALANCE_S_IND - ACCOUNT_LEAF_KEY_S_IND)
        } else {
            -(ACCOUNT_LEAF_NONCE_BALANCE_C_IND - ACCOUNT_LEAF_KEY_C_IND)
        };
        let rot_s = if is_s {
            0
        } else {
            -(ACCOUNT_LEAF_NONCE_BALANCE_C_IND - ACCOUNT_LEAF_NONCE_BALANCE_S_IND)
        };

        circuit!([meta, cb.base], {
            let account = AccountLeafInfo::new(meta, ctx.clone(), rot_key);

            // The two string RLP bytes stored in the s RLP bytes.
            // The two list RLP bytes are stored in the c RLP bytes.
            // The RLP bytes of nonce/balance are stored bytes[0].

            // RLC calculation for nonce/balance
            let nonce = DataTransition::new(meta, accs.s_mod_node_rlc);
            let balance = DataTransition::new(meta, accs.c_mod_node_rlc);
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
                let (num_bytes, value_rlc) = ifx! {is_long => {
                    let num_bytes = get_num_bytes_short(a!(ctx.main(is_s).bytes[0]));
                    let value_rlc = ctx.main(is_s).bytes(meta, 0)[1..].to_vec().rlc(&r);
                    (num_bytes, value_rlc)
                } elsex {
                    (1.expr(), a!(ctx.main(is_s).bytes[0]))
                }};
                require!(data => value_rlc);
                // RLC bytes zero check (+2 because data starts at bytes[0])
                cb.set_length_sc(is_s, 2.expr() + num_bytes.expr());
                // Get the correct multiplier for the length
                require!((FixedTableTag::RMult, num_bytes.expr() + mult_offset.expr(), mult_diff) => @format!("mult{}", if is_s {""} else {"2"}));

                // Go from the value rlc to the data rlc
                let rlc = account.to_data_rlc(meta, ctx.main(is_s), value_rlc, is_long, 0);
                (rlc, num_bytes)
            };
            let (nonce_rlc, nonce_num_bytes) = calc_rlc(
                nonce.expr(),
                account.is_nonce_long(),
                mult_diff_nonce.expr(),
                4,
                true,
            );
            let (balance_rlc, balance_num_bytes) = calc_rlc(
                balance.expr(),
                account.is_balance_long(),
                mult_diff_balance.expr(),
                0,
                false,
            );

            // Calculate and store the combined nonce + balance multipliers
            let account_rlc = DataTransition::new_with_rot(meta, accs.acc_s.rlc, rot_key, 0);
            let mult_prev = a!(accs.acc_s.mult, rot_key);
            // Multipliers
            let mult_after_nonce = a!(accs.acc_c.mult);
            let mult_diff_balance = a!(accs.key.mult);
            let acc_mult_final = a!(accs.acc_s.mult);
            require!(mult_after_nonce => mult_prev.expr() * mult_diff_nonce.expr());
            require!(acc_mult_final => mult_after_nonce.expr() * mult_diff_balance.expr());
            // Store the RLP bytes + nonce + balance RLC.
            let rlc = account_rlc.prev()
                + account.nonce_balance_rlc(
                    meta,
                    nonce_rlc.expr(),
                    balance_rlc.expr(),
                    mult_prev.expr(),
                    mult_diff_nonce.expr(),
                    0,
                );
            require!(account_rlc => rlc);

            // Check the RLP encoding consistency.
            // RlP encoding: account = [key, [nonce, balance, storage, codehash]]
            // The only exception is when `is_non_existing_account_proof = 1` &
            // `is_wrong_leaf = 0`. In this case the value does not matter as
            // the account leaf is only a placeholder and does not use
            // `s_main.rlp1` and `s_main.rlp2`.
            //  TODO(Brecht): Can we remove this if by just making this pass in this special
            // case?
            ifx! {not!(and::expr(&[a!(proof_type.is_non_existing_account_proof), not!(account.is_wrong_leaf(meta, is_s))])) => {
                // We always store between 55 and 256 bytes of data in the values list.
                require!(a!(s_main.rlp1) => RLP_LONG + 1);
                // The RLP encoded list always has 2 RLP bytes (the c RLP bytes).
                require!(a!(s_main.rlp2) => a!(c_main.rlp2) + 2.expr());
                // `c_main.rlp1` always needs to be RLP_LIST_LONG + 1.
                require!(a!(c_main.rlp1) => RLP_LIST_LONG + 1);
                // The length of the list is `#(nonce bytes) + #(balance bytes) + 2 * (1 + #(hash))`.
                require!(a!(c_main.rlp2) => nonce_num_bytes.expr() + balance_num_bytes.expr() + (2 * (1 + 32)).expr());
                // Now check that the the key and value list length matches the account length.
                let len = account.num_bytes(meta);
                let key_num_bytes = account.num_bytes_on_key_row(meta);
                // The RLP encoded string always has 2 RLP bytes (the s RLP bytes).
                let value_list_num_bytes = a!(s_main.rlp2) + 2.expr();
                // Account length needs to equal all key bytes and all values list bytes.
                require!(len => key_num_bytes + value_list_num_bytes);
            }}

            // To enable lookups for balance modification we need to have S balance and C
            // balance in the same row.
            if is_s {
                require!(a!(value_prev) => nonce);
            } else {
                require!(a!(value, rot_s) => nonce);
                require!(a!(value_prev) => balance.prev());
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
