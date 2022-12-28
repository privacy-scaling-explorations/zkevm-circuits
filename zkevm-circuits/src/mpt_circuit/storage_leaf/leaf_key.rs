use gadgets::util::{and, not, select, Expr};
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Region, Value},
    plonk::VirtualCells,
    poly::Rotation,
};
use std::marker::PhantomData;

use crate::{
    constraints,
    evm_circuit::util::rlc,
    mpt_circuit::{helpers::extend_rand, FixedTableTag},
    mpt_circuit::{
        helpers::BaseConstraintBuilder,
        param::{
            BRANCH_ROWS_NUM, IS_BRANCH_C16_POS, IS_BRANCH_C1_POS, IS_BRANCH_C_PLACEHOLDER_POS,
            IS_BRANCH_S_PLACEHOLDER_POS, NIBBLES_COUNTER_POS, RLP_NUM, S_START,
        },
    },
    mpt_circuit::{
        witness_row::{MptWitnessRow, MptWitnessRowType},
        MPTContext,
    },
    mpt_circuit::{MPTConfig, ProofValues},
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
[226 160 59 138 106 70 105 186 37 13 38 205 122 69 158 202 157 33 95 131 7 227 58 235 229 3 121 188 90 54 23 236 52 68 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 2]
[1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 13]
[226 160 59 138 106 70 105 186 37 13 38 205 122 69 158 202 157 33 95 131 7 227 58 235 229 3 121 188 90 54 23 236 52 68 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 3]
[17 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 14]
[0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 15]
[0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 19]

In the above example the value has been changed from 1 (`LEAF_VALUE_S`) to 17 (`LEAF_VALUE_C`).

In the example below the value in `LEAF_VALUE_C` takes more than 1 byte: `[187 239 170 ...]`
This has two consequences:
 - Two additional RLP bytes: `[161 160]` where `33 = 161 - 128` means there are `31` bytes behind `161`,
   `32 = 160 - 128` means there are `30` bytes behind `160`.
 - `LEAF_KEY_S` starts with `248` because the leaf has more than 55 bytes, `1 = 248 - 247` means
   there is 1 byte after `248` which specifies the length - the length is `67`. We can see that
   that the leaf key is shifted by 1 position compared to the example above.

For this reason we need to distinguish two cases: 1 byte in leaf value, more than 1 byte in leaf value.
These two cases are denoted by `is_short` and `is_long`. There are two other cases we need to
distinguish: `last_level` when the leaf is in the last level and has no nibbles, `one_nibble` when
the leaf has only one nibble.

`is_long`:
[226 160 59 138 106 70 105 186 37 13 38 205 122 69 158 202 157 33 95 131 7 227 58 235 229 3 121 188 90 54 23 236 52 68 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 2]
[1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 13]
[248 67 160 59 138 106 70 105 186 37 13 38 205 122 69 158 202 157 33 95 131 7 227 58 235 229 3 121 188 90 54 23 236 52 68 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 3]
[161 160 187 239 170 18 88 1 56 188 38 60 149 117 120 38 223 78 36 235 129 201 170 170 170 170 170 170 170 170 170 170 170 170 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 14]
[0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 15]
[0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 19]

`last_level`
[194 32 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 2]
[1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 13]
[194 32 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 3]
[17 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 14]
[0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 15]
[0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 19]

`one_nibble`:
[194 48 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 2]
[1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 13]
[194 48 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 3]
[17 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 14]
[0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 15]
[0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 19]

`s_mod_node_rlc` (`flag1`) and `c_mod_node_rlc` (`flag2`) columns store the information of what
kind of case we have:
 `flag1: 1, flag2: 0`: `is_long`
 `flag1: 0, flag2: 1`: `is_short`
 `flag1: 1, flag2: 1`: `last_level`
 `flag1: 0, flag0: 1`: `one_nibble`

The constraints in `leaf_key.rs` apply to `LEAF_KEY_S` and `LEAF_KEY_C` rows.
*/

#[derive(Clone, Debug, Default)]
pub(crate) struct LeafKeyConfig<F> {
    _marker: PhantomData<F>,
}

impl<F: FieldExt> LeafKeyConfig<F> {
    pub fn configure(
        meta: &mut VirtualCells<'_, F>,
        cb: &mut BaseConstraintBuilder<F>,
        ctx: MPTContext<F>,
        is_s: bool,
    ) -> Self {
        let s_main = ctx.s_main;
        let c_main = ctx.c_main;
        let accs = ctx.accumulators;
        let is_account_leaf_in_added_branch = ctx.account_leaf.is_in_added_branch;
        let denoter = ctx.denoter;
        let r = ctx.r;

        let rot_into_init = if is_s { -19 } else { -21 };
        let rot_into_account = if is_s { -1 } else { -3 };

        constraints! {[meta, cb], {
            let flag1 = a!(accs.s_mod_node_rlc);
            let flag2 = a!(accs.c_mod_node_rlc);
            let last_level = flag1.clone() * flag2.clone();
            let one_nibble = not::expr(flag1.clone()) * not::expr(flag2.clone());
            let is_long = flag1.clone() * not::expr(flag2.clone());
            let is_short = not::expr(flag1.clone()) * flag2.clone();

            // The two values that store the information about what kind of case we have need to be boolean.
            require!(flag1 => bool);
            require!(flag2 => bool);

            /* Storage leaf key RLC */
            // Checking the leaf RLC is ok - this value is then taken in the next row, where
            // leaf value is added to the RLC. Finally, the lookup is used to check the hash that
            // corresponds to the RLC is in the parent branch.

            let is_leaf_in_first_storage_level = a!(is_account_leaf_in_added_branch, rot_into_account);
            let sel = a!(if is_s {denoter.sel1} else {denoter.sel2}, rot_into_init + 1);

            let is_leaf_in_first_level = a!(if is_s {denoter.sel1} else {denoter.sel2}, 1);
            let is_leaf_placeholder = is_leaf_in_first_level + selectx!{not::expr(is_leaf_in_first_storage_level.expr()) => {sel}};

            ifx!{not::expr(is_leaf_placeholder.expr()) => {
                // When `is_long` (the leaf value is longer than 1 byte), `s_main.rlp1` needs to be 248.
                // Example:
                // `[248 67 160 59 138 106 70 105 186 37 13 38 205 122 69 158 202 157 33 95 131 7 227 58 235 229 3 121 188 90 54 23 236 52 68 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 3]`
                ifx!{is_long => {
                    require!(a!(s_main.rlp1) => 248);
                }}

                // When `last_level`, there is no nibble stored in the leaf key, it is just the value
                // `32` in `s_main.rlp2`. In the `getProof` output, there is then the value stored immediately
                // after `32`. However, in the MPT witness, we have value in the next row, so there are 0s
                // in `s_main.bytes` (we do not need to check `s_main.bytes[i]` to be 0 due to how the RLC
                // constraints are written).
                // Example:
                // `[194 32 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 3]`
                ifx!{last_level => {
                    require!(a!(s_main.rlp2) => 32);
                }}

                // We need to ensure that the RLC of the row is computed properly for `is_short` and
                // `is_long`. We compare the computed value with the value stored in `accumulators.acc_s.rlc`.
                ifx!{is_short.expr() + is_long.expr() => {
                    // c_rlp2 can appear if long and if no branch above leaf
                    let rlc = rlc::expr(
                        &[s_main.rlp_bytes(), c_main.rlp_bytes()].concat()[..36].iter().map(|&byte| a!(byte)).collect::<Vec<_>>(),
                        &(extend_rand(&r)),
                    );
                    require!(a!(accs.acc_s.rlc) => rlc);
                }}

                // We need to ensure that the RLC of the row is computed properly for `last_level` and
                // `one_nibble`. We compare the computed value with the value stored in `accumulators.acc_s.rlc`.
                // `last_level` and `one_nibble` cases have one RLP byte (`s_rlp1`) and one byte (`s_rlp2`)
                // where it is 32 (for `last_level`) or `48 + last_nibble` (for `one_nibble`).
                ifx!{last_level.expr() + one_nibble.expr() => {
                    // If leaf in last level, it contains only s_rlp1 and s_rlp2, while s_main.bytes are 0.
                    let rlc_last_level_or_one_nibble = rlc::expr(
                        &[s_main.rlp_bytes(), c_main.rlp_bytes()].concat()[..2].iter().map(|&byte| a!(byte)).collect::<Vec<_>>(),
                        &r,
                    );
                    require!(a!(accs.acc_s.rlc) => rlc_last_level_or_one_nibble);
                }}

                /* Storage leaf key RLC & nibbles count (branch not placeholder) */
                // We need to ensure that the storage leaf is at the key specified in `key_rlc` column (used
                // by MPT lookup). To do this we take the key RLC computed in the branches above the leaf
                // and add the remaining bytes (nibbles) stored in the leaf.

                // We also ensure that the number of all nibbles (in branches / extension nodes above
                // the leaf and in the leaf) is 64.

                // `key_rlc_acc_start = 0` if leaf in first storage level
                // `key_mult_start = 1` if leaf in first storage level
                // key rlc is in the first branch node (not branch init)
                let rot = if is_s {-18} else {-20};
                let key_rlc_acc_start = selectx!{not::expr(is_leaf_in_first_storage_level.expr()) => {a!(accs.key.rlc, rot)}};
                let key_mult_start = selectx!{not::expr(is_leaf_in_first_storage_level.expr()) => {
                    a!(accs.key.mult, rot)
                } elsex {
                    1
                }};

                // `c16` and `c1` specify whether in the branch above the leaf the `modified_nibble`
                // had to be multiplied by 16 or by 1 for the computation the key RLC.
                // `c16 = 0, c1 = 1` if leaf in first storage level, because we do not have the branch above
                // and we need to multiply the first nibble by 16 (as it would be `c1` in the branch above)
                let is_c16 = selectx!{not::expr(is_leaf_in_first_storage_level.expr()) => {a!(s_main.bytes[IS_BRANCH_C16_POS - RLP_NUM], rot_into_init)}};
                let is_c1 = selectx!{not::expr(is_leaf_in_first_storage_level.expr()) => {
                    a!(s_main.bytes[IS_BRANCH_C1_POS - RLP_NUM], rot_into_init)
                } elsex {
                    1
                }};

                // `is_branch_placeholder = 0` when in first level
                let pos = if is_s {IS_BRANCH_S_PLACEHOLDER_POS} else {IS_BRANCH_C_PLACEHOLDER_POS};
                let is_branch_placeholder = selectx!{not::expr(is_leaf_in_first_storage_level.expr()) => {a!(s_main.bytes[pos - RLP_NUM], rot_into_init)}};

                // If the last branch is placeholder (the placeholder branch is the same as its
                // parallel counterpart), there is a branch `modified_node` nibble already
                // incorporated in `key_rlc`. That means we need to ignore the first nibble here
                // (in leaf key).

                ifx!{not::expr(is_leaf_placeholder.expr()), not::expr(is_branch_placeholder.expr()) => {
                    // Set to key_mult_start * r if is_c16, else key_mult_start
                    let key_mult = key_mult_start.clone() * selectx!{is_c16 => {
                        r[0].clone()
                    } elsex {
                        1
                    }};

                    ifx!{is_short => {
                        // If `is_c1` and branch above is not a placeholder, we have 32 in `s_main.bytes[0]`.
                        // This is because `is_c1` in the branch above means there is an even number of nibbles left
                        // and we have an even number of nibbles in the leaf, the first byte (after RLP bytes
                        // specifying the length) of the key is 32.
                        ifx!{is_c1 => {
                            require!(a!(s_main.bytes[0]) => 32);
                        }}

                        // We need to ensure the leaf key RLC is computed properly. We take the key RLC value
                        // from the last branch and add the bytes from position
                        // `s_main.bytes[0]` up at most to `c_main.rlp1`. We need to ensure that there are 0s
                        // after the last key byte, this is done by `key_len_lookup`.
                        // The computed value needs to be the same as the value stored `key_rlc` column.
                        // `is_short` example:
                        // [226,160,59,138,106,70,105,186,37,13,38[227,32,161,160,187,239,170,18,88,1,56,188,38,60,149,117,120,38,223,78,36,235,129,201,170,170,170,170,170,170,170,170,170,170,170,170]
                        // Note: No need to distinguish between `c16` and `c1` here as it was already
                        // when computing `key_rlc_acc_short`.

                        // If sel1 = 1, we have nibble+48 in s_main.bytes[0].
                        // c_rlp1 can appear if no branch above the leaf
                        let key_rlc = key_rlc_acc_start.expr() + rlc::expr(
                            &[s_main.rlp_bytes(), c_main.rlp_bytes()].concat()[2..35].iter().enumerate().map(|(idx, &byte)|
                                (if idx == 0 { (a!(byte) - 48.expr()) * is_c16.expr() * key_mult_start.expr() } else { a!(byte) * key_mult.expr() })).collect::<Vec<_>>(),
                            &[[1.expr()].to_vec(), r.to_vec()].concat(),
                        );
                        require!(a!(accs.key.rlc) => key_rlc);
                    }}

                    // For long RLP (key starts at `s_main.bytes[1]`):
                    ifx!{is_long => {
                        // If `is_c1` and branch above is not a placeholder, we have 32 in `s_main.bytes[1]`.
                        // This is because `is_c1` in the branch above means there is an even number of nibbles left
                        // and we have an even number of nibbles in the leaf, the first byte (after RLP bytes
                        // specifying the length) of the key is 32.
                        ifx!{is_c1 => {
                            require!(a!(s_main.bytes[1]) => 32);
                        }}

                        // We need to ensure the leaf key RLC is computed properly. We take the key RLC value
                        // from the last branch and add the bytes from position
                        // `s_main.bytes[1]` up at most to `c_main.rlp2`. We need to ensure that there are 0s
                        // after the last key byte, this is done by `key_len_lookup`.
                        // The computed value needs to be the same as the value stored `key_rlc` column.
                        // `is_long` example:
                        // `[248,67,160,59,138,106,70,105,186,37,13,38,205,122,69,158,202,157,33,95,131,7,227,58,235,229,3,121,188,90,54,23,236,52,68,161,160,...`
                        // Note: No need to distinguish between `c16` and `c1` here as it was already
                        // when computing `key_rlc_acc_long`.
                        // If `is_c16`, we have nibble+48 in `s_main.bytes[1]`.
                        let key_rlc = key_rlc_acc_start.expr() + rlc::expr(
                            &[s_main.rlp_bytes(), c_main.rlp_bytes()].concat()[3..36].iter().enumerate().map(|(idx, &byte)|
                                (if idx == 0 { (a!(byte) - 48.expr()) * is_c16.expr() * key_mult_start.expr() } else { a!(byte) * key_mult.expr() })).collect::<Vec<_>>(),
                            &[[1.expr()].to_vec(), r.to_vec()].concat(),
                        );
                        require!(a!(accs.key.rlc) => key_rlc);
                    }}

                    ifx!{last_level => {
                        // When the leaf is in the last level there are no nibbles stored in the key and
                        // `s_main.rlp2 = 32`.
                        require!(a!(s_main.rlp2) => 32);

                        // We need to ensure the leaf key RLC is computed properly.
                        // When the leaf is in the last level we simply take the key RLC value
                        // from the last branch and this is the final key RLC value as there is no
                        // nibble in the leaf.
                        // The computed value needs to be the same as the value stored `key_rlc` column.
                        // Last level example:
                        // `[227,32,161,160,187,239,170,18,88,1,56,188,38,60,149,117,120,38,223,78,36,235,129,201,170,170,170,170,170,170,170,170,170,170,170,170]`
                        require!(a!(accs.key.rlc) => key_rlc_acc_start);
                    }}

                    // We need to ensure the leaf key RLC is computed properly.
                    // When there is only one nibble in the leaf, we take the key RLC value
                    // from the last branch and add the last remaining nibble stored in `s_main.rlp2`.
                    // The computed value needs to be the same as the value stored `key_rlc` column.
                    // One nibble example short value:
                    // `[194,48,1]`
                    // One nibble example long value:
                    // `[227,48,161,160,187,239,170,18,88,1,56,188,38,60,149,117,120,38,223,78,36,235,129,201,170,170,170,170,170,170,170,170,170,170,170,170]`
                    ifx!{one_nibble => {
                        let key_rlc = key_rlc_acc_start.expr() + (a!(s_main.rlp2) - 48.expr()) * key_mult_start;
                        require!(a!(accs.key.rlc) => key_rlc);
                    }}

                    // Checking the total number of nibbles is to prevent having short addresses
                    // which could lead to a root node which would be shorter than 32 bytes and thus not hashed. That
                    // means the trie could be manipulated to reach a desired root.
                    let leaf_nibbles_long = selectx!{is_c1 => {
                        (a!(s_main.bytes[0])- 128.expr() - 1.expr()) * 2.expr()
                    } elsex {
                        (a!(s_main.bytes[0])- 128.expr()) * 2.expr() - 1.expr()
                    }};
                    let leaf_nibbles_short = selectx!{is_c1 => {
                        (a!(s_main.rlp2) - 128.expr() - 1.expr()) * 2.expr()
                    } elsex {
                        (a!(s_main.rlp2) - 128.expr()) * 2.expr() - 1.expr()
                    }};
                    let leaf_nibbles_last_level = 0.expr();
                    let leaf_nibbles_one_nibble = 1.expr();
                    let leaf_nibbles = leaf_nibbles_long * is_long.expr() + leaf_nibbles_short * is_short.expr()
                        + leaf_nibbles_last_level * last_level.expr() + leaf_nibbles_one_nibble * one_nibble.expr();
                    let nibbles_count = selectx!{not::expr(is_leaf_in_first_storage_level.expr()) => {
                        a!(s_main.bytes[NIBBLES_COUNTER_POS - RLP_NUM], rot_into_init)
                    }};
                    require!(nibbles_count + leaf_nibbles => 64);
                }}

                /* Storage leaf key RLC (after placeholder) */
                // For leaf under the placeholder branch we would not need to check the key RLC -
                // this leaf is something we did not ask for, it is just a leaf that happened to be
                // at the place where adding a new leaf causes adding a new branch.
                // For example, when adding a leaf `L` causes that a leaf `L1`
                // (this will be the leaf under the branch placeholder)
                // is replaced by a branch, we get a placeholder branch at `S` side
                // and leaf `L1` under it. However, the key RLC needs to be compared for leaf `L`,
                // because this is where the modification takes place.
                // In delete, the situation is turned around.

                // However, we also check that the key RLC for `L1` is computed properly because
                // we need `L1` key RLC for the constraints for checking that leaf `L1` is the same
                // as the drifted leaf in the branch parallel. This can be checked by
                // comparing the key RLC of the leaf before being replaced by branch and the key RLC
                // of this same leaf after it drifted into a branch.
                // Constraints for this are in `leaf_key_in_added_branch.rs`.

                // Note that the hash of a leaf `L1` needs to be checked to be in the branch
                // above the placeholder branch - this is checked in `leaf_value.rs`.

                // Note: `last_level` cannot occur in a leaf after placeholder branch, because being
                // after placeholder branch means this leaf drifted down into a new branch (in a parallel
                // proof) and thus cannot be in the last level.

                let is_first_storage_level = a!(is_account_leaf_in_added_branch, rot_into_init - 1);
                let is_leaf_in_first_level = a!(is_account_leaf_in_added_branch, rot_into_account);

                let pos = if is_s {IS_BRANCH_S_PLACEHOLDER_POS} else {IS_BRANCH_C_PLACEHOLDER_POS};
                let is_branch_placeholder = a!(s_main.bytes[pos - RLP_NUM], rot_into_init);

                // Note: key RLC is in the first branch node (not branch init).
                let rot_level_above = rot_into_init + 1 - BRANCH_ROWS_NUM;

                // Retrieve the key RLC and multiplier from above the placeholder branch.
                let key_rlc_acc_start = selectx!{not::expr(is_first_storage_level.expr()) => {a!(accs.key.rlc, rot_level_above)}};
                let key_mult_start = selectx!{not::expr(is_first_storage_level.expr()) => {
                    a!(accs.key.mult, rot_level_above)
                } elsex {
                    1
                }};

                // Note that when `is_first_storage_level`, it is always `is_c1 = 1` because
                // there are all 32 bytes in a key.
                let is_c16 = selectx!{not::expr(is_first_storage_level.expr()) => {a!(s_main.bytes[IS_BRANCH_C16_POS - RLP_NUM], rot_level_above - 1)}};
                let is_c1 = selectx!{not::expr(is_first_storage_level.expr()) => {
                    a!(s_main.bytes[IS_BRANCH_C1_POS - RLP_NUM], rot_level_above - 1)
                } elsex {
                    1
                }};

                ifx!{is_branch_placeholder, not::expr(is_leaf_in_first_level.expr()) => {
                    // Set to key_mult_start if sel2, stays key_mult if sel1
                    let key_mult = key_mult_start.clone() * selectx!{is_c16 => {
                        r[0].clone()
                    } elsex {
                        1
                    }};

                    ifx!{is_short => {
                        // If `is_c1 = 1` which means there is an even number of nibbles stored in a leaf,
                        // we have 32 in `s_main.bytes[0]`.
                        ifx!{is_c1 => {
                            require!(a!(s_main.bytes[0]) => 32);
                        }}

                        // When `is_short` the first key byte is at `s_main.bytes[0]`. We retrieve the key RLC from the
                        // branch above the branch placeholder and add the nibbles stored in a leaf.
                        // The computed key RLC needs to be the same as the value stored at `accumulators.key.rlc`.
                        // `is_short`:
                        // `[226 160 59 138 106 70 105 186 37 13 38 205 122 69 158 202 157 33 95 131 7 227 58 235 229 3 121 188 90 54 23 236 52 68 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 2]`
                        // `is_long`:
                        // `[248 67 160 59 138 106 70 105 186 37 13 38 205 122 69 158 202 157 33 95 131 7 227 58 235 229 3 121 188 90 54 23 236 52 68 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 3]`
                        // Note: No need to distinguish between `is_c16` and `is_c1` here as it was already
                        // when computing `key_rlc_acc_short`.
                        // If `is_c16 = 1`, we have one nibble+48 in `s_main.bytes[0]`.
                        let key_rlc = key_rlc_acc_start.expr() + rlc::expr(
                            &[s_main.rlp_bytes(), c_main.rlp_bytes()].concat()[2..35].iter().enumerate().map(|(idx, &byte)|
                                (if idx == 0 { (a!(byte) - 48.expr()) * is_c16.expr() * key_mult_start.expr() } else { a!(byte) * key_mult.expr() })).collect::<Vec<_>>(),
                            &[[1.expr()].to_vec(), r.to_vec()].concat(),
                        );
                        require!(a!(accs.key.rlc) => key_rlc);
                    }}

                    ifx!{is_long => {
                        // If `is_c1 = 1` which means there is an even number of nibbles stored in a leaf,
                        // we have 32 in `s_main.bytes[1]`.
                        ifx!{is_c1 => {
                            require!(a!(s_main.bytes[1]) => 32);
                        }}

                        // When `is_long` the first key byte is at `s_main.bytes[1]`. We retrieve the key RLC from the
                        // branch above the branch placeholder and add the nibbles stored in a leaf.
                        // The computed key RLC needs to be the same as the value stored at `accumulators.key.rlc`.
                        // `is_short`:
                        // `[226 160 59 138 106 70 105 186 37 13 38 205 122 69 158 202 157 33 95 131 7 227 58 235 229 3 121 188 90 54 23 236 52 68 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 2]`
                        // `is_long`:
                        // `[248 67 160 59 138 106 70 105 186 37 13 38 205 122 69 158 202 157 33 95 131 7 227 58 235 229 3 121 188 90 54 23 236 52 68 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 3]`
                        // No need to distinguish between `is_c16` and `is_c1` here as it was already
                        // when computing `key_rlc_acc_long`.
                        // If `is_c16 = 1`, we have nibble+48 in `s_main.bytes[1]`.
                        let key_rlc = key_rlc_acc_start.expr() + rlc::expr(
                            &[s_main.rlp_bytes(), c_main.rlp_bytes()].concat()[3..36].iter().enumerate().map(|(idx, &byte)|
                                (if idx == 0 { (a!(byte) - 48.expr()) * is_c16.expr() * key_mult_start.expr() } else { a!(byte) * key_mult.expr() })).collect::<Vec<_>>(),
                            &[[1.expr()].to_vec(), r.to_vec()].concat(),
                        );
                        require!(a!(accs.key.rlc) => key_rlc);
                    }}

                    // Note: When the leaf is after the placeholder branch, it cannot be in the last level
                    // otherwise it would not be possible to add a branch placeholder.

                    // Checking the total number of nibbles is to prevent having short addresses
                    // which could lead to a root node which would be shorter than 32 bytes and thus not hashed. That
                    // means the trie could be manipulated to reach a desired root.
                    // To get the number of nibbles above the leaf we need to go into the branch above the placeholder branch.
                    // Note that when the leaf is in the first storage level (but positioned after the placeholder
                    // in the circuit), there is no branch above the placeholder branch from where
                    // `nibbles_count` is to be retrieved. In that case `nibbles_count = 0`.
                    let leaf_nibbles_long = selectx!{is_c1 => {
                        (a!(s_main.bytes[0])- 128.expr() - 1.expr()) * 2.expr()
                    } elsex {
                        (a!(s_main.bytes[0])- 128.expr()) * 2.expr() - 1.expr()
                    }};
                    let leaf_nibbles_short = selectx!{is_c1 => {
                        (a!(s_main.rlp2) - 128.expr() - 1.expr()) * 2.expr()
                    } elsex {
                        (a!(s_main.rlp2) - 128.expr()) * 2.expr() - 1.expr()
                    }};
                    let leaf_nibbles_last_level = 0.expr();
                    let leaf_nibbles_one_nibble = 1.expr();
                    let leaf_nibbles = leaf_nibbles_long * is_long.expr() + leaf_nibbles_short * is_short.expr()
                        + leaf_nibbles_last_level * last_level.expr() + leaf_nibbles_one_nibble * one_nibble.expr();
                    let nibbles_count = selectx!{not::expr(is_first_storage_level.expr()) => {
                        a!(s_main.bytes[NIBBLES_COUNTER_POS - RLP_NUM], rot_into_init - BRANCH_ROWS_NUM)
                    }};
                    require!(nibbles_count + leaf_nibbles => 64);
                }}
            }}

            // RLC bytes zero check
            // There are 0s in `s_main.bytes` after the last key nibble (this does not need to be checked
            // for `last_level` and `one_nibble` as in these cases `s_main.bytes` are not used).
            ifx!{is_short => {
                require!((FixedTableTag::RMult, a!(s_main.rlp2) - 128.expr() + 2.expr(), a!(accs.acc_s.mult)) => @fixed);

                for (idx, &byte) in [s_main.rlp_bytes(), c_main.rlp_bytes()].concat()[2..35].into_iter().enumerate() {
                    require!((FixedTableTag::RangeKeyLen256, a!(byte) * (a!(s_main.rlp2) - 128.expr() - (idx + 1).expr())) => @fixed);
                }
            }}
            ifx!{is_long => {
                require!((FixedTableTag::RMult, a!(s_main.bytes[0]) - 128.expr() + 3.expr(), a!(accs.acc_s.mult)) => @fixed);

                for (idx, &byte) in [s_main.rlp_bytes(), c_main.rlp_bytes()].concat()[3..36].into_iter().enumerate() {
                    require!((FixedTableTag::RangeKeyLen256, a!(byte) * (a!(s_main.bytes[0]) - 128.expr() - (idx + 1).expr())) => @fixed);
                }
            }}
        }}

        LeafKeyConfig {
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
        /*
        getProof storage leaf examples:
            short (one RLP byte > 128: 160):
            [226,160,59,138,106,70,105,186,37,13,38,205,122,69,158,202,157,33,95,131,7,227,58,235,229,3,121,188,90,54,23,236,52,68,1]

            long (two RLP bytes: 67, 160):
            [248,67,160,59,138,106,70,105,186,37,13,38,205,122,69,158,202,157,33,95,131,7,227,58,235,229,3,121,188,90,54,23,236,52,68,161,160,187,239,170,18,88,1,56,188,38,60,149,117,120,38,223,78,36,235,129,201,170,170,170,170,170,17

            last_level (one RLP byte: 32)
            32 at position 1 means there are no key nibbles (last level):
            [227,32,161,160,187,239,170,18,88,1,56,188,38,60,149,117,120,38,223,78,36,235,129,201,170,170,170,170,170,170,170,170,170,170,170,170]
            [194,32,1]

            this one falls into short again:
            [196,130,32,0,1]
        */

        /*
        Info whether leaf rlp is long or short:
         - long means the key length is at position 2.
         - short means the key length is at position 1.
        */
        let mut typ = "short";
        if row.get_byte(0) == 248 {
            typ = "long";
        } else if row.get_byte(1) == 32 {
            typ = "last_level";
        } else if row.get_byte(1) < 128 {
            typ = "one_nibble";
        }
        mpt_config.assign_long_short(region, typ, offset).ok();

        pv.acc_s = F::zero();
        pv.acc_mult_s = F::one();
        let len: usize;
        if typ == "long" {
            len = (row.get_byte(2) - 128) as usize + 3;
        } else if typ == "short" {
            len = (row.get_byte(1) - 128) as usize + 2;
        } else {
            // last_level or one_nibble
            len = 2
        }
        mpt_config.compute_acc_and_mult(&row.bytes, &mut pv.acc_s, &mut pv.acc_mult_s, 0, len);

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

        // note that this assignment needs to be after assign_acc call
        if row.get_byte(0) < 223 {
            // when shorter than 32 bytes, the node doesn't get hashed
            // not_hashed
            region
                .assign_advice(
                    || "assign not_hashed".to_string(),
                    mpt_config.accumulators.acc_c.rlc,
                    offset,
                    || Value::known(F::one()),
                )
                .ok();
        }

        // TODO: handle if branch or extension node is added
        let mut start = S_START - 1;
        if row.get_byte(0) == 248 {
            // long RLP
            start = S_START;
        }

        // For leaf S and leaf C we need to start with the same rlc.
        let mut key_rlc_new = pv.key_rlc;
        let mut key_rlc_mult_new = pv.key_rlc_mult;
        if (pv.is_branch_s_placeholder && row.get_type() == MptWitnessRowType::StorageLeafSKey)
            || (pv.is_branch_c_placeholder && row.get_type() == MptWitnessRowType::StorageLeafCKey)
        {
            key_rlc_new = pv.key_rlc_prev;
            key_rlc_mult_new = pv.key_rlc_mult_prev;
        }
        if typ != "last_level" && typ != "one_nibble" {
            // If in last level or having only one nibble,
            // the key RLC is already computed using the first two bytes above.
            mpt_config.compute_key_rlc(&row.bytes, &mut key_rlc_new, &mut key_rlc_mult_new, start);
        }
        region
            .assign_advice(
                || "assign key_rlc".to_string(),
                mpt_config.accumulators.key.rlc,
                offset,
                || Value::known(key_rlc_new),
            )
            .ok();

        // Store key_rlc into rlc2 to be later set in leaf value C row (to enable
        // lookups):
        pv.rlc2 = key_rlc_new;
    }
}
