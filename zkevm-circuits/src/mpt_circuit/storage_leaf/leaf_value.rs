use gadgets::util::{and, not, Expr};
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Region, Value},
    plonk::{Advice, Column, Expression, Fixed, VirtualCells},
    poly::Rotation,
};
use std::marker::PhantomData;

use crate::{
    constraints,
    evm_circuit::util::rlc,
    mpt_circuit::columns::{AccumulatorCols, DenoteCols, MainCols, PositionCols},
    mpt_circuit::{
        columns::ProofTypeCols,
        helpers::{get_leaf_len, key_len_lookup, BaseConstraintBuilder},
        param::{
            ACCOUNT_LEAF_ROWS, ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND,
            ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND, BRANCH_ROWS_NUM, HASH_WIDTH,
            IS_BRANCH_C_PLACEHOLDER_POS, IS_BRANCH_S_PLACEHOLDER_POS, IS_STORAGE_MOD_POS,
            LEAF_NON_EXISTING_IND, LEAF_VALUE_C_IND, LEAF_VALUE_S_IND, RLP_NUM,
        },
        MPTContext,
    },
    mpt_circuit::{
        helpers::extend_rand,
        witness_row::{MptWitnessRow, MptWitnessRowType},
    },
    mpt_circuit::{MPTConfig, ProofValues},
    table::KeccakTable,
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

`is_long` (`C` is long, while `S` is short):
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

The constraints in `leaf_value.rs` apply to `LEAF_VALUE_S` and `LEAF_VALUE_C` rows.
The constraints ensure the hash of a storage leaf is in a parent branch and that the RLP
of the leaf is correct.

Lookups:
The `is_storage_mod` lookup is enabled in `LEAF_VALUE_C` row.

Note that there are no checks for example for the root as the constraints to ensure `start_root`
and `final_root` does not change (except in the first row of the modification) are in `proof_chain.rs`
and the constraints to ensure the lookup roots correspond to the roots of the trie are in the first
level nodes (`account_leaf_storage_codehash.rs` or `branch_hash_in_parent.rs`).
*/

#[derive(Clone, Debug, Default)]
pub(crate) struct LeafValueConfig<F> {
    _marker: PhantomData<F>,
}

impl<F: FieldExt> LeafValueConfig<F> {
    pub fn configure(
        meta: &mut VirtualCells<'_, F>,
        cb: &mut BaseConstraintBuilder<F>,
        ctx: MPTContext<F>,
        is_s: bool,
    ) -> Self {
        let proof_type = ctx.proof_type;
        let position_cols = ctx.position_cols;
        let is_leaf_value = if is_s {
            ctx.storage_leaf.is_s_value
        } else {
            ctx.storage_leaf.is_c_value
        };
        let s_main = ctx.s_main;
        // key_rlc_mult (accs.key.mult) to store key_rlc from previous row (to enable
        // lookup)
        let accs = ctx.accumulators;
        let denoter = ctx.denoter;
        let is_account_leaf_in_added_branch = ctx.account_leaf.is_in_added_branch;
        let value_prev = ctx.value_prev;
        let value = ctx.value;
        let r = ctx.r;

        // A rotation into any branch child is ok as `s_mod_node_hash_rlc` and
        // `c_mod_node_hash_rlc` are the same in all branch children.
        let rot_into_branch = -6;
        let rot_into_init = -LEAF_VALUE_S_IND - BRANCH_ROWS_NUM - if is_s { 0 } else { 2 };
        let rot_into_account = if is_s {
            -LEAF_VALUE_S_IND
        } else {
            -LEAF_VALUE_C_IND
        } - 1;

        constraints! {[meta, cb], {
            let q_not_first = f!(position_cols.q_not_first);
            let not_first_level = a!(position_cols.not_first_level);
            let is_leaf = a!(is_leaf_value);
            let q_enable = q_not_first.expr() * is_leaf.expr();

            let is_long = a!(accs.s_mod_node_rlc);
            let is_short = a!(accs.c_mod_node_rlc);
            let flag1 = a!(accs.s_mod_node_rlc, -1);
            let flag2 = a!(accs.c_mod_node_rlc, -1);
            let last_level = flag1.expr() * flag2.expr();
            let one_nibble = not::expr(flag1.expr()) * not::expr(flag2.expr());
            let is_leaf_long = flag1.expr() * not::expr(flag2.expr());
            let is_leaf_short = not::expr(flag1.expr()) * flag2.expr();

            let sel = meta.query_advice(if is_s {denoter.sel1} else {denoter.sel2}, Rotation(rot_into_branch));

            let is_placeholder_without_branch = a!(if is_s {denoter.sel1} else {denoter.sel2});
            let is_account_leaf_above = a!(is_account_leaf_in_added_branch, rot_into_account);
            let is_leaf_placeholder = is_placeholder_without_branch.expr() + not::expr(is_account_leaf_above.expr()) * sel.expr();

            ifx!{q_enable => {
                /* Leaf & leaf value RLC */
                // We need the RLC of the whole leaf for a lookup that ensures the leaf is in the parent branch.
                // We need the leaf value RLC for external lookups that ensure the value has been set correctly.

                // `is_short` means value has only one byte and consequently, the RLP of
                // the value is only this byte itself. If there are more bytes, the value is
                // equipped with two RLP meta bytes, like 161 160 if there is a
                // value of length 32 (the first RLP byte means 33 bytes after it, the second
                // RLP byte means 32 bytes after it).
                // `is_short` example:
                // `[1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 13]`
                // `is_long` example:
                // `[161 160 187 239 170 18 88 1 56 188 38 60 149 117 120 38 223 78 36 235 129 201 170 170 170 170 170 170 170 170 170 170 170 170 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 14]`

                // We need to ensure `is_long` and `is_short` are booleans and that `is_long + is_short = 1`.
                require!(is_short => bool);
                require!(is_long => bool);
                require!(is_short.expr() + is_long.expr() => 1);

                let leaf_rlc_prev = a!(accs.acc_s.rlc, -1);
                let leaf_mult_prev = a!(accs.acc_s.mult, -1);
                ifx!{is_short => {
                    // We need to ensure that the stored leaf value RLC is the same as the computed one.
                    require!(a!(accs.acc_c.rlc) => a!(s_main.rlp1));
                    // We need to ensure that the stored leaf RLC is the same as the computed one.
                    require!(a!(accs.acc_s.rlc) => leaf_rlc_prev.expr() + a!(s_main.rlp1) * leaf_mult_prev.expr());
                } elsex {
                    // We need to ensure that the stored leaf value RLC is the same as the computed one.
                    let value_rlc = rlc::expr(
                        &s_main.bytes.iter().map(|&byte| a!(byte)).collect::<Vec<_>>(),
                        &r,
                    );
                    require!(a!(accs.acc_c.rlc) => value_rlc);
                    // We need to ensure that the stored leaf RLC is the same as the computed one.
                    let leaf_rlc = leaf_rlc_prev.expr() + rlc::expr(
                        &[a!(s_main.rlp1), a!(s_main.rlp2), value_rlc].into_iter().map(|part| part * leaf_mult_prev.expr()).collect::<Vec<_>>(),
                        &r,
                    );
                    require!(a!(accs.acc_s.rlc) => leaf_rlc);
                }}

                if !is_s {
                    // To enable external lookups we need to have the following information in the same row:
                    //  - key RLC:                       we copy it to `accs.key.mult` column from the leaf key C row
                    //  - previous (`S`) leaf value RLC: we copy it to `value_prev` column from the leaf value `S` row
                    //  - current (`C`) leaf value RLC:  stored in `acc_c` column, we copy it to `value` column
                    require!(a!(accs.key.mult) => a!(accs.key.rlc, -1));
                    require!(a!(value_prev) => a!(accs.acc_c.rlc, -2));
                    require!(a!(accs.acc_c.rlc) => a!(value));
                }

                ifx!{sel, not::expr(is_account_leaf_above.expr()) => {
                    // `sel` column in branch children rows determines whether the `modified_node` is empty child.
                    // For example when adding a new storage leaf to the trie, we have an empty child in `S` proof
                    // and non-empty in `C` proof.
                    // When there is an empty child, we have a placeholder leaf under the last branch.
                    // If `sel = 1` which means an empty child, we need to ensure that the value is set to 0
                    // in the placeholder leaf.
                    // Note: For a leaf without a branch (means it is in the first level of the trie)
                    // the constraint is in `storage_root_in_account_leaf.rs`.
                    for byte in s_main.rlp_bytes().iter() {
                        require!(a!(*byte) => 0);
                    }
                }}

                // RLP constraints:
                ifx!{not::expr(is_leaf_placeholder.expr()) => {
                    let s_rlp1_prev = a!(s_main.rlp1, -1);
                    let s_rlp2_prev = a!(s_main.rlp2, -1);
                    let s_rlp2_cur = a!(s_main.rlp2);

                    let short_remainder = s_rlp1_prev.clone() - 192.expr() - s_rlp2_prev.clone() + 128.expr() - 1.expr();
                    let long_remainder = s_rlp2_prev - a!(s_main.bytes[0], -1) + 128.expr() - 1.expr();

                    // When the leaf is short (first key byte in `s_main.bytes[0]` in the leaf key row) and the value
                    // is short (first value byte in `s_main.rlp1` in the leaf value row), we need to check that:
                    // `s_rlp1_prev - 192 - s_rlp2_prev + 128 - 1 - 1 = 0`.
                    // The first `-1` presents the byte occupied by `s_rlp2_prev`.
                    // The second `-1` presents the length of the value which is 1 because the value is short in this case.
                    // Example:
                    // `[226 160 59 138 106 70 105 186 37 13 38 205 122 69 158 202 157 33 95 131 7 227 58 235 229 3 121 188 90 54 23 236 52 68 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 2]`

                    ifx!{is_short => {
                        // In the example: `34 = 226 - 192` gives the length of the RLP stream. `32 = 160 - 128` gives the length
                        // of the key. That means there are 34 bytes after the first byte, 32 of these are occupied by the key,
                        // 1 is occupied by `s_rlp2_prev`, and 1 is occupied by the value.
                        ifx!{is_leaf_short => {
                            require!(short_remainder => 1);
                        }}

                        // Note: long short is not possible because the key has at most 32 bytes and
                        // short value means only 1 byte which (together with RLP meta
                        // bytes) cannot go over 55 bytes.

                        // When the leaf is in the last level of the trie and the value is short,
                        // we need to ensure that `s_main.rlp2 = 32`.
                        // Note that in this case we do not have the length of the key stored in `s_main.rlp2` or `s_main.bytes[0]`.
                        // Example: `[194,32,1]`
                        ifx!{last_level.expr() + one_nibble.expr() => {
                            require!(s_rlp1_prev => 194.expr());
                        }}
                    }}

                    ifx!{is_long => {
                        // When the leaf is long (first key byte in `s_main.bytes[1]` in the leaf key row) and the value
                        // is long (first value byte in `s_main.bytes[0]` in the leaf value row), we need to check that:
                        // `s_rlp2_prev - s_bytes0_prev + 128 - 1 - (s_rlp2_cur - 128 + 1 + 1) = 0`.
                        // The expression `s_rlp2_prev - s_bytes0_prev + 128 - 1` gives us the number of bytes that are to be left
                        // in the value. The expression `s_rlp2_cur - 128 + 1 + 1` gives us the number of bytes in the leaf.
                        // Note that there is an additional constraint to ensure `s_main.rlp1 = s_main.rlp2 + 1`.
                        // Example:
                        // `[248 67 160 59 138 106 70 105 186 37 13 38 205 122 69 158 202 157 33 95 131 7 227 58 235 229 3 121 188 90 54 23 236 52 68 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 3]`
                        // `[161 160 187 239 170 18 88 1 56 188 38 60 149 117 120 38 223 78 36 235 129 201 170 170 170 170 170 170 170 170 170 170 170 170 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 14]`
                        let long_value_len = s_rlp2_cur.clone() - 128.expr() + 1.expr() + 1.expr();
                        // When the leaf is short (first key byte in `s_main.bytes[0]` in the leaf key row) and the value
                        // is long (first value byte in `s_main.bytes[0]` in the leaf value row), we need to check that:
                        // `s_rlp1_prev - 192 - s_rlp2_prev + 128 - 1 - (s_rlp2_cur - 128 + 1 + 1) = 0`.
                        // The expression `s_rlp1_prev - 192 - s_rlp2_prev + 128 - 1` gives us the number of bytes that are to be left
                        // in the value. The expression `s_rlp2_cur - 128 + 1 + 1` gives us the number of bytes in the leaf.
                        ifx!{is_leaf_short => {
                            require!(short_remainder => long_value_len);
                        }}
                        // 67 is the number of bytes after `s_main.rlp2`. `160 - 128 + 1` is the number of bytes that are occupied
                        // by the key and the byte that stores key length.
                        // In the next row, we have `32 = 160 - 128` bytes after `s_main.rlp2`, but we need to take into
                        // account also the two bytes `s_main.rlp1` and `s_main.rlp2`.
                        ifx!{is_leaf_long => {
                            require!(long_remainder => long_value_len);
                        }}
                        // When the leaf is in the last level of the trie and the value is long or there is one nibble in the key,
                        // we need to check:
                        // `s_rlp1_prev - 192 - 1  - (s_rlp2_cur - 128 + 1 + 1) = 0`.
                        // `s_rlp1_prev - 192 - 1` gives us the number of bytes that are to be in the leaf value row, while
                        // s_rlp2_cur - 128 + 1 + 1 gives us the number of bytes in the leaf value row.
                        // Note that in this case we do not have the length of the key stored in `s_main.rlp2` or `s_main.bytes[0]`.
                        // Example:
                        // `[227,32,161,160,187,239,170,18,88,1,56,188,38,60,149,117,120,38,223,78,36,235,129,201,170,170,170,170,170,170,170,170,170,170,170,170]`
                        ifx!{last_level.expr() + one_nibble.expr() => {
                            require!(s_rlp1_prev => 192.expr() + 1.expr() + long_value_len.expr());
                        }}
                    }}
                }}

                if !is_s {
                    // Check that `is_wrong_leaf` is boolean
                    let is_wrong_leaf = a!(s_main.rlp1, LEAF_NON_EXISTING_IND - LEAF_VALUE_C_IND);
                    require!(is_wrong_leaf => bool);
                    // Note: some is_wrong_leaf constraints are in this config because
                    // leaf_non_existing config only triggers constraints for
                    // non_existing_storage proof (see q_enable).
                    let is_non_existing_storage_proof = a!(proof_type.is_non_existing_storage_proof);
                    ifx!{not::expr(is_non_existing_storage_proof.expr()) => {
                        require!(is_wrong_leaf => 0);
                    }}
                }
            }}

            let rot_into_storage_root = if is_s {
                -LEAF_VALUE_S_IND - (ACCOUNT_LEAF_ROWS - ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND)
            } else {
                -LEAF_VALUE_C_IND - (ACCOUNT_LEAF_ROWS - ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND)
            };
            // rot_into_leaf_key = -1
            let len = get_leaf_len(meta, s_main.clone(), accs.clone(), -1);
            let is_branch_placeholder = a!(
                s_main.bytes[if is_s {IS_BRANCH_S_PLACEHOLDER_POS} else {IS_BRANCH_C_PLACEHOLDER_POS} - RLP_NUM],
                rot_into_init
            );
            let not_hashed = a!(accs.acc_c.rlc, -1);
            let mod_node_hash_rlc_cur = a!(if is_s {accs.s_mod_node_rlc} else {accs.c_mod_node_rlc}, rot_into_branch);
            let is_account_leaf_in_added_branch_placeholder = a!(
                is_account_leaf_in_added_branch,
                rot_into_account - BRANCH_ROWS_NUM
            );

            ifx!{is_leaf => {
                ifx!{not_first_level => {
                    ifx!{is_account_leaf_above => {
                        /* Hash of the only storage leaf is storage trie root */
                        // If there is no branch or extension node in the storage trie (just a leaf), it needs
                        // to be ensured that the hash of the (only) leaf is the storage root.
                        // Note: storage leaf in the first level cannot be shorter than 32 bytes (it is always hashed).
                        // Note: if leaf is a placeholder, the root in the account leaf needs to be the empty trie hash
                        // (see the gate below).
                        ifx!{not::expr(is_placeholder_without_branch.expr()) => {
                            // Note: storage root is always in `s_main.bytes`.
                            let hash_rlc = rlc::expr(
                                &s_main.bytes.iter().map(|&byte| a!(byte, rot_into_storage_root)).collect::<Vec<_>>(),
                                &r,
                            );
                            require!((a!(accs.acc_s.rlc), len, hash_rlc) => @keccak);
                        }}
                    } elsex {
                        /* Hash of the only storage leaf which is after a placeholder is storage trie root */
                        // If there is no branch or extension node in the storage trie (just a leaf)
                        // and the only leaf appears after branch placeholder, it needs
                        // to be ensured that the hash of the (only) leaf is the storage root.
                        // This appears when there is only one leaf in the storage trie and we add another leaf which
                        // means the only leaf in a trie is replaced by a branch or extension node (in delete scenario
                        // we have two leaves and one is deleted) - that means we have a branch placeholder in `S` proof
                        // and the leaf after it.
                        // Note: Branch in the first level cannot be shorter than 32 bytes (it is always hashed).
                        // Check in leaf value row.
                        // Only check if there is an account above the leaf.
                        // if account is directly above storage leaf, there is no placeholder branch
                        ifx!{is_account_leaf_in_added_branch_placeholder, is_branch_placeholder => {
                            // Note: storage root is always in `s_main.bytes`.
                            let hash_rlc = rlc::expr(
                                &s_main.bytes.iter().map(|&byte| a!(byte, rot_into_storage_root - BRANCH_ROWS_NUM)).collect::<Vec<_>>(),
                                &r,
                            );
                            require!((a!(accs.acc_s.rlc), len, hash_rlc) => @keccak);
                        }}
                    }}
                }}

                ifx!{q_not_first => {
                    ifx!{is_account_leaf_above => {
                        /* Hash of the only storage leaf which is placeholder requires empty storage root */
                        // When there is only one leaf in a storage trie and it is a placeholder, the trie needs to
                        // be empty - the storage root is hash of an empty trie.
                        // This occurs when the storage trie is empty and the first leaf is added (or reversed when
                        // there is only one leaf and it is deleted) - in this case we have a placeholder leaf in
                        // `S` proof and only one leaf in `C` proof. We need to check that in `S` proof we have an
                        // empty trie.
                        let empty_trie_hash: Vec<u8> = vec![
                            86, 232, 31, 23, 27, 204, 85, 166, 255, 131, 69, 230, 146, 192, 248, 110, 91,
                            72, 224, 27, 153, 108, 173, 192, 1, 98, 47, 181, 227, 99, 180, 33,
                        ];
                        // Only check if there is an account above the leaf.
                        ifx!{is_placeholder_without_branch => {
                            for (byte, empty_byte) in s_main.bytes.iter().zip(empty_trie_hash.iter()) {
                                require!(a!(*byte, rot_into_storage_root) => empty_byte.expr());
                            }
                        }}
                    } elsex {
                        ifx!{not_first_level, not::expr(sel.expr()) => {
                            ifx!{not::expr(is_branch_placeholder.expr()) => {
                                ifx!{not_hashed => {
                                    /* Non-hashed leaf in parent */
                                    // When the leaf is not hashed (shorter than 32 bytes), it needs to be checked that its RLC
                                    // is the same as the RLC of the modified node in the parent branch.
                                    // When leaf is not hashed, the `mod_node_hash_rlc` stores the RLC of the leaf bytes
                                    // (instead of the RLC of leaf hash). So we take the leaf RLC and compare it to the value
                                    // stored in `mod_node_hash_rlc` in the parent branch.
                                    // Note: `branch_parallel.rs` checks that there are 0s in `*_bytes` after the last
                                    // byte of the non-hashed branch child (otherwise some corrupted RLC could be provided).
                                    // For leaf without branch, the constraints are in storage_root_in_account_leaf.
                                    require!(a!(accs.acc_s.rlc) => mod_node_hash_rlc_cur);
                                } elsex {
                                    /* Leaf hash in parent */
                                    // It needs to be checked that the hash of a leaf is in the parent node. We do this by a lookup
                                    // into keccak table: `lookup(leaf_hash_rlc, parent_node_mod_child_rlc)`.
                                    // For leaf without branch, the constraints are in `storage_root_in_account_leaf.rs`.
                                    // If `sel = 1`, the leaf is only a placeholder (the leaf is being added or deleted)
                                    // and we do not check the hash of it.
                                    require!((a!(accs.acc_s.rlc), len, mod_node_hash_rlc_cur) => @keccak);
                                }}
                            } elsex {
                                /* Leaf hash in parent (branch placeholder) */
                                // Lookup for case when there is a placeholder branch - in this case we need to
                                // check the hash to correspond to the modified node of the branch above the placeholder branch.
                                // For leaf without branch, the constraints are in storage_root_in_account_leaf.
                                // Note: `sel1` and `sel2` in branch children: denote whether there is no leaf at
                                // `is_modified` (when value is added or deleted from trie).
                                // If `sel = 1`, there is no leaf at this position (value is being added or
                                // deleted) and we do not check the hash of it.
                                ifx!{not::expr(is_account_leaf_in_added_branch_placeholder.expr()) => {
                                    let mult = a!(accs.acc_s.mult, -1);
                                    let rlc = a!(accs.acc_s.rlc, -1) + rlc::expr(
                                        &s_main.rlp_bytes().iter().map(|&byte| a!(byte) * mult.expr()).collect::<Vec<_>>(),
                                        &extend_rand(&r),
                                    );
                                    // -3 to get from init branch into the previous branch (last row), note that -2 is needed
                                    // because of extension nodes.
                                    let mod_node_hash_rlc = a!(if is_s {accs.s_mod_node_rlc} else {accs.c_mod_node_rlc}, rot_into_init - 3);
                                    require!((rlc, len, mod_node_hash_rlc) => @keccak);
                                }}
                            }}
                        }}
                    }}
                }}
            }}

            /*let sel = |meta: &mut VirtualCells<F>| {
                let not_first_level = meta.query_advice(position_cols.not_first_level, Rotation::cur());
                let is_leaf = meta.query_advice(is_leaf_value, Rotation::cur());
                not_first_level * is_leaf
            };

            // There are 0s in `s_main.bytes` after the last value byte.
            if check_zeros {
                for ind in 0..HASH_WIDTH {
                    key_len_lookup(
                        meta,
                        sel,
                        ind + 1,
                        s_main.rlp2,
                        s_main.bytes[ind],
                        128,
                        fixed_table,
                    )
                }
            }*/
        }}

        // Note: For cases when storage leaf is in the first storage level, the
        // constraints are in `storage_root_in_account_leaf.rs`.

        LeafValueConfig {
            _marker: PhantomData,
        }
    }

    pub fn assign(
        &self,
        region: &mut Region<'_, F>,
        mpt_config: &MPTConfig<F>,
        witness: &[MptWitnessRow<F>],
        pv: &mut ProofValues<F>,
        offset: usize,
        is_s: bool,
    ) {
        let row_prev = &witness[offset - 1];
        let row = &witness[offset];

        // Info whether leaf value is 1 byte or more:
        let mut is_long = false;
        if row_prev.get_byte(0) == 248 {
            // whole leaf is in long format (3 RLP meta bytes)
            let key_len = row_prev.get_byte(2) - 128;
            if row_prev.get_byte(1) - key_len - 1 > 1 {
                is_long = true;
            }
        } else if row_prev.get_byte(1) < 128 {
            // last_level or one_nibble
            let leaf_len = row_prev.get_byte(0) - 192;
            if leaf_len - 1 > 1 {
                is_long = true;
            }
        } else {
            let leaf_len = row_prev.get_byte(0) - 192;
            let key_len = row_prev.get_byte(1) - 128;
            if leaf_len - key_len - 1 > 1 {
                is_long = true;
            }
        }
        // Short means there is only one byte for value (no RLP specific bytes).
        // Long means there is more than one byte for value which brings two
        // RLP specific bytes, like: 161 160 ... for 32-long value.
        let mut typ = "short";
        if is_long {
            typ = "long";
        }
        mpt_config.assign_long_short(region, typ, offset).ok();

        // Leaf RLC
        mpt_config.compute_acc_and_mult(
            &row.bytes,
            &mut pv.acc_s,
            &mut pv.acc_mult_s,
            0,
            HASH_WIDTH + 2,
        );

        pv.acc_c = F::zero();
        pv.acc_mult_c = F::one();
        // Leaf value RLC
        let mut start = 0;
        if is_long {
            start = 2;
        }
        mpt_config.compute_acc_and_mult(
            &row.bytes,
            &mut pv.acc_c,
            &mut pv.acc_mult_c,
            start,
            HASH_WIDTH + 2,
        );

        let empty_trie_hash: Vec<u8> = vec![
            86, 232, 31, 23, 27, 204, 85, 166, 255, 131, 69, 230, 146, 192, 248, 110, 91, 72, 224,
            27, 153, 108, 173, 192, 1, 98, 47, 181, 227, 99, 180, 33,
        ];
        if is_s {
            // Store leaf value RLC into rlc1 to be later set in leaf value C row (to enable
            // lookups):
            pv.rlc1 = pv.acc_c;

            /*
            account leaf storage codehash S <- rotate here
            account leaf storage codehash C
            account leaf in added branch
            leaf key S
            leaf value S <- we are here
            leaf key C
            leaf value C
            */
            let row_prev = &witness[offset - 4];
            if row_prev.get_type() == MptWitnessRowType::AccountLeafRootCodehashS
                && row_prev.s_hash_bytes() == empty_trie_hash
            {
                // Leaf is without branch and it is just a placeholder.
                region
                    .assign_advice(
                        || "assign sel1".to_string(),
                        mpt_config.denoter.sel1,
                        offset,
                        || Value::known(F::one()),
                    )
                    .ok();
            }
        } else {
            region
                .assign_advice(
                    || "assign key_rlc into key_rlc_mult".to_string(),
                    mpt_config.accumulators.key.mult,
                    offset,
                    || Value::known(pv.rlc2),
                )
                .ok();
            region
                .assign_advice(
                    || "assign leaf value S into value_prev".to_string(),
                    mpt_config.value_prev,
                    offset,
                    || Value::known(pv.rlc1),
                )
                .ok();

            /*
            account leaf storage codehash S
            account leaf storage codehash C <- rotate here
            account leaf in added branch
            leaf key S
            leaf value S
            leaf key C
            leaf value C <- we are here
            */
            let row_prev = &witness[offset - 5];
            if row_prev.get_type() == MptWitnessRowType::AccountLeafRootCodehashC
                && row_prev.s_hash_bytes() == empty_trie_hash
            {
                // Leaf is without branch and it is just a placeholder.
                region
                    .assign_advice(
                        || "assign sel2".to_string(),
                        mpt_config.denoter.sel2,
                        offset,
                        || Value::known(F::one()),
                    )
                    .ok();
            }
        }

        mpt_config
            .assign_acc(
                region,
                pv.acc_s, // leaf RLC
                pv.acc_mult_s,
                pv.acc_c, // leaf value RLC
                F::zero(),
                offset,
            )
            .ok();

        region
            .assign_advice(
                || "assign leaf value C into value".to_string(),
                mpt_config.value,
                offset,
                || Value::known(pv.acc_c),
            )
            .ok();

        if !is_s && row.get_byte_rev(IS_STORAGE_MOD_POS) == 1 {
            region
                .assign_advice(
                    || "assign lookup enabled".to_string(),
                    mpt_config.proof_type.proof_type,
                    offset,
                    || Value::known(F::from(6_u64)), /* storage mod lookup enabled in this row
                                                      * if it is is_storage_mod proof */
                )
                .ok();
        }
    }
}
