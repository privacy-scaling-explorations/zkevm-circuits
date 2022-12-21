use gadgets::util::{and, not, or, select, Expr};
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
    mpt_circuit::columns::{AccumulatorCols, MainCols, PositionCols, ProofTypeCols},
    mpt_circuit::helpers::{compute_rlc, extend_rand, mult_diff_lookup, range_lookups},
    mpt_circuit::witness_row::{MptWitnessRow, MptWitnessRowType},
    mpt_circuit::{
        helpers::key_len_lookup, param::IS_ACCOUNT_DELETE_MOD_POS, FixedTableTag, MPTConfig,
        ProofValues,
    },
    mpt_circuit::{
        helpers::BaseConstraintBuilder,
        param::{
            BRANCH_ROWS_NUM, HASH_WIDTH, IS_BRANCH_C16_POS, IS_BRANCH_C1_POS,
            IS_BRANCH_C_PLACEHOLDER_POS, IS_BRANCH_S_PLACEHOLDER_POS, IS_EXT_LONG_EVEN_C16_POS,
            IS_EXT_LONG_EVEN_C1_POS, IS_EXT_LONG_ODD_C16_POS, IS_EXT_LONG_ODD_C1_POS,
            IS_EXT_SHORT_C16_POS, IS_EXT_SHORT_C1_POS, NIBBLES_COUNTER_POS,
            POWER_OF_RANDOMNESS_LEN, RLP_NUM, S_START,
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

The constraints in this file apply to ACCOUNT_LEAF_KEY_S and ACCOUNT_LEAF_KEY_C rows.

For example, the two rows might be:
[248,106,161,32,252,237,52,8,133,130,180,167,143,97,28,115,102,25,94,62,148,249,8,6,55,244,16,75,187,208,208,127,251,120,61,73,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
[248,106,161,32,252,237,52,8,133,130,180,167,143,97,28,115,102,25,94,62,148,249,8,6,55,244,16,75,187,208,208,127,251,120,61,73,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

Here, in `ACCOUNT_LEAF_KEY_S` example row, there are key nibbles for `S` proof stored in compact form.
The nibbles start at `s_main.bytes[1]` and can go to `c_main.rlp2`.

In `ACCOUNT_LEAF_KEY_C` example row, there are key nibbles for `C` proof stored in compact form.
The nibbles start at `s_main.bytes[1]` and can go to `c_main.rlp2`.

The whole account leaf looks like:
[248,106,161,32,252,237,52,8,133,130,180,167,143,97,28,115,102,25,94,62,148,249,8,6,55,244,16,75,187,208,208,127,251,120,61,73,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
[248,106,161,32,252,237,52,8,133,130,180,167,143,97,28,115,102,25,94,62,148,249,8,6,55,244,16,75,187,208,208,127,251,120,61,73,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
[0,0,0,32,252,237,52,8,133,130,180,167,143,97,28,115,102,25,94,62,148,249,8,6,55,244,16,75,187,208,208,127,251,120,61,73,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
[184,70,128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,248,68,128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
[184,70,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,248,68,128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
[0,160,86,232,31,23,27,204,85,166,255,131,69,230,146,192,248,110,91,72,224,27,153,108,173,192,1,98,47,181,227,99,180,33,0,160,197,210,70,1,134,247,35,60,146,126,125,178,220,199,3,192,229,0,182,83,202,130,39,59,123,250,216,4,93,133,164,122]
[0,160,86,232,31,23,27,204,85,166,255,131,69,230,146,192,248,110,91,72,224,27,153,108,173,192,1,98,47,181,227,99,180,33,0,160,197,210,70,1,134,247,35,60,146,126,125,178,220,199,3,192,229,0,182,83,202,130,39,59,123,250,216,4,93,133,164,122]
[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

There are two main scenarios when an account is added to the trie:
 1. There exists another account which has the same address to the some point as the one that
 is being added, including the position of this account in the branch.
 In this case a new branch is added to the trie.
 The existing account drifts down one level to the new branch. The newly
 added account will also appear in this branch. For example, let us say that we have the account `A`
 with nibbles `[3, 12, 3]` in the trie. We then add the account `A1` with nibbles `[3, 12, 5]`
 to the trie. The branch will appear (at position `[3, 12]`) which will have `A` at position 3
 and `A1` at position 5. This means there will be an additional branch in `C` proof (or in `S`
 proof when the situation is reversed - we are deleting the leaf instead of adding) and
 for this reason we add a placeholder branch for `S` proof (for `C` proof in reversed situation)
 to preserve the circuit layout (more details about this technicality are given below).

 2. The branch where the new account is to be added has nil node at the position where the new account
 is to be added. For example, let us have a branch at `[3, 12]`, we are adding a leaf with the
 first three nibbles as `[3, 12, 5]`, and the position 5 in our branch is not occupied.
 There does not exist an account which has the same address to the some point.
 In this case, the `getProof` response does not end with a leaf, but with a branch.
 To preserve the layout, a placeholder account leaf is added.

Lookups:
The `is_account_delete_mod` lookup is enabled in `ACCOUNT_LEAF_KEY_S` row.
*/

#[derive(Clone, Debug)]
pub(crate) struct AccountLeafKeyConfig<F> {
    _marker: PhantomData<F>,
}

impl<F: FieldExt> AccountLeafKeyConfig<F> {
    #[allow(clippy::too_many_arguments)]
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        proof_type: ProofTypeCols<F>,
        q_enable: impl Fn(&mut VirtualCells<'_, F>) -> Expression<F> + Copy,
        position_cols: PositionCols<F>,
        s_main: MainCols<F>,
        c_main: MainCols<F>,
        accs: AccumulatorCols<F>,
        r: [Expression<F>; HASH_WIDTH],
        fixed_table: [Column<Fixed>; 3],
        address_rlc: Column<Advice>,
        sel_2: Column<Advice>,
        is_s: bool,
        check_zeros: bool,
    ) -> Self {
        // key rlc is in the first branch node
        let rot_into_first_branch_child = if is_s { -18 } else { -19 };
        let rot_into_init = rot_into_first_branch_child - 1;

        let mut cb = BaseConstraintBuilder::default();
        meta.create_gate("Account leaf RLC after key", |meta| {
        constraints!{[meta, cb], {
            let q_enable = q_enable(meta);
            ifx!{q_enable => {
                /* Account leaf RLC after key */
                // [248,112,157,59,158,160,175,159,65,212,107,23,98,208,38,205,150,63,244,2,185,236,246,95,240,224,191,229,27,102,202,231,184,80
                // There are 112 bytes after the first two bytes.
                // 157 means the key is 29 (157 - 128) bytes long.

                // Account leaf always starts with 248 because its length is always longer than 55 bytes due to
                // containing two hashes - storage root and codehash, which are both of 32 bytes.
                // 248 is RLP byte which means there is `1 = 248 - 247` byte specifying the length of the remaining
                // list. For example, in [248,112,157,59,...], there are 112 byte after the second byte.
                require!(a!(s_main.rlp1) => 248);

                // In each row of the account leaf we compute an intermediate RLC of the whole leaf.
                // The RLC after account leaf key row is stored in `acc` column. We check the stored value
                // is computed correctly.
                let rlc = rlc::expr(
                    &[s_main.rlp_bytes(), c_main.rlp_bytes()].concat()[0..36].iter().map(|&byte| a!(byte)).collect::<Vec<_>>(),
                    &extend_rand(&r),
                );
                require!(a!(accs.acc_s.rlc) => rlc);

                /* Account leaf address RLC & nibbles count (branch not placeholder) */

                let is_leaf_in_first_level = not::expr(a!(position_cols.not_first_level));

                // `is_branch_placeholder = 0` when in first level
                let is_branch_placeholder = not::expr(is_leaf_in_first_level.expr()) * a!(s_main.bytes[if is_s {IS_BRANCH_S_PLACEHOLDER_POS} else {IS_BRANCH_C_PLACEHOLDER_POS} - RLP_NUM], rot_into_first_branch_child - 1);

                // `key_rlc_acc_start = 0` if leaf in first level
                // `key_mult_start = 1` if leaf in first level
                let key_rlc_acc_start = selectx!{not::expr(is_leaf_in_first_level.expr()) => {
                    a!(accs.key.rlc, rot_into_first_branch_child)
                }};
                let key_mult_start = selectx!{not::expr(is_leaf_in_first_level.expr()) => {
                    a!(accs.key.mult, rot_into_first_branch_child)
                } elsex {
                    1
                }};

                // `is_c16 = 0, is_c1 = 1` if leaf in first level, because we do not have the branch above
                // and we need to multiply the first nibble by 16 (as it would be `c1` in the branch above)
                let is_c16 = selectx!{not::expr(is_leaf_in_first_level.expr()) => {
                    a!(s_main.bytes[IS_BRANCH_C16_POS - RLP_NUM], rot_into_first_branch_child - 1)
                }};
                let is_c1 = selectx!{not::expr(is_leaf_in_first_level.expr()) => {
                    a!(s_main.bytes[IS_BRANCH_C1_POS - RLP_NUM], rot_into_first_branch_child - 1)
                } elsex {
                    1
                }};

                // `is_c16`/`is_c1` hold the information whether there is even or odd number of nibbles in the leaf.

                // Let us observe a case with even number of nibbles first:
                // `[248,106,161,32,252,237,52,8,133,130,180,167,143,97,28,115,102,25,94,62,148,249,8,6,55,244,16,75,187,208,208,127,251,120,61,73,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]`
                // In this case we have 32 in `s_main.bytes[1]`. The nibbles start in `s_main.bytes[2]`,
                // eacy byte presents two nibbles. We can simply add the bytes to the intermediate RLC:
                // `rlc = intermediate_rlc + s_main.bytes[2] * mult_prev + s_main.bytes[3] * mult_prev * r + ... `

                // Let us observe a case with odd number of nibbles now:
                // `[248,106,161,51,25,...]`
                // In this case we have 51 in `s_main.bytes[1]`, this presents the first nibble: `3 = 51 - 48`.
                // From `s_main.bytes[2]` it is as in the even number case. We compute the RLC as:
                // `rlc = intermediate_rlc + (s_main.bytes[1] - 48) * mult_prev + s_main.bytes[2] * mult_prev * r + ... `

                // If there is an even number of nibbles in the leaf, `s_main.bytes[1]` need to be 32.
                ifx!{not::expr(is_branch_placeholder.expr()), is_c1 => {
                    require!(a!(s_main.bytes[1]) => 32);
                }}

                // set to key_mult_start * r if is_c16, else key_mult_start
                let key_mult = key_mult_start.clone() * selectx!{is_c16 => {
                    r[0].clone()
                } elsex {
                    1
                }};

                // If sel1 = 1, we have nibble+48 in s_main.bytes[0].
                let rlc = key_rlc_acc_start + rlc::expr(
                    &[s_main.rlp_bytes(), c_main.rlp_bytes()].concat()[3..36].iter().enumerate().map(|(idx, &byte)|
                        (if idx == 0 { (a!(byte) - 48.expr()) * is_c16.expr() * key_mult_start.expr() } else { a!(byte) * key_mult.expr() })).collect::<Vec<_>>(),
                    &[[1.expr()].to_vec(), r.to_vec()].concat(),
                );

                let key_rlc = a!(accs.key.rlc);

                // Account leaf contains the remaining nibbles of the account address. Combining the path
                // of the leaf in the trie and these remaining nibbles needs to be the same as the account
                // address which is given in the `address_rlc` column that is to be used by a lookup (see the
                // constraint below).

                // Address RLC needs to be computed properly - we need to take into account the path of the leaf
                // in the trie and the remaining nibbles in the account leaf.

                // The intermediate RLC is retrieved from the last branch above the account leaf - this
                // presents the RLC after the path to the leaf is considered. After this, the bytes (nibbles
                // in a compacted form) in the leaf have to be added to the RLC.
                ifx!{not::expr(is_branch_placeholder.expr()) => {
                    require!(key_rlc => rlc);
                }}

                // The computed key RLC needs to be the same as the value in `address_rlc` column.
                // This seems to be redundant (we could write one constraint instead of two:
                // `key_rlc_acc - address_rlc = 0`), but note that `key_rlc` is used in
                // `account_leaf_key_in_added_branch` and in cases when there is a placeholder branch
                // we have `key_rlc - address_rlc != 0` because `key_rlc` is computed for the branch
                // that is parallel to the placeholder branch.
                let is_non_existing_account_proof = a!(proof_type.is_non_existing_account_proof);
                ifx!{not::expr(is_branch_placeholder.expr()), not::expr(is_non_existing_account_proof.expr()) => {
                    require!(key_rlc => a!(address_rlc));
                }}

                // Checking the total number of nibbles is to prevent having short addresses
                // which could lead to a root node which would be shorter than 32 bytes and thus not hashed. That
                // means the trie could be manipulated to reach a desired root.
                // Note: we need to check the number of nibbles being 64 for non_existing_account_proof too
                // (even if the address being checked here might is the address of the wrong leaf)
                ifx!{not::expr(is_branch_placeholder.expr()) => {
                    let s_bytes0 = a!(s_main.bytes[0]);
                    let leaf_nibbles = selectx!{is_c1 => {
                        (s_bytes0.expr() - 128.expr() - 1.expr()) * 2.expr()
                    } elsex {
                        (s_bytes0.expr() - 128.expr()) * 2.expr() - 1.expr()
                    }};

                    // nibbles_count = 0 if in first storage level
                    let nibbles_count = selectx!{not::expr(is_leaf_in_first_level.expr()) => {
                        a!(s_main.bytes[NIBBLES_COUNTER_POS - RLP_NUM], rot_into_init)
                    }};

                    require!(nibbles_count + leaf_nibbles => 64);
                }}

                /* Account leaf address RLC & nibbles count (after placeholder) */

                // The example layout for a branch placeholder looks like (placeholder could be in `C` proof too):
                //     Branch 1S               || Branch 1C
                //     Branch 2S (placeholder) || Branch 2C
                //     Leaf S
                //     Leaf C

                // Using `Previous key RLC` constraint we ensured that we copied the key RLC from Branch 1S
                // to Leaf S `accs.acc_c.rlc` column. So when add nibbles to compute the key RLC (address RLC)
                // of the account, we start with `accs.acc_c.rlc` value from the current row.
                let is_branch_placeholder = a!(s_main.bytes[if is_s {IS_BRANCH_S_PLACEHOLDER_POS} else {IS_BRANCH_C_PLACEHOLDER_POS} - RLP_NUM], rot_into_first_branch_child - 1);

                // Note: key RLC is in the first branch node (not branch init).
                let is_placeholder_branch_in_first_level = not::expr(a!(position_cols.not_first_level, rot_into_init));
                let rot_level_above = rot_into_init + 1 - BRANCH_ROWS_NUM;
                let key_rlc_acc_start = selectx!{not::expr(is_placeholder_branch_in_first_level.expr()) => {
                    a!(accs.key.rlc, rot_level_above)
                }};
                let key_mult_start = selectx!{not::expr(is_placeholder_branch_in_first_level.expr()) => {
                    a!(accs.key.mult, rot_level_above)
                } elsex {
                    1
                }};

                // TODO: the expressions below can be simplified

                let sel1p = meta.query_advice(
                    s_main.bytes[IS_BRANCH_C16_POS - RLP_NUM],
                    Rotation(rot_into_first_branch_child - 1),
                );
                let sel2p = meta.query_advice(
                    s_main.bytes[IS_BRANCH_C1_POS - RLP_NUM],
                    Rotation(rot_into_first_branch_child - 1),
                );

                // sel1/sel2 tells us whether there is an even or odd number of nibbles in the leaf.
                // sel1/sel2 info is need for the computation of the key RLC (see below), in case of a leaf
                // after branch placeholder, sel1/sel2 can be computed as follows.

                // Note that we cannot rotate back into Branch 1S because we get PoisonedConstraint
                // in extension_node_key.

                // Instead, we can rotate into branch parallel to the placeholder branch and compute sel1/sel2 with info from there.
                // Let's denote sel1/sel2 from this branch by sel1p/sel2p.

                // There are a couple of different cases, for example when branch/extension node parallel
                // to the placeholder branch is a regular branch.
                // There is only one nibble taken by Branch 2C, so sel1/sel2 simply turns around compared to sel1p/sel2p:
                // sel1 = sel2p
                // sel2 = sel1p

                // When branch/extension node parallel to the placeholder branch is an extension node, it depends on the
                // number of nibbles. If there is an odd number of nibbles: sel1 = sel1p, sel2 = sel2p. If there is
                // an even number of nibbles, it turns around.

                // Note: _c16 presents the same info as sel1, _c1 presents the same info as sel2 (this information is doubled
                // to reduce the degree when handling different cases in extension_node_key).

                let is_ext_short_c16 = meta.query_advice(
                    s_main.bytes[IS_EXT_SHORT_C16_POS - RLP_NUM],
                    Rotation(rot_into_init),
                );
                let is_ext_short_c1 = meta.query_advice(
                    s_main.bytes[IS_EXT_SHORT_C1_POS - RLP_NUM],
                    Rotation(rot_into_init),
                );
                let is_ext_long_even_c16 = meta.query_advice(
                    s_main.bytes[IS_EXT_LONG_EVEN_C16_POS - RLP_NUM],
                    Rotation(rot_into_init),
                );
                let is_ext_long_even_c1 = meta.query_advice(
                    s_main.bytes[IS_EXT_LONG_EVEN_C1_POS - RLP_NUM],
                    Rotation(rot_into_init),
                );
                let is_ext_long_odd_c16 = meta.query_advice(
                    s_main.bytes[IS_EXT_LONG_ODD_C16_POS - RLP_NUM],
                    Rotation(rot_into_init),
                );
                let is_ext_long_odd_c1 = meta.query_advice(
                    s_main.bytes[IS_EXT_LONG_ODD_C1_POS - RLP_NUM],
                    Rotation(rot_into_init),
                );

                let is_extension_node = is_ext_short_c16.clone()
                    + is_ext_short_c1.clone()
                    + is_ext_long_even_c16.clone()
                    + is_ext_long_even_c1.clone()
                    + is_ext_long_odd_c16.clone()
                    + is_ext_long_odd_c1.clone();

                let sel1 = not::expr(is_extension_node) * sel2p.clone()
                    + is_ext_short_c16 * sel1p.clone()
                    + is_ext_short_c1 * sel2p.clone()
                    + is_ext_long_even_c16 * sel2p.clone()
                    + is_ext_long_even_c1 * sel1p.clone()
                    + is_ext_long_odd_c16 * sel1p
                    + is_ext_long_odd_c1 * sel2p;
                let sel2 = not::expr(sel1.expr());

                // If sel2 = 1, we have 32 in s_main.bytes[1].
                ifx!{sel2, is_branch_placeholder, not::expr(is_leaf_in_first_level.expr()) => {
                    require!(a!(s_main.bytes[1]) => 32);
                }}

                // set to key_mult_start * r if `sel1`, else key_mult_start
                let key_mult = key_mult_start.clone() * selectx!{sel1 => {
                    r[0].clone()
                } elsex {
                    1
                }};

                // If sel1 = 1, we have nibble+48 in s_main.bytes[0].
                let rlc = key_rlc_acc_start + rlc::expr(
                    &[s_main.rlp_bytes(), c_main.rlp_bytes()].concat()[3..36].iter().enumerate().map(|(idx, &byte)|
                        (if idx == 0 { (a!(byte) - 48.expr()) * sel1.expr() * key_mult_start.expr() } else { a!(byte) * key_mult.expr() })).collect::<Vec<_>>(),
                    &[[1.expr()].to_vec(), r.to_vec()].concat(),
                );

                // Although `key_rlc` is not compared to `address_rlc` in the case when the leaf
                // is below the placeholder branch (`address_rlc` is compared to the parallel leaf `key_rlc`),
                // we still need properly computed `key_rlc` to reuse it in `account_leaf_key_in_added_branch`.
                // Note: `key_rlc - address_rlc != 0` when placeholder branch.
                ifx!{is_branch_placeholder, not::expr(is_leaf_in_first_level.expr()) => {
                    require!(rlc => a!(accs.key.rlc));
                }}

                // Note that when the leaf is in the first level (but positioned after the placeholder
                // in the circuit), there is no branch above the placeholder branch from where
                // `nibbles_count` is to be retrieved. In that case `nibbles_count = 0`.
                ifx!{is_branch_placeholder, not::expr(is_leaf_in_first_level.expr()) => {
                    let s_bytes0 = a!(s_main.bytes[0]);
                    let leaf_nibbles = selectx!{sel2 => {
                        (s_bytes0.expr() - 128.expr() - 1.expr()) * 2.expr()
                    } elsex {
                        (s_bytes0.expr() - 128.expr()) * 2.expr() - 1.expr()
                    }};

                    // Note that when the leaf is in the first level (but positioned after the placeholder
                    // in the circuit), there is no branch above the placeholder branch from where
                    // `nibbles_count` is to be retrieved. In that case `nibbles_count = 0`.
                    let is_not_branch_in_first_level = a!(position_cols.not_first_level, rot_into_first_branch_child);
                    let nibbles_count = selectx!{is_not_branch_in_first_level => {
                        a!(s_main.bytes[NIBBLES_COUNTER_POS - RLP_NUM], rot_into_init - BRANCH_ROWS_NUM)
                    }};

                    require!(nibbles_count + leaf_nibbles => 64);
                }}

                /* Account delete */

                // We need to make sure there is no leaf when account is deleted. Two possible cases:
                // 1. Account leaf is deleted and there is a nil object in branch. In this case we have
                //     a placeholder leaf.
                // 2. Account leaf is deleted from a branch with two leaves, the remaining leaf moves one level up
                //     and replaces the branch. In this case we have a branch placeholder.
                // So we need to check there is a placeholder branch when we have the second case.
                // Note: we do not need to cover the case when the (only) branch dissapears and only one
                // leaf remains in the trie because there will always be at least two leaves
                // (the genesis account) when account will be deleted,
                // so there will always be a branch / extension node (and thus placeholder branch).
                if !is_s {
                    // is_leaf_placeholder is stored in branch children: sel1 for S, sel2 for C.
                    let is_leaf_placeholder = a!(sel_2, rot_into_init + 1);
                    let is_account_delete_mod = a!(proof_type.is_account_delete_mod);
                    let is_branch_placeholder = a!(s_main.bytes[IS_BRANCH_C_PLACEHOLDER_POS - RLP_NUM], rot_into_init);
                    // Note: this constraint suffices because the proper transition from branch to a
                    // leaf (2. case) is checked by constraints in
                    // account_leaf_key_in_added_branch.
                    ifx!{is_account_delete_mod => {
                        require!(or::expr([is_leaf_placeholder, is_branch_placeholder]) => true);
                    }}
                }
            }}
            }}

            cb.gate(1.expr())
        });

        /*
        Key RLC is computed over all of `s_main.bytes[1], ..., s_main.bytes[31], c_main.rlp1, c_main.rlp2`
        because we do not know the key length in advance.
        To prevent changing the key and setting `s_main.bytes[i]` (or `c_main.rlp1/c_main.rlp2`) for
        `i > key_len + 1` to get the desired key RLC, we need to ensure that
        `s_main.bytes[i] = 0` for `i > key_len + 1`.

        Note: the key length is always in s_main.bytes[0] here as opposed to storage
        key leaf where it can appear in s_rlp2 too. This is because the account
        leaf contains nonce, balance, ... which makes it always longer than 55 bytes,
        which makes a RLP to start with 248 (s_rlp1) and having one byte (in s_rlp2)
        for the length of the remaining stream.
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
            key_len_lookup(
                meta,
                q_enable,
                32,
                s_main.bytes[0],
                c_main.rlp1,
                128,
                fixed_table,
            );
            key_len_lookup(
                meta,
                q_enable,
                33,
                s_main.bytes[0],
                c_main.rlp2,
                128,
                fixed_table,
            );
        }

        /*
        When the account intermediate RLC is computed in the next row (nonce balance row), we need
        to know the intermediate RLC from the current row and the randomness multiplier (`r` to some power).
        The power of randomness `r` is determined by the key length - the intermediate RLC in the current row
        is computed as (key starts in `s_main.bytes[1]`):
        `rlc = s_main.rlp1 + s_main.rlp2 * r + s_main.bytes[0] * r^2 + key_bytes[0] * r^3 + ... + key_bytes[key_len-1] * r^{key_len + 2}`
        So the multiplier to be used in the next row is `r^{key_len + 2}`.

        `mult_diff` needs to correspond to the key length + 2 RLP bytes + 1 byte for byte that contains the key length.
        That means `mult_diff` needs to be `r^{key_len+1}` where `key_len = s_main.bytes[0] - 128`.
        */
        mult_diff_lookup(
            meta,
            q_enable,
            3,
            s_main.bytes[0],
            accs.acc_s.mult,
            128,
            fixed_table,
        );

        // Note: there is no need to check `key_rlc_mult` as it is not used after this
        // row.

        /*
        Range lookups ensure that `s_main`, `c_main.rlp1`, `c_main.rlp2` columns are all bytes (between 0 - 255).
        Note that `c_main.bytes` columns are not used.
        */
        range_lookups(
            meta,
            q_enable,
            s_main.bytes.to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );
        // s_rlp1 is always 248 (checked above)
        range_lookups(
            meta,
            q_enable,
            [s_main.rlp2, c_main.rlp1, c_main.rlp2].to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );

        AccountLeafKeyConfig {
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
        // account leaf key S & C
        let mut acc = F::zero();
        let mut acc_mult = F::one();
        // 35 = 2 (leaf rlp) + 1 (key rlp) + key_len
        let key_len = (row.get_byte(2) - 128) as usize;
        for b in row.bytes.iter().take(3 + key_len) {
            acc += F::from(*b as u64) * acc_mult;
            acc_mult *= mpt_config.randomness;
        }

        if row.get_type() == MptWitnessRowType::AccountLeafKeyS {
            pv.acc_account_s = acc;
            pv.acc_mult_account_s = acc_mult;

            if row.get_byte_rev(IS_ACCOUNT_DELETE_MOD_POS) == 1 {
                region
                    .assign_advice(
                        || "assign lookup enabled".to_string(),
                        mpt_config.proof_type.proof_type,
                        offset,
                        || Value::known(F::from(5_u64)), /* account delete mod lookup enabled in
                                                          * this row if it is is_account_delete
                                                          * proof */
                    )
                    .ok();
            }
        } else {
            pv.acc_account_c = acc;
            pv.acc_mult_account_c = acc_mult;
        }

        // For leaf S and leaf C we need to start with the same rlc.
        let mut key_rlc_new = pv.key_rlc;
        let mut key_rlc_mult_new = pv.key_rlc_mult;
        if (pv.is_branch_s_placeholder && row.get_type() == MptWitnessRowType::AccountLeafKeyS)
            || (pv.is_branch_c_placeholder && row.get_type() == MptWitnessRowType::AccountLeafKeyC)
        {
            key_rlc_new = pv.key_rlc_prev;
            key_rlc_mult_new = pv.key_rlc_mult_prev;
        }

        mpt_config.compute_key_rlc(&row.bytes, &mut key_rlc_new, &mut key_rlc_mult_new, S_START);
        region
            .assign_advice(
                || "assign key_rlc".to_string(),
                mpt_config.accumulators.key.rlc,
                offset,
                || Value::known(key_rlc_new),
            )
            .ok();

        mpt_config
            .assign_acc(region, acc, acc_mult, F::zero(), F::zero(), offset)
            .ok();
    }
}
