use gadgets::util::{and, not, select, Expr};
use halo2_proofs::{arithmetic::FieldExt, circuit::Region, plonk::VirtualCells, poly::Rotation};
use std::marker::PhantomData;

use crate::{
    constraints,
    evm_circuit::util::rlc,
    mpt_circuit::helpers::{get_is_extension_node, get_is_extension_node_one_nibble},
    mpt_circuit::{helpers::extend_rand, witness_row::MptWitnessRow, FixedTableTag, MPTContext},
    mpt_circuit::{
        helpers::{get_leaf_len, BaseConstraintBuilder},
        param::{
            BRANCH_ROWS_NUM, IS_BRANCH_C16_POS, IS_BRANCH_C1_POS, LEAF_DRIFTED_IND, LEAF_KEY_C_IND,
            LEAF_KEY_S_IND,
        },
    },
    mpt_circuit::{MPTConfig, ProofValues},
};

use crate::mpt_circuit::param::{
    IS_BRANCH_C_PLACEHOLDER_POS, IS_BRANCH_S_PLACEHOLDER_POS, RLP_NUM,
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
[226 160 32 235 117 17 208 2 186 74 12 134 238 103 127 37 240 27 164 245 42 218 188 162 9 151 17 57 90 177 190 250 180 61 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 2]
[27 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 13]
[225 159 63 117 31 216 242 20 172 137 89 10 84 218 35 38 178 182 67 5 68 54 127 178 216 248 46 67 173 108 157 55 18 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 3]
[17 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 14]
[225 159 59 117 17 208 2 186 74 12 134 238 103 127 37 240 27 164 245 42 218 188 162 9 151 17 57 90 177 190 250 180 61 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 15]
[0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 19]

The `LEAF_DRIFTED` row is nonempty when a leaf is added (or deleted) to the position in trie where there is already
an existing leaf. This appears when an existing leaf and a newly added leaf have the same initial key nibbles.
In this case, a new branch is created and both leaves (existing and newly added) appear in the new branch.
`LEAF_DRIFTED` row contains the key bytes of the existing leaf once it drifted down to the new branch.

The constraints for `LEAF_DRIFTED` row are very similar to the ones for `LEAF_KEY` rows, but we have
different selectors (different row) and there are some scenarios that do not appear here, like being in
the first level of the trie. Also, when computing the leaf RLC, we need to take a different approach because
the leaf value for the drifted leaf is stored in a parallel proof.
*/

#[derive(Clone, Debug, Default)]
pub(crate) struct LeafKeyInAddedBranchConfig<F> {
    _marker: PhantomData<F>,
}

impl<F: FieldExt> LeafKeyInAddedBranchConfig<F> {
    pub fn configure(
        meta: &mut VirtualCells<'_, F>,
        cb: &mut BaseConstraintBuilder<F>,
        ctx: MPTContext<F>,
    ) -> Self {
        let s_main = ctx.s_main;
        let c_main = ctx.c_main;
        let accs = ctx.accumulators;
        let drifted_pos = ctx.branch.drifted_pos;
        let is_account_leaf_in_added_branch = ctx.account_leaf.is_in_added_branch;
        let r = ctx.r;

        let rot_branch_init = -LEAF_DRIFTED_IND - BRANCH_ROWS_NUM;
        let rot_into_account = -LEAF_DRIFTED_IND - 1;

        // Note: The leaf value is not stored in this row, but it needs to be the same
        // as the leaf value before it drifted down to the new branch, so we can
        // retrieve it from the row of a leaf before a drift. We need the leaf value to
        // build the leaf RLC to check that the hash of a drifted leaf is in the
        // new branch.
        // It needs to be ensured that the leaf intermediate RLC (containing the leaf
        // key bytes) is properly computed. The intermediate RLC is then used to
        // compute the final leaf RLC (containing the leaf value bytes too).
        // Finally, the lookup is used to check that the hash that
        // corresponds to the leaf RLC is in the parent branch at `drifted_pos`
        // position.
        constraints! {[meta, cb], {
            // drifted leaf appears only when there is a placeholder branch
            let is_branch_s_placeholder = meta.query_advice(
                s_main.bytes[IS_BRANCH_S_PLACEHOLDER_POS - RLP_NUM],
                Rotation(rot_branch_init),
            );
            let is_branch_c_placeholder = meta.query_advice(
                s_main.bytes[IS_BRANCH_C_PLACEHOLDER_POS - RLP_NUM],
                Rotation(rot_branch_init),
            );
            let is_branch_placeholder = is_branch_s_placeholder.expr() + is_branch_c_placeholder.expr();

            let is_leaf_in_first_storage_level = a!(is_account_leaf_in_added_branch, rot_into_account);

            let flag1 = a!(accs.s_mod_node_rlc);
            let flag2 = a!(accs.c_mod_node_rlc);
            let last_level = flag1.expr() * flag2.expr();
            let one_nibble = not::expr(flag1.expr()) * not::expr(flag2.expr());
            let is_long = flag1.expr() * not::expr(flag2.expr());
            let is_short = not::expr(flag1.expr()) * flag2.expr();

            // When `is_long` (the leaf value is longer than 1 byte), `s_main.rlp1` needs to be 248.
            // Example:
            // `[248 67 160 59 138 106 70 105 186 37 13 38 205 122 69 158 202 157 33 95 131 7 227 58 235 229 3 121 188 90 54 23 236 52 68 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 3]`
            ifx!{is_long => {
                require!(a!(s_main.rlp1) => 248);
            }}

            // The two values that store the information about what kind of case we have need to be boolean.
            require!(flag1 => bool);
            require!(flag2 => bool);

            ifx!{not::expr(is_leaf_in_first_storage_level.expr()), is_branch_placeholder => {
                // If leaf is in the first storage level, there cannot be a placeholder branch (it would push the
                // leaf into a second level) and we do not need to trigger any checks.
                // Note that in this case `is_branch_placeholder` gets some value from the account rows and we cannot use it.

                // We need to ensure that the RLC of the row is computed properly for `is_short` and
                // `is_long`. We compare the computed value with the value stored in `accumulators.acc_s.rlc`.
                ifx!{is_short.expr() + is_long.expr() => {
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
                    let rlc_last_level = rlc::expr(
                        &[s_main.rlp_bytes(), c_main.rlp_bytes()].concat()[..2].iter().map(|&byte| a!(byte)).collect::<Vec<_>>(),
                        &r,
                    );
                    require!(a!(accs.acc_s.rlc) => rlc_last_level);
                }}
            }}

            /* Storage drifted leaf key RLC */
            // We need to ensure that the drifted leaf has the proper key RLC. It needs to be the same as the key RLC
            // of this same leaf before it drifted to the new branch. The difference is that after being drifted the leaf
            // has one nibble less stored in the key - `drifted_pos` nibble that is in a branch parallel to the branch
            // placeholder (if it is an extension node there are more nibbles of a difference).
            // Leaf key S
            // Leaf value S
            // Leaf key C
            // Leaf value C
            // Drifted leaf (leaf in added branch)
            // Add case (S branch is placeholder):
            // Branch S           || Branch C
            // Placeholder branch || Added branch
            // Leaf S             || Leaf C
            //                     || Drifted leaf (this is Leaf S drifted into Added branch)
            // Leaf S needs to have the same key RLC as Drifted leaf.
            // Note that Leaf S key RLC is computed by taking the key RLC from Branch S and
            // then adding the bytes in Leaf key S row.
            // Drifted leaf RLC is computed by taking the key RLC from Added branch and
            // then adding the bytes in Drifted leaf row.
            // Delete case (C branch is placeholder):
            // Branch S                        || Branch C
            // Branch to be deleted            || Placeholder branch
            // Leaf S (leaf to be deleted)     || Leaf C
            // Leaf to be drifted one level up ||

            let is_ext_node = get_is_extension_node(meta, s_main.bytes, rot_branch_init);
            let is_branch_placeholder_in_first_level = a!(is_account_leaf_in_added_branch, rot_branch_init - 1);

            // We obtain the key RLC from the branch / extension node above the placeholder branch.
            // We then add the remaining key nibbles that are stored in the drifted leaf key and the final RLC
            // needs to be the same as the one stored in `accumulators.key.rlc` in the storage leaf key row
            // (not the drifted leaf). This means the storage leaf has the same key RLC before and after
            // it drifts into a new branch.

            // We need the intermediate key RLC right before `drifted_pos` is added to it.
            // If the branch parallel to the placeholder branch is an extension node,
            // we have the intermediate RLC stored in the extension node `accumulators.key.rlc`.
            // If it is a regular branch, we need to go one branch above to retrieve the RLC (if there is no level above,
            // we take 0).
            let key_rlc_cur = selectx!{is_ext_node => {
                a!(accs.key.rlc, -LEAF_DRIFTED_IND - 1)
            } elsex {
                selectx!{not::expr(is_branch_placeholder_in_first_level.expr()) => {
                    a!(accs.key.rlc, rot_branch_init - BRANCH_ROWS_NUM + 1)
                }}
            }};

            // Note: Branch key RLC is in the first branch child row (not in branch init). We need to go
            // in the branch above the placeholder branch.
            let branch_above_placeholder_mult = selectx!{is_branch_placeholder_in_first_level => {
                1.expr()
            } elsex {
                a!(accs.key.mult, rot_branch_init - BRANCH_ROWS_NUM + 1)
            }};

            // When we have only one nibble in the extension node, `mult_diff` is not used
            // (and set).
            let is_one_nibble = get_is_extension_node_one_nibble(meta, s_main.bytes, rot_branch_init);

            // `is_c16` and `is_c1` determine whether `drifted_pos` needs to be multiplied by 16 or 1.
            let is_c16 = a!(s_main.bytes[IS_BRANCH_C16_POS - RLP_NUM], rot_branch_init);
            let is_c1 = a!(s_main.bytes[IS_BRANCH_C1_POS - RLP_NUM], rot_branch_init);

            // `mult_diff` is the power of multiplier `r` and it corresponds to the number of nibbles in the extension node.
            // We need `mult_diff` because there is nothing stored in
            // `meta.query_advice(accs.key.mult, Rotation(-ACCOUNT_DRIFTED_LEAF_IND-1))` as we always use `mult_diff` in `extension_node_key.rs`.
            let key_rlc_mult = branch_above_placeholder_mult.expr() *
            selectx!{is_ext_node => {
                selectx!{is_one_nibble => {
                    selectx!{is_c1 => {
                        1.expr()
                    } elsex { // is_c16 TODO(Brecht): check if !c1 -> c16
                        r[0].expr()
                    }}
                } elsex {
                    // `mult_diff` is the power of multiplier `r` and it corresponds to the number of nibbles in the extension node.
                    // We need `mult_diff` because there is nothing stored in
                    // `meta.query_advice(accs.key.mult, Rotation(-ACCOUNT_DRIFTED_LEAF_IND-1))` as we always use `mult_diff` in `extension_node_key.rs`.
                    a!(accs.mult_diff, rot_branch_init + 1)
                }}
            } elsex {
                1.expr()
            }};

            // Key RLC of the drifted leaf needs to be the same as key RLC of the leaf
            // before it drifted down into extension/branch.

            // We retrieve `key_rlc` from the leaf before it drifted into a newly added branch. This RLC
            // need to be the same as the drifted leaf key RLC.
            let leaf_key_s_rlc = a!(accs.key.rlc, (-(LEAF_DRIFTED_IND - LEAF_KEY_S_IND)));
            let leaf_key_c_rlc = a!(accs.key.rlc, -(LEAF_DRIFTED_IND - LEAF_KEY_C_IND));

            ifx!{not::expr(is_leaf_in_first_storage_level.expr()) => {
                let drifted_pos_mult = key_rlc_mult.clone() * 16.expr() * is_c16.clone() + key_rlc_mult.clone() * is_c1.clone();
                // Any rotation that lands into branch children can be used.
                let key_rlc_start = key_rlc_cur + a!(drifted_pos, -17) * drifted_pos_mult;

                ifx!{is_short => {
                    // If `is_c1` and branch above is not a placeholder, we have 32 in `s_main.bytes[0]`.
                    // This is because `c1` in the branch above means there is an even number of nibbles left
                    // and we have an even number of nibbles in the leaf, the first byte (after RLP bytes
                    // specifying the length) of the key is 32.

                    // Note: `is_c1` is taken from the branch parallel to the placeholder branch. This is because
                    // the leaf in added branch is in this branch (parallel to placeholder branch).
                    // When computing the key RLC, `is_c1` means `drifted_pos` needs to be multiplied by 1, while
                    // `is_c16` means `drifted_pos` needs to be multiplied by 16.
                    ifx!{is_branch_placeholder, is_c1 => {
                        require!(a!(s_main.bytes[0]) => 32);
                    }}

                    // Note: drifted leaf key cannot reach `c_main.rlp1` because it has at most 31 nibbles.
                    // In case of 31 nibbles, the key occupies 32 bytes (in case of 32 nibbles and no
                    // branch above the leaf, the key occupies 33 bytes).

                    // No need to distinguish between `is_c16` and `is_c1` here as it was already
                    // when computing `key_rlc`.

                    // If `is_c16 = 1`, we have one nibble+48 in `s_main.bytes[0]`.
                    let key_rlc = key_rlc_start.expr() + rlc::expr(
                        &s_main.bytes.iter().enumerate().map(|(idx, &byte)| key_rlc_mult.expr() * (if idx == 0 { (a!(byte) - 48.expr()) * is_c16.expr() } else { a!(byte) })).collect::<Vec<_>>(),
                        &r,
                    );

                    // When `S` placeholder, `leaf_key_s_rlc` is the key RLC of the leaf before it drifted down
                    // in a new branch. We retrieve it from `LEAF_KEY_S` row.
                    // This value needs to be the same as the key RLC of the drifted leaf.
                    ifx!{is_branch_s_placeholder => {
                        require!(leaf_key_s_rlc => key_rlc);
                    }}

                    // When `C` placeholder, `leaf_key_c_rlc` is the key RLC of the leaf after its neighbour leaf
                    // has been deleted (and there were only two leaves, so the branch was deleted).
                    // We retrieve it from `LEAF_KEY_C` row.
                    // This value needs to be the same as the key RLC of the neighbour leaf (neighbour of
                    // the leaf that was deleted) before the leaf was deleted.
                    ifx!{is_branch_c_placeholder => {
                        require!(leaf_key_c_rlc => key_rlc);
                    }}
                }}

                ifx!{is_long => {
                    // Note: long means long leaf RLP, not extension node nibbles.

                    // If `is_c1` and branch above is not a placeholder, we have 32 in `s_main.bytes[1]`.
                    // This is because `is_c1` in the branch above means there is an even number of nibbles left
                    // and we have an even number of nibbles in the leaf, the first byte (after RLP bytes
                    // specifying the length) of the key is 32.
                    ifx!{is_c1 => {
                        require!(a!(s_main.bytes[1]) => 32);
                    }}

                    // If `is_c16 = 1`, we have one nibble+48 in `s_main.bytes[1]`.
                    let key_rlc = key_rlc_start.expr() + rlc::expr(
                        &[s_main.rlp_bytes(), c_main.rlp_bytes()].concat()[3..35].iter().enumerate().map(|(idx, &byte)| key_rlc_mult.expr() * (if idx == 0 { (a!(byte) - 48.expr()) * is_c16.expr() } else { a!(byte) })).collect::<Vec<_>>(),
                        &r,
                    );

                    // When `S` placeholder, `leaf_key_s_rlc` is the key RLC of the leaf before it drifted down
                    // in a new branch. We retrieve it from `LEAF_KEY_S` row.
                    // This value needs to be the same as the key RLC of the drifted leaf.
                    ifx!{is_branch_s_placeholder => {
                        require!(leaf_key_s_rlc => key_rlc);
                    }}

                    // When `C` placeholder, `leaf_key_c_rlc` is the key RLC of the leaf after its neighbour leaf
                    // has been deleted (and there were only two leaves, so the branch was deleted).
                    // We retrieve it from `LEAF_KEY_C` row.
                    // This value needs to be the same as the key RLC of the neighbour leaf (neighbour of
                    // the leaf that was deleted) before the leaf was deleted.
                    ifx!{is_branch_c_placeholder => {
                        require!(leaf_key_c_rlc => key_rlc);
                    }}
                }}

                ifx!{last_level => {
                    let s_rlp2 = a!(s_main.rlp2);
                    let key_rlc_one_nibble = key_rlc_start.expr() + (s_rlp2.expr() - 48.expr()) * key_rlc_mult;

                    // When the leaf is in the last level there are no nibbles stored in the key and `s_main.rlp2 = 32`.
                    ifx!{is_branch_placeholder => {
                        require!(s_rlp2 => 32.expr());
                    }}

                    ifx!{is_branch_s_placeholder => {
                        // When `S` placeholder, `leaf_key_s_rlc` is the key RLC of the leaf before it drifted down
                        // in a new branch. We retrieve it from `LEAF_KEY_S` row.
                        // This value needs to be the same as the key RLC of the drifted leaf.

                        // We do not need to add any nibbles to the key RLC as there are none stored in the storage leaf
                        // (last level).
                        // no nibbles in drifted leaf
                        require!(leaf_key_s_rlc => key_rlc_start);
                        // We only need to add one nibble to the key RLC.
                        // no nibbles in drifted leaf
                        require!(leaf_key_s_rlc => key_rlc_one_nibble);
                    }}

                    ifx!{is_branch_c_placeholder => {
                        // When `C` placeholder, `leaf_key_c_rlc` is the key RLC of the leaf after its neighbour leaf
                        // has been deleted (and there were only two leaves, so the branch was deleted).
                        // We retrieve it from `LEAF_KEY_C` row.
                        // This value needs to be the same as the key RLC of the neighbour leaf (neighbour of
                        // the leaf that was deleted) before the leaf was deleted.

                        // We do not need to add any nibbles to the key RLC as there are none stored in the storage leaf
                        // (last level).
                        // no nibbles in drifted leaf
                        require!(leaf_key_c_rlc => key_rlc_start);
                        // We only need to add one nibble to the key RLC.
                        // no nibbles in drifted leaf
                        require!(leaf_key_c_rlc => key_rlc_one_nibble);
                    }}
                }}
            }}

            let acc_mult = a!(accs.acc_s.mult);
            let len = get_leaf_len(meta, s_main.clone(), accs.clone(), 0);
            ifx!{not::expr(is_leaf_in_first_storage_level.expr()) => {
                ifx!{is_branch_s_placeholder => {
                    /* Leaf key in added branch: neighbour leaf in the added branch (S) */
                    // It needs to be ensured that the hash of the drifted leaf is in the parent branch
                    // at `drifted_pos` position.
                    // Rows:
                    // Leaf key S
                    // Leaf value S
                    // Leaf key C
                    // Leaf value C
                    // Drifted leaf (leaf in added branch)
                    // Add case (S branch is placeholder):
                    //     Branch S           || Branch C
                    //     Placeholder branch || Added branch
                    //     Leaf S             || Leaf C
                    //                        || Drifted leaf (this is Leaf S drifted into Added branch)
                    // We need to compute the RLC of the drifted leaf. We compute the intermediate RLC
                    // from the bytes in `LEAF_DRIFTED` row. And we retrieve the value from `LEAF_VALUE_S` row
                    // (where there is the same leaf, but before it drifted down into a new branch).
                    // Then we execute the lookup into a keccak table: `lookup(leaf_rlc, branch_child_at_drifted_pos_rlc)`.

                    // If branch placeholder in `S`, the leaf value is 3 rows above.
                    let rlc = a!(accs.acc_s.rlc) + rlc::expr(
                        &s_main.rlp_bytes().iter().map(|&byte| acc_mult.expr() * a!(byte, -3)).collect::<Vec<_>>(),
                        &extend_rand(&r),
                    );

                    // `s_mod_node_hash_rlc` in the placeholder branch stores the hash of a neighbour leaf.
                    // This is because `c_mod_node_hash_rlc` in the added branch stores the hash of
                    // `modified_node` (the leaf that has been added):
                    // Add case (S branch is placeholder):
                    //     Branch S           || Branch C
                    //     Placeholder branch (`s_mod_node_hash_rlc` stores `drifted_pos` node hash) || Added branch (`c_mod_node_hash_rlc` stores `modified_node` hash)
                    //     Leaf S             || Leaf C
                    //                        || Drifted leaf (this is Leaf S drifted into Added branch)
                    // That the stored value corresponds to the value in the non-placeholder branch at `drifted_pos`
                    // is checked in `branch_parallel.rs`.
                    // Any rotation that lands into branch children can be used.
                    let s_mod_node_hash_rlc = a!(accs.s_mod_node_rlc, -17);
                    require!((rlc, len, s_mod_node_hash_rlc) => @keccak);
                }}
                ifx!{is_branch_c_placeholder => {
                    /* Leaf key in added branch: neighbour leaf in the deleted branch (C) */
                    // It needs to be ensured that the hash of the drifted leaf is in the parent branch
                    // at `drifted_pos` position.
                    // Rows:
                    // Leaf key S
                    // Leaf value S
                    // Leaf key C
                    // Leaf value C
                    // Drifted leaf (leaf in added branch)
                    // Delete case (C branch is placeholder):
                    // Branch S                        || Branch C
                    // Branch to be deleted            || Placeholder branch
                    // Leaf S (leaf to be deleted)     || Leaf C
                    // Leaf to be drifted one level up ||
                    // We need to compute the RLC of the leaf that is a neighbour leaf of the leaf that is to be deleted.
                    // We compute the intermediate RLC from the bytes in `LEAF_DRIFTED` row.
                    // And we retrieve the value from `LEAF_VALUE_C` row
                    // (where there is the same leaf, but after it was moved one level up because of the deleted branch).
                    // Then we execute the lookup into a keccak table: `lookup(leaf_rlc, branch_child_at_drifted_pos_rlc)`.

                    // If branch placeholder in C, value is 1 above.
                    let rlc = a!(accs.acc_s.rlc) + rlc::expr(
                        &s_main.rlp_bytes().iter().map(|&byte| acc_mult.expr() * a!(byte, -1)).collect::<Vec<_>>(),
                        &extend_rand(&r),
                    );

                    // `c_mod_node_hash_rlc` in the placeholder branch stores the hash of a neighbour leaf.
                    // This is because `s_mod_node_hash_rlc` in the deleted branch stores the hash of
                    // `modified_node` (the leaf that is to be deleted):
                    // Delete case (C branch is placeholder):
                    //     Branch S                        || Branch C
                    //     Branch to be deleted (`s_mod_node_hash_rlc` stores `modified_node` hash) || Placeholder branch (`c_mod_node_hash_rlc` stores `drifted_pos` node hash)
                    //     Leaf S (leaf to be deleted)     || Leaf C
                    //     Leaf to be drifted one level up ||
                    // That the stored value corresponds to the value in the non-placeholder branch at `drifted_pos`
                    // is checked in `branch_parallel.rs`.
                    let c_mod_node_hash_rlc = a!(accs.c_mod_node_rlc, -17);
                    require!((rlc, len, c_mod_node_hash_rlc) => @keccak);
                }}
            }}

            // RLC bytes zero check
            // There are 0s in `s_main.bytes` after the last key nibble (this does not need
            // to be checked for `last_level` and `one_nibble` as in these cases
            // `s_main.bytes` are not used).
            ifx!{is_branch_placeholder, not::expr(is_leaf_in_first_storage_level) => {
                ifx!{is_short => {
                    require!((FixedTableTag::RMult, a!(s_main.rlp2) - 128.expr() + 2.expr(), a!(accs.acc_s.mult)) => @fixed);

                    for (idx, &byte) in [s_main.rlp_bytes(), c_main.rlp_bytes()].concat()[2..34].into_iter().enumerate() {
                        require!((FixedTableTag::RangeKeyLen256, a!(byte) * (a!(s_main.rlp2) - 128.expr() - (idx + 1).expr())) => @fixed);
                    }
                }}
                ifx!{is_long => {
                    require!((FixedTableTag::RMult, a!(s_main.bytes[0]) - 128.expr() + 3.expr(), a!(accs.acc_s.mult)) => @fixed);

                    for (idx, &byte) in [s_main.rlp_bytes(), c_main.rlp_bytes()].concat()[3..35].into_iter().enumerate() {
                        require!((FixedTableTag::RangeKeyLen256, a!(byte) * (a!(s_main.bytes[0]) - 128.expr() - (idx + 1).expr())) => @fixed);
                    }
                }}
            }}
        }}

        LeafKeyInAddedBranchConfig {
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
        row[1] != 0 just to avoid usize problems below (when row doesn't
        need to be assigned) Info whether leaf rlp is long or short.
        */
        let mut typ = "short";
        if row.get_byte(0) == 248 {
            typ = "long";
        } else if row.get_byte(1) == 32 {
            typ = "last_level";
        }
        mpt_config.assign_long_short(region, typ, offset).ok();

        pv.acc_s = F::zero();
        pv.acc_mult_s = F::one();
        let len = if row.get_byte(0) == 248 {
            (row.get_byte(2) - 128) as usize + 3
        } else {
            (row.get_byte(1) - 128) as usize + 2
        };
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
    }
}
