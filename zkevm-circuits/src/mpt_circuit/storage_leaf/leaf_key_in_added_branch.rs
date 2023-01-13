use gadgets::util::{not, Expr};
use halo2_proofs::{arithmetic::FieldExt, circuit::Region, plonk::VirtualCells, poly::Rotation};
use std::marker::PhantomData;

use crate::{
    circuit,
    evm_circuit::util::rlc,
    mpt_circuit::{helpers::BranchNodeInfo, witness_row::MptWitnessRow, FixedTableTag, MPTContext},
    mpt_circuit::{
        helpers::{get_leaf_len, BaseConstraintBuilder},
        param::{BRANCH_ROWS_NUM, LEAF_DRIFTED_IND, LEAF_KEY_C_IND, LEAF_KEY_S_IND},
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


Note: The leaf value is not stored in this row, but it needs to be the same
as the leaf value before it drifted down to the new branch, so we can
retrieve it from the row of a leaf before a drift. We need the leaf value to
build the leaf RLC to check that the hash of a drifted leaf is in the
new branch.
It needs to be ensured that the leaf intermediate RLC (containing the leaf
key bytes) is properly computed. The intermediate RLC is then used to
compute the final leaf RLC (containing the leaf value bytes too).
Finally, the lookup is used to check that the hash that
corresponds to the leaf RLC is in the parent branch at `drifted_pos`
position.
drifted leaf appears only when there is a placeholder branch

We obtain the key RLC from the branch / extension node above the placeholder branch.
We then add the remaining key nibbles that are stored in the drifted leaf key and the final RLC
needs to be the same as the one stored in `accumulators.key.rlc` in the storage leaf key row
(not the drifted leaf). This means the storage leaf has the same key RLC before and after
it drifts into a new branch.

We need to ensure that the drifted leaf has the proper key RLC. It needs to be the same as the key RLC
of this same leaf before it drifted to the new branch. The difference is that after being drifted the leaf
has one nibble less stored in the key - `drifted_pos` nibble that is in a branch parallel to the branch
placeholder (if it is an extension node there are more nibbles of a difference).
Leaf key S
Leaf value S
Leaf key C
Leaf value C
Drifted leaf (leaf in added branch)
Add case (S branch is placeholder):
Branch S           || Branch C
Placeholder branch || Added branch
Leaf S             || Leaf C
                   || Drifted leaf (this is Leaf S drifted into Added branch)
Leaf S needs to have the same key RLC as Drifted leaf.
Note that Leaf S key RLC is computed by taking the key RLC from Branch S and
then adding the bytes in Leaf key S row.
Drifted leaf RLC is computed by taking the key RLC from Added branch and
then adding the bytes in Drifted leaf row.
Delete case (C branch is placeholder):
Branch S                        || Branch C
Branch to be deleted            || Placeholder branch
Leaf S (leaf to be deleted)     || Leaf C
Leaf to be drifted one level up ||

/* Leaf key in added branch: neighbour leaf in the added branch (S) */
It needs to be ensured that the hash of the drifted leaf is in the parent branch
at `drifted_pos` position.
Rows:
Leaf key S
Leaf value S
Leaf key C
Leaf value C
Drifted leaf (leaf in added branch)
Add case (S branch is placeholder):
    Branch S           || Branch C
    Placeholder branch || Added branch
    Leaf S             || Leaf C
                       || Drifted leaf (this is Leaf S drifted into Added branch)
We need to compute the RLC of the drifted leaf. We compute the intermediate RLC
from the bytes in `LEAF_DRIFTED` row. And we retrieve the value from `LEAF_VALUE_S` row
(where there is the same leaf, but before it drifted down into a new branch).
Then we execute the lookup into a keccak table: `lookup(leaf_rlc, branch_child_at_drifted_pos_rlc)`.

`s_mod_node_hash_rlc` in the placeholder branch stores the hash of a neighbour leaf.
This is because `c_mod_node_hash_rlc` in the added branch stores the hash of
`modified_node` (the leaf that has been added):
Add case (S branch is placeholder):
    Branch S           || Branch C
    Placeholder branch (`s_mod_node_hash_rlc` stores `drifted_pos` node hash) || Added branch (`c_mod_node_hash_rlc` stores `modified_node` hash)
    Leaf S             || Leaf C
                       || Drifted leaf (this is Leaf S drifted into Added branch)
That the stored value corresponds to the value in the non-placeholder branch at `drifted_pos`
is checked in `branch_rlc.rs`.

/* Leaf key in added branch: neighbour leaf in the deleted branch (C) */
It needs to be ensured that the hash of the drifted leaf is in the parent branch
at `drifted_pos` position.
Rows:
Leaf key S
Leaf value S
Leaf key C
Leaf value C
Drifted leaf (leaf in added branch)
Delete case (C branch is placeholder):
Branch S                        || Branch C
Branch to be deleted            || Placeholder branch
Leaf S (leaf to be deleted)     || Leaf C
Leaf to be drifted one level up ||
We need to compute the RLC of the leaf that is a neighbour leaf of the leaf that is to be deleted.
We compute the intermediate RLC from the bytes in `LEAF_DRIFTED` row.
And we retrieve the value from `LEAF_VALUE_C` row
(where there is the same leaf, but after it was moved one level up because of the deleted branch).
Then we execute the lookup into a keccak table: `lookup(leaf_rlc, branch_child_at_drifted_pos_rlc)`.

`c_mod_node_hash_rlc` in the placeholder branch stores the hash of a neighbour leaf.
This is because `s_mod_node_hash_rlc` in the deleted branch stores the hash of
`modified_node` (the leaf that is to be deleted):
Delete case (C branch is placeholder):
    Branch S                        || Branch C
    Branch to be deleted (`s_mod_node_hash_rlc` stores `modified_node` hash) || Placeholder branch (`c_mod_node_hash_rlc` stores `drifted_pos` node hash)
    Leaf S (leaf to be deleted)     || Leaf C
    Leaf to be drifted one level up ||
That the stored value corresponds to the value in the non-placeholder branch at `drifted_pos`
is checked in `branch_rlc.rs`.

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
        let rot_branch_parent = rot_branch_init - 1;
        let rot_first_child = rot_branch_init + 1;
        let rot_first_child_prev = rot_first_child - BRANCH_ROWS_NUM;
        let rot_parent = -LEAF_DRIFTED_IND - 1;
        let rot_branch_child = -BRANCH_ROWS_NUM + 2;
        let rot_key_s = -(LEAF_DRIFTED_IND - LEAF_KEY_S_IND);
        let rot_key_c = -(LEAF_DRIFTED_IND - LEAF_KEY_C_IND);

        circuit!([meta, cb], {
            let branch = BranchNodeInfo::new(meta, s_main, true, rot_branch_init);

            let flag1 = a!(accs.s_mod_node_rlc);
            let flag2 = a!(accs.c_mod_node_rlc);
            let has_no_nibble = flag1.expr() * flag2.expr();
            let has_one_nibble = not!(flag1) * not!(flag2);
            let is_long = flag1.expr() * not!(flag2);
            let is_short = not!(flag1) * flag2.expr();

            // The two flag values need to be boolean.
            require!(flag1 => bool);
            require!(flag2 => bool);

            // Calculate and store the leaf data RLC
            let rlc = rlc::expr(
                &[s_main.rlp_bytes(), c_main.rlp_bytes()].concat()[..36]
                    .iter()
                    .map(|&byte| a!(byte))
                    .collect::<Vec<_>>(),
                &r,
            );
            require!(a!(accs.acc_s.rlc) => rlc);

            let is_in_first_storage_level = a!(is_account_leaf_in_added_branch, rot_parent);
            ifx! {not!(is_in_first_storage_level) => {
                // We need the intermediate key RLC right before `drifted_pos` is added to it.
                // If the branch parallel to the placeholder branch is an extension node,
                // we have the intermediate RLC stored in the extension node `accumulators.key.rlc`.
                // If it is a regular branch, we need to go one branch above to retrieve the RLC (if there is no level above,
                // we take 0).
                let is_branch_placeholder_in_first_level = a!(is_account_leaf_in_added_branch, rot_branch_parent);
                let (key_rlc_prev, key_mult_prev) = ifx!{branch.is_extension() => {
                    let key_mult_prev = ifx!{is_branch_placeholder_in_first_level => {
                        1.expr()
                    } elsex {
                        a!(accs.key.mult, rot_first_child_prev)
                    }};
                    (a!(accs.key.rlc, rot_parent), key_mult_prev * a!(accs.mult_diff, rot_first_child))
                } elsex {
                    ifx!{is_branch_placeholder_in_first_level => {
                        (0.expr(), 1.expr())
                    } elsex {
                        (a!(accs.key.rlc, rot_first_child_prev), a!(accs.key.mult, rot_first_child_prev))
                    }}
                }};
                let drifted_pos_mult = key_mult_prev.expr() * ifx!{branch.is_c16() => { 16.expr() } elsex { 1.expr() }};
                let key_rlc_prev = key_rlc_prev + a!(drifted_pos, rot_branch_child) * drifted_pos_mult;
                let key_rlc = key_rlc_prev.expr() + matchx! {
                    is_short => {
                        // If `is_c1` and branch above is not a placeholder, we have 32 in `s_main.bytes[0]`.
                        // This is because `c1` in the branch above means there is an even number of nibbles left
                        // and we have an even number of nibbles in the leaf, the first byte (after RLP bytes
                        // specifying the length) of the key is 32.
                        ifx!{branch.is_c1() => {
                            require!(a!(s_main.bytes[0]) => 32);
                        }}
                        // Note: drifted leaf key cannot reach `c_main.rlp1` because it has at most 31 nibbles.
                        // In case of 31 nibbles, the key occupies 32 bytes (in case of 32 nibbles and no
                        // branch above the leaf, the key occupies 33 bytes).
                        // If `is_c16 = 1`, we have one nibble+48 in `s_main.bytes[0]`.
                        rlc::expr(
                            &s_main.bytes.iter().enumerate().map(|(idx, &byte)| key_mult_prev.expr() * (if idx == 0 { (a!(byte) - 48.expr()) * branch.is_c16() } else { a!(byte) })).collect::<Vec<_>>(),
                            &r,
                        )
                    },
                    is_long => {
                        // When `is_long` (the leaf value is longer than 1 byte), `s_main.rlp1` needs to be 248.
                        require!(a!(s_main.rlp1) => 248);
                        // Note: long means long leaf RLP, not extension node nibbles.
                        // If `is_c1` and branch above is not a placeholder, we have 32 in `s_main.bytes[1]`.
                        // This is because `is_c1` in the branch above means there is an even number of nibbles left
                        // and we have an even number of nibbles in the leaf, the first byte (after RLP bytes
                        // specifying the length) of the key is 32.
                        ifx!{branch.is_c1() => {
                            require!(a!(s_main.bytes[1]) => 32);
                        }}
                        // If `is_c16 = 1`, we have one nibble+48 in `s_main.bytes[1]`.
                        rlc::expr(
                            &[s_main.rlp_bytes(), c_main.rlp_bytes()].concat()[3..35].iter().enumerate().map(|(idx, &byte)| key_mult_prev.expr() * (if idx == 0 { (a!(byte) - 48.expr()) * branch.is_c16() } else { a!(byte) })).collect::<Vec<_>>(),
                            &r,
                        )
                    },
                    has_no_nibble => {
                        let s_rlp2 = a!(s_main.rlp2);
                        // When the leaf is in the last level there are no nibbles stored in the key and `s_main.rlp2 = 32`.
                        require!(s_rlp2 => 32.expr());
                        (s_rlp2.expr() - 48.expr()) * key_mult_prev.expr()
                    },
                    has_one_nibble => 0.expr(),
                };
                // Check that the drifted leaf key is unchanged.
                let acc_mult = a!(accs.acc_s.mult);
                let len = get_leaf_len(meta, s_main.clone(), accs.clone(), 0);
                let (stored_key_rlc, mod_rlc, do_lookup, mod_hash) = matchx! {
                    branch.is_branch_s_placeholder => {
                        // When `S` placeholder, `leaf_key_s_rlc` is the key RLC of the leaf before it drifted down
                        // in a new branch. We retrieve it from `LEAF_KEY_S` row.
                        // This value needs to be the same as the key RLC of the drifted leaf.
                        /* Leaf key in added branch: neighbour leaf in the added branch (S) */
                        // It needs to be ensured that the hash of the drifted leaf is in the parent branch
                        // at `drifted_pos` position.
                        // If branch placeholder in `S`, the leaf value is 3 rows above.
                        let rlc = a!(accs.acc_s.rlc) + rlc::expr(
                            &s_main.rlp_bytes().iter().map(|&byte| acc_mult.expr() * a!(byte, -3)).collect::<Vec<_>>(),
                            &r,
                        );
                        // `s_mod_node_hash_rlc` in the placeholder branch stores the hash of a neighbour leaf.
                        // This is because `c_mod_node_hash_rlc` in the added branch stores the hash of
                        // `modified_node` (the leaf that has been added).
                        (a!(accs.key.rlc, rot_key_s), rlc, true.expr(), a!(accs.mod_node_rlc(true), rot_branch_child))
                    },
                    branch.is_branch_c_placeholder => {
                        // When `C` placeholder, `leaf_key_c_rlc` is the key RLC of the leaf after its neighbour leaf
                        // has been deleted (and there were only two leaves, so the branch was deleted).
                        // We retrieve it from `LEAF_KEY_C` row.
                        // This value needs to be the same as the key RLC of the neighbour leaf (neighbour of
                        // the leaf that was deleted) before the leaf was deleted.
                        /* Leaf key in added branch: neighbour leaf in the deleted branch (C) */
                        // It needs to be ensured that the hash of the drifted leaf is in the parent branch
                        // at `drifted_pos` position.
                        // If branch placeholder in C, value is 1 above.
                        let rlc = a!(accs.acc_s.rlc) + rlc::expr(
                            &s_main.rlp_bytes().iter().map(|&byte| acc_mult.expr() * a!(byte, -1)).collect::<Vec<_>>(),
                            &r,
                        );
                        // `c_mod_node_hash_rlc` in the placeholder branch stores the hash of a neighbour leaf.
                        // This is because `s_mod_node_hash_rlc` in the deleted branch stores the hash of
                        // `modified_node` (the leaf that is to be deleted).
                        (a!(accs.key.rlc, rot_key_c), rlc, true.expr(), a!(accs.mod_node_rlc(false), rot_branch_child))
                    },
                    not!(branch.is_s_or_c_placeholder()) => {
                        (key_rlc.expr(), 0.expr(), false.expr(), 0.expr())
                    },
                };
                require!(stored_key_rlc => key_rlc);
                ifx! {do_lookup => {
                    require!((1, mod_rlc, len, mod_hash) => @"keccak");
                }}

                // Check zero bytes and mult_diff
                // TODO(Brecht): share code with leaf_key.rs
                ifx!{branch.is_s_or_c_placeholder() => {
                    // Get the number of bytes used for the key in the leaf.
                    let key_len = matchx! {
                        has_no_nibble.expr() + has_one_nibble.expr() => 1.expr(), // 1 byte in s_rlp2
                        is_short => a!(s_main.rlp2) - 128.expr(),
                        is_long => a!(s_main.bytes[0]) - 128.expr(),
                    };
                    // Num bytes used in RLC
                    let num_bytes = key_len + matchx! {
                        has_no_nibble.expr() + has_one_nibble.expr() => 1.expr(), // 1 RLP byte
                        is_short => 2.expr(),                                     // 2 RLP bytes
                        is_long => 3.expr(),                                      // 3 RLP bytes
                    };
                    // Multiplier is number of bytes
                    require!((FixedTableTag::RMult, num_bytes.expr(), a!(accs.acc_s.mult)) => @"mult");
                    // RLC bytes zero check (subtract RLP bytes used)
                    cb.set_range_length(num_bytes.expr() - 2.expr());
                }}
            }}
        });

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
