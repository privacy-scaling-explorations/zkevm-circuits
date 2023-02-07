use halo2_proofs::{arithmetic::FieldExt, circuit::Region, plonk::VirtualCells, poly::Rotation};
use std::marker::PhantomData;

use crate::{
    circuit,
    circuit_tools::{RLCChainable, ConstraintBuilder},
    mpt_circuit::{
        helpers::StorageLeafInfo,
        param::{BRANCH_ROWS_NUM, LEAF_DRIFTED_IND, LEAF_KEY_C_IND, LEAF_KEY_S_IND},
    },
    mpt_circuit::{
        helpers::{get_parent_rlc_state, BranchNodeInfo, MPTConstraintBuilder},
        param::{LEAF_VALUE_C_IND, LEAF_VALUE_S_IND},
        witness_row::MptWitnessRow,
        FixedTableTag, MPTContext,
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
        cb: &mut MPTConstraintBuilder<F>,
        ctx: MPTContext<F>,
    ) -> Self {
        let s_main = ctx.s_main;
        let accs = ctx.accumulators;
        let r = ctx.r.clone();

        let rot_branch_init = -LEAF_DRIFTED_IND - BRANCH_ROWS_NUM;
        let rot_parent = -LEAF_DRIFTED_IND - 1;
        let rot_branch_child = -BRANCH_ROWS_NUM + 2;
        let rot_key_s = -(LEAF_DRIFTED_IND - LEAF_KEY_S_IND);
        let rot_value_s = -(LEAF_DRIFTED_IND - LEAF_VALUE_S_IND);
        let rot_key_c = -(LEAF_DRIFTED_IND - LEAF_KEY_C_IND);
        let rot_value_c = -(LEAF_DRIFTED_IND - LEAF_VALUE_C_IND);

        circuit!([meta, cb.base], {
            let storage = StorageLeafInfo::new(meta, ctx.clone(), true, rot_key_s);
            ifx! {not!(storage.is_below_account(meta)) => {
                let branch = BranchNodeInfo::new(meta, ctx.clone(), true, rot_branch_init);
                let drifted_storage = StorageLeafInfo::new(meta, ctx.clone(), true, 0);

                // The two flag values need to be boolean.
                require!(drifted_storage.flag1 => bool);
                require!(drifted_storage.flag2 => bool);

                // Calculate and store the leaf RLC (RLP + key)
                let drifted_rlc = a!(accs.acc_s.rlc);
                require!(drifted_rlc => ctx.rlc(meta, 0..36, 0));

                // We need the intermediate key RLC right before `drifted_index` is added to it.
                // If the branch parallel to the placeholder branch is an extension node,
                // we have the intermediate RLC stored in the extension node `accs.key.rlc`.
                let is_branch_in_first_level = branch.is_below_account(meta);
                let (key_rlc_prev, key_mult_prev) = get_parent_rlc_state(meta, ctx.clone(), is_branch_in_first_level, rot_parent);
                // Calculate the drifted key RLC
                let drifted_key_rlc = key_rlc_prev.expr() +
                    branch.drifted_nibble_rlc(meta, &mut cb.base, key_mult_prev.expr()) +
                    drifted_storage.key_rlc(meta, &mut cb.base, key_mult_prev, branch.is_key_odd(), r[0].expr(), true, 0);

                // Check zero bytes and mult_diff
                let mult = a!(accs.acc_s.mult);
                ifx!{branch.is_placeholder_s_or_c() => {
                    // Num bytes used in RLC
                    let num_bytes = drifted_storage.num_bytes_on_key_row(meta);
                    // Multiplier is number of bytes
                    require!((FixedTableTag::RMult, num_bytes.expr(), mult) => @"mult");
                    // RLC bytes zero check
                    cb.set_length(num_bytes.expr());
                }}

                // Check that the drifted leaf is unchanged and is stored at `drifted_index`.
                let calc_rlc = |is_s, meta: &mut VirtualCells<'_, F>, cb: &mut ConstraintBuilder<F>| {
                    circuit!([meta, cb], {
                        let rot_key = if is_s { rot_key_s } else { rot_key_c };
                        let rot_value = if is_s { rot_value_s } else { rot_value_c };
                        // Complete the drifted leaf rlc by adding the bytes on the value row
                        let drifted_rlc = (drifted_rlc.expr(), mult.expr()).rlc_chain(s_main.rlc(meta, rot_value, &r));
                        (true.expr(), a!(accs.key.rlc, rot_key), drifted_rlc, a!(accs.mod_node_rlc(is_s), rot_branch_child))
                    })
                };
                let (do_checks, key_rlc, drifted_rlc, mod_hash) = matchx! {
                    branch.is_placeholder_s() => {
                        // Neighbour leaf in the added branch
                        // - `leaf_key_s_rlc` is the key RLC of the leaf before it drifted down
                        // in a new branch.
                        // - `s_mod_node_rlc` in the placeholder branch stores the hash of a neighbour leaf.
                        // This is because `c_mod_node_rlc` in the added branch stores the hash of
                        // `modified_index` (the leaf that has been added).
                        calc_rlc(true, meta, &mut cb.base)
                    },
                    branch.is_placeholder_c() => {
                        // Neighbour leaf in the deleted branch
                        // -`leaf_key_c_rlc` is the key RLC of the leaf after its neighbour leaf
                        // has been deleted (and there were only two leaves, so the branch was deleted).
                        // - `c_mod_node_hash_rlc` in the placeholder branch stores the hash of a neighbour leaf.
                        // This is because `s_mod_node_rlc` in the deleted branch stores the hash of
                        // `modified_index` (the leaf that is to be deleted).
                        calc_rlc(false, meta, &mut cb.base)
                    },
                    _ => (false.expr(), 0.expr(), 0.expr(), 0.expr()),
                };
                ifx! {do_checks => {
                    // The key of the drifted leaf needs to match the key of the leaf
                    require!(key_rlc => drifted_key_rlc);
                    // The drifted leaf needs to be stored in the branch at `drifted_index`.
                    require!((1, drifted_rlc, drifted_storage.num_bytes(meta), mod_hash) => @"keccak");
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
    }
}
