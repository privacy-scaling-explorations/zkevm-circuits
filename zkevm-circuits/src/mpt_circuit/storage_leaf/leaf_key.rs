use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Region, Value},
    plonk::VirtualCells,
    poly::Rotation,
};
use std::marker::PhantomData;

use crate::{
    circuit,
    mpt_circuit::{
        helpers::BranchNodeInfo,
        param::{BRANCH_ROWS_NUM, S_START},
    },
    mpt_circuit::{
        helpers::{MPTConstraintBuilder, StorageLeafInfo},
        param::KEY_LEN_IN_NIBBLES,
        FixedTableTag,
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

- We need to ensure that the storage leaf is at the key specified in `key_rlc` column (used
by MPT lookup). To do this we take the key RLC computed in the branches above the leaf
and add the remaining bytes (nibbles) stored in the leaf.
We also ensure that the number of all nibbles (in branches / extension nodes above
the leaf and in the leaf) is 64.
- For leaf under the placeholder branch we would not need to check the key RLC -
this leaf is something we did not ask for, it is just a leaf that happened to be
at the place where adding a new leaf causes adding a new branch.
For example, when adding a leaf `L` causes that a leaf `L1`
(this will be the leaf under the branch placeholder)
is replaced by a branch, we get a placeholder branch at `S` side
and leaf `L1` under it. However, the key RLC needs to be compared for leaf `L`,
because this is where the modification takes place.
In delete, the situation is turned around.
However, we also check that the key RLC for `L1` is computed properly because
we need `L1` key RLC for the constraints for checking that leaf `L1` is the same
as the drifted leaf in the branch parallel. This can be checked by
comparing the key RLC of the leaf before being replaced by branch and the key RLC
of this same leaf after it drifted into a branch.
Constraints for this are in `leaf_key_in_added_branch.rs`.
Note that the hash of a leaf `L1` needs to be checked to be in the branch
above the placeholder branch - this is checked in `leaf_value.rs`.
Note: `last_level` cannot occur in a leaf after placeholder branch, because being
after placeholder branch means this leaf drifted down into a new branch (in a parallel
proof) and thus cannot be in the last level.
- key rlc is in the first branch node (not branch init)
- If the last branch is placeholder (the placeholder branch is the same as its
parallel counterpart), there is a branch `modified_node` nibble already
incorporated in `key_rlc`. That means we need to ignore the first nibble here
(in leaf key).

*/

#[derive(Clone, Debug, Default)]
pub(crate) struct LeafKeyConfig<F> {
    _marker: PhantomData<F>,
}

impl<F: FieldExt> LeafKeyConfig<F> {
    pub fn configure(
        meta: &mut VirtualCells<'_, F>,
        cb: &mut MPTConstraintBuilder<F>,
        ctx: MPTContext<F>,
        is_s: bool,
    ) -> Self {
        let accs = ctx.accumulators;

        let rot_parent = if is_s { -1 } else { -3 };
        let rot_branch_init = rot_parent - (BRANCH_ROWS_NUM - 1);
        let rot_branch_init_prev = rot_branch_init - BRANCH_ROWS_NUM;
        let rot_first_child = rot_branch_init + 1;
        let rot_first_child_prev = rot_first_child - BRANCH_ROWS_NUM;

        circuit!([meta, cb.base], {
            let storage = StorageLeafInfo::new(meta, ctx.clone(), is_s, 0);

            // The two flag values need to be boolean.
            require!(storage.flag1 => bool);
            require!(storage.flag2 => bool);

            // Calculate and store the leaf data RLC
            require!(a!(accs.acc_s.rlc) => ctx.rlc(meta, 0..36, 0));

            // Get the key data from the branch above (if any)
            let (key_rlc_prev, key_mult_prev, is_key_odd, nibbles_count_prev) = ifx! {not!(storage.is_below_account(meta)) => {
                let branch = BranchNodeInfo::new(meta, ctx.clone(), is_s, rot_branch_init);
                ifx!{branch.is_placeholder() => {
                    ifx!{not!(branch.is_below_account(meta)) => {
                        let branch_prev = BranchNodeInfo::new(meta, ctx.clone(), is_s, rot_branch_init_prev);
                        let rot_prev = rot_first_child_prev;
                        (a!(accs.key.rlc, rot_prev), a!(accs.key.mult, rot_prev), branch_prev.is_key_odd(), branch_prev.nibbles_counter().expr())
                    } elsex {
                        (0.expr(), 1.expr(), 0.expr(), 0.expr())
                    }}
                } elsex {
                    let rot = rot_first_child;
                    (a!(accs.key.rlc, rot), a!(accs.key.mult, rot), branch.is_key_odd(), branch.nibbles_counter().expr())
                }}
            } elsex {
                (0.expr(), 1.expr(), 0.expr(), 0.expr())
            }};

            // Calculate and store the key RLC.
            let key_rlc = key_rlc_prev.expr()
                + storage.key_rlc(
                    meta,
                    &mut cb.base,
                    key_mult_prev,
                    is_key_odd.expr(),
                    1.expr(),
                    true,
                );
            require!(a!(accs.key.rlc) => key_rlc);

            // Total number of nibbles needs to be KEY_LEN_IN_NIBBLES (except in a
            // placeholder leaf).
            // TODO(Brecht): why not in placeholder leaf?
            ifx! {not!(storage.is_placeholder(meta)) => {
                let num_nibbles = storage.num_key_nibbles(meta, is_key_odd.expr());
                require!(nibbles_count_prev + num_nibbles => KEY_LEN_IN_NIBBLES);
            }}

            // Num bytes used in RLC
            let num_bytes = storage.num_bytes_on_key_row(meta);
            // Multiplier is number of bytes
            require!((FixedTableTag::RMult, num_bytes.expr(), a!(accs.acc_s.mult)) => @"mult");
            // RLC bytes zero check
            cb.set_length(num_bytes.expr());
        });

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
        pv.storage_key_rlc = key_rlc_new;

        // Store key_rlc into rlc2 to be later set in leaf value C row (to enable
        // lookups):
        pv.rlc2 = key_rlc_new;
    }
}
