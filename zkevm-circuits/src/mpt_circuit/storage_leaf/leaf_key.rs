use gadgets::util::{not, Expr};
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Region, Value},
    plonk::VirtualCells,
    poly::Rotation,
};
use std::marker::PhantomData;

use crate::{
    circuit,
    evm_circuit::util::rlc,
    mpt_circuit::{
        helpers::BranchNodeInfo,
        param::{BRANCH_ROWS_NUM, S_START},
    },
    mpt_circuit::{helpers::MPTConstraintBuilder, FixedTableTag},
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
        let s_main = ctx.s_main;
        let accs = ctx.accumulators;
        let is_account_leaf_in_added_branch = ctx.account_leaf.is_in_added_branch;
        let denoter = ctx.denoter;
        let r = ctx.r.clone();

        let rot_parent = if is_s { -1 } else { -3 };
        let rot_branch_init = rot_parent - (BRANCH_ROWS_NUM - 1);
        let rot_branch_init_prev = rot_branch_init - BRANCH_ROWS_NUM;
        let rot_first_child = rot_branch_init + 1;
        let rot_first_child_prev = rot_first_child - BRANCH_ROWS_NUM;
        let rot_branch_parent = rot_branch_init - 1;

        circuit!([meta, cb.base], {
            let branch = BranchNodeInfo::new(meta, s_main, is_s, rot_branch_init);

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
                &ctx.rlp_bytes()[..36]
                    .iter()
                    .map(|&byte| a!(byte))
                    .collect::<Vec<_>>(),
                &r,
            );
            require!(a!(accs.acc_s.rlc) => rlc);

            // Calculate the key RLC
            let is_in_first_storage_level = a!(is_account_leaf_in_added_branch, rot_parent);
            let (key_rlc_prev, key_mult_prev, is_c16, nibbles_count_prev) = ifx! {not!(is_in_first_storage_level) => {
                ifx!{branch.is_placeholder() => {
                    ifx!{not!(a!(is_account_leaf_in_added_branch, rot_branch_parent)) => {
                        let branch_prev = BranchNodeInfo::new(meta, s_main, is_s, rot_branch_init_prev);
                        let rot_prev = rot_first_child_prev;
                        (a!(accs.key.rlc, rot_prev), a!(accs.key.mult, rot_prev), branch_prev.is_c16(), branch_prev.nibbles_counter().expr())
                    } elsex {
                        (0.expr(), 1.expr(), 0.expr(), 0.expr())
                    }}
                } elsex {
                    let rot = rot_first_child;
                    (a!(accs.key.rlc, rot), a!(accs.key.mult, rot), branch.is_c16(), branch.nibbles_counter().expr())
                }}
            } elsex {
                (0.expr(), 1.expr(), 0.expr(), 0.expr())
            }};
            // Set to key_mult_start * r if is_c16, else key_mult_start
            let key_mult =
                key_mult_prev.expr() * ifx! {is_c16 => { r[0].clone() } elsex { 1.expr() }};
            // TODO(Brecht): Shift the bytes in the witness so the same constraints can be
            // used?
            let key_rlc = key_rlc_prev.expr()
                + matchx! {
                    is_short => {
                        // If `is_c1` and branch above is not a placeholder, we have 32 in `s_main.bytes[0]`.
                        // This is because `is_c1` in the branch above means there is an even number of nibbles left
                        // and we have an even number of nibbles in the leaf, the first byte (after RLP bytes
                        // specifying the length) of the key is 32.
                        ifx!{not!(is_c16) => {
                            require!(a!(s_main.bytes[0]) => 32);
                        }}
                        // When `is_short` the first key byte is at `s_main.bytes[0]`.
                        // If is_c16, we have nibble+48 in s_main.bytes[0].
                        rlc::expr(
                            &ctx.rlp_bytes()[2..35].iter().enumerate().map(|(idx, &byte)|
                                (if idx == 0 { (a!(byte) - 48.expr()) * is_c16.expr() * key_mult_prev.expr() } else { a!(byte) * key_mult.expr() })).collect::<Vec<_>>(),
                            &[[1.expr()].to_vec(), r.to_vec()].concat(),
                        )
                    },
                    is_long => {
                        // `s_main.rlp1` needs to be 248.
                        require!(a!(s_main.rlp1) => 248);
                        // If `is_c1` and branch above is not a placeholder, we have 32 in `s_main.bytes[1]`.
                        // This is because `is_c1` in the branch above means there is an even number of nibbles left
                        // and we have an even number of nibbles in the leaf, the first byte (after RLP bytes
                        // specifying the length) of the key is 32.
                        ifx!{not!(is_c16) => {
                            require!(a!(s_main.bytes[1]) => 32);
                        }}
                        // When `is_long` the first key byte is at `s_main.bytes[1]`.
                        // If `is_c16`, we have nibble+48 in `s_main.bytes[1]`.
                        rlc::expr(
                            &ctx.rlp_bytes()[3..36].iter().enumerate().map(|(idx, &byte)|
                                (if idx == 0 { (a!(byte) - 48.expr()) * is_c16.expr() * key_mult_prev.expr() } else { a!(byte) * key_mult.expr() })).collect::<Vec<_>>(),
                            &[[1.expr()].to_vec(), r.to_vec()].concat(),
                        )
                    },
                    has_no_nibble => {
                        // When `last_level`, there is no nibble stored in the leaf key, it is just the value
                        // `32` in `s_main.rlp2`. In the `getProof` output, there is then the value stored immediately
                        // after `32`. However, in the MPT witness, we have value in the next row, so there are 0s
                        // in `s_main.bytes`.
                        require!(a!(s_main.rlp2) => 32);
                        // No nibble
                        0.expr()
                    },
                    has_one_nibble => {
                        // When there is only one nibble we take the last remaining nibble stored in `s_main.rlp2`.
                        (a!(s_main.rlp2) - 48.expr()) * key_mult_prev
                    },
                };
            require!(a!(accs.key.rlc) => key_rlc);

            // Get the number of bytes used for the key in the leaf.
            let key_len = matchx! {
                has_no_nibble.expr() + has_one_nibble.expr() => 1.expr(), // 1 byte in s_rlp2
                is_short => a!(s_main.rlp2) - 128.expr(),
                is_long => a!(s_main.bytes[0]) - 128.expr(),
            };
            // Total number of nibbles needs to be 64 (except in a placeholder leaf).
            let is_in_first_level = a!(denoter.sel(is_s), 1);
            let is_leaf_placeholder = is_in_first_level
                + ifx! {not!(is_in_first_storage_level) => {
                    a!(denoter.sel(is_s), rot_first_child)
                }};
            let num_nibbles = ifx! {is_c16 => {
                key_len.expr() * 2.expr() - 1.expr()
            } elsex {
                (key_len.expr() - 1.expr()) * 2.expr()
            }};
            ifx! {not!(is_leaf_placeholder) => {
                require!(nibbles_count_prev + num_nibbles => 64);
            }}

            // Num bytes used in RLC
            let num_bytes = key_len
                + matchx! {
                    has_no_nibble.expr() + has_one_nibble.expr() => 1.expr(), // 1 RLP byte
                    is_short => 2.expr(), // 2 RLP bytes
                    is_long => 3.expr(), // 3 RLP bytes
                };
            // Multiplier is number of bytes
            require!((FixedTableTag::RMult, num_bytes.expr(), a!(accs.acc_s.mult)) => @"mult");
            // RLC bytes zero check (subtract RLP bytes used)
            cb.set_length(num_bytes.expr() - 2.expr());
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

        // Store key_rlc into rlc2 to be later set in leaf value C row (to enable
        // lookups):
        pv.rlc2 = key_rlc_new;
    }
}
