use gadgets::util::{not, sum, Expr};
use halo2_proofs::{
    arithmetic::FieldExt,
    plonk::{Expression, VirtualCells},
    poly::Rotation,
};
use std::marker::PhantomData;

use crate::{
    circuit,
    circuit_tools::DataTransition,
    evm_circuit::util::rlc,
    mpt_circuit::MPTContext,
    mpt_circuit::{helpers::BranchNodeInfo, param::BRANCH_ROWS_NUM},
    mpt_circuit::{helpers::MPTConstraintBuilder, FixedTableTag},
};

/*
A branch occupies 19 rows:
BRANCH.IS_INIT
BRANCH.IS_CHILD 0
...
BRANCH.IS_CHILD 15
BRANCH.IS_EXTENSION_NODE_S
BRANCH.IS_EXTENSION_NODE_C

Example:

[1 0 1 0 248 81 0 248 81 0 14 1 0 6 1 0 0 0 0 1 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0]
[0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1]
[0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1]
[0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1]
[0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1]
[0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1]
[0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1]
[0 160 29 143 36 49 6 106 55 88 195 10 34 208 147 134 155 181 100 142 66 21 255 171 228 168 85 11 239 170 233 241 171 242 0 160 29 143 36 49 6 106 55 88 195 10 34 208 147 134 155 181 100 142 66 21 255 171 228 168 85 11 239 170 233 241 171 242 1]
[0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1]
[0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1]
[0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1]
[0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1]
[0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1]
[0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1]
[0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1]
[0 160 135 117 154 48 1 221 143 224 133 179 90 254 130 41 47 5 101 84 204 111 220 62 215 253 155 107 212 69 138 221 91 174 0 160 135 117 154 48 1 221 143 224 133 179 90 254 130 41 47 5 101 84 204 111 220 62 215 253 155 107 212 69 138 221 91 174 1]
[0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1]
[226 30 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 160 30 252 7 160 150 158 68 221 229 48 73 181 91 223 120 156 43 93 5 199 95 184 42 20 87 178 65 243 228 156 123 174 0 16]
[0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 160 30 252 7 160 150 158 68 221 229 48 73 181 91 223 120 156 43 93 5 199 95 184 42 20 87 178 65 243 228 156 123 174 0 17]

The last two rows present the extension node. This might be a bit misleading, because the extension
node appears in the trie above the branch (the first 17 rows).

The constraints in `branch_key.rs` checks whether the key RLC is being properly
computed using `modified_node`. Note that `modified_node` presents the branch node
to be modified and is one of the nibbles of a key.

Let us have the following scenario:

```
Branch1:
  node1_0
  node1_1     <- modified_node
  ...
  node1_15
Branch2
  node2_0
  ...
  node2_7    <- modified_node
  ...
  node2_15
Branch3
  node3_0
  ...
  node3_5    <- modified_node
  ...
  node3_15
Branch4
  node4_0
  ...
  node4_11    <- modified_node
  ...
  node4_15
Leaf1
```

We have four branches and finally a leaf in the fourth branch. The modified nodes are: `1, 7, 5, 11`.
The modified nodes occupy two bytes, the remaining 30 bytes are stored in `Leaf1`:
`b_0, ..., b_29`.

The key at which the change occurs is thus: `1 * 16 + 7, 5 * 16 + 11, b_0, ..., b_29`.
The RLC of the key is: `(1 * 16 + 7) + (5 * 16 + 11) * r + b_0 * r^2 + b_29 * r^31`.

In each branch we check whether the intermediate RLC is computed correctly. The intermediate
values are stored in `accumulators.key`. There is always the actual RLC value and the multiplier
that is to be used when adding the next summand: `accumulators.key.rlc, accumulators.key.mult`.

For example, in `Branch1` we check whether the intermediate RLC is `1 * 16`.
In `Branch2`, we check whether the intermediate RLC is `rlc_prev_branch_init_row + 7`.
In `Branch3`, we check whether the intermediate RLC is `rlc_prev_branch_init_row + 5 * 16 * r`.
In `Branch4`, we check whether the intermediate RLC is `rlc_prev_branch_init_row + 11 * r`.

There are auxiliary columns `sel1` and `sel2` which specify whether we are in branch where
the nibble has to be multiplied by 16 or by 1. `sel1 = 1` means multiplying by 16,
`sel2 = 1` means multiplying by 1.

TODO: extension node longer than 55 bytes - we leave this for now as it is very unlikely to happen.

ExtensionNodeConfig supports extension nodes longer than 55 bytes, however ExtensionNodeKeyConfig
currently does not. See below.

Currently, we do not store key for the C extension node - it is always the same as key for
the S extension node. However, it can happen that one extension node is longer than 55 bytes and one not
(being longer than 55 bytes is very unlikely because that would mean the extension need to be at least
22 bytes long - adding 32 for branch hash and 2 RLP bytes would give us 56).
In this case the longer than 55 bytes extension node starts as: [248, remaining_length, extension_bytes_length, ...],
while the shorter than 55 bytes extension node starts as: [247, extension_bytes_length, ...].

We do not have space to store C RLP & key into extension node C row as we already store key nibbles there (same
for both extension nodes).

The best seems to be to handle four different cases:
 - s_short, c_short (not to be confused with short/long meaning nibbles, here it means the whole ext. node longer or shorter than 55 bytes)
 - s_short, c_long
 - s_long, c_short
 - s_long, c_long

Using this approach we do not need to store C RLP & key, but it will increase the degree
(unless we pack this info together with short/long nibbles & c1/c16).
*/

#[derive(Clone, Debug)]
pub(crate) struct BranchKeyConfig<F> {
    _marker: PhantomData<F>,
}

impl<F: FieldExt> BranchKeyConfig<F> {
    pub fn configure(
        meta: &mut VirtualCells<'_, F>,
        cb: &mut MPTConstraintBuilder<F>,
        ctx: MPTContext<F>,
    ) -> Self {
        let position_cols = ctx.position_cols;
        let s_main = ctx.s_main;
        let key = ctx.accumulators.key;
        let mult_diff = ctx.accumulators.mult_diff;
        let r = ctx.r.clone();

        let rot_branch_init = -BRANCH_ROWS_NUM + 1;
        let rot_first_child = rot_branch_init + 1;
        let rot_first_child_prev = rot_first_child - BRANCH_ROWS_NUM;
        let rot_branch_init_prev = rot_branch_init - BRANCH_ROWS_NUM;
        circuit!([meta, cb.base], {
            let not_first_level = a!(position_cols.not_first_level);
            let branch = BranchNodeInfo::new(meta, ctx.clone(), true, rot_branch_init);
            let branch_prev = BranchNodeInfo::new(meta, ctx.clone(), true, rot_branch_init_prev);
            let modified_node_index = a!(ctx.branch.modified_node_index, rot_first_child);
            let key_rlc =
                DataTransition::new_with_rot(meta, key.rlc, rot_first_child_prev, rot_first_child);
            let key_mult =
                DataTransition::new_with_rot(meta, key.mult, rot_first_child_prev, rot_first_child);

            ifx! {f!(position_cols.q_not_first_ext_c), a!(ctx.branch.is_extension_node_c) => {
                let selectors = [branch.is_key_odd(), branch.is_key_even()];
                // Selectors need to be boolean.
                for selector in selectors.iter() {
                    require!(selector => bool);
                }
                // One selector needs to be enabled.
                require!(sum::expr(&selectors) => 1);

                // Get the previous values from the previous branch. In the first level use initial values.
                let after_first_level = not_first_level.expr() * not!(branch.is_below_account(meta));
                let (key_rlc_prev, key_mult_prev) = ifx!{after_first_level => {
                    (key_rlc.prev(), key_mult.prev())
                } elsex {
                    (0.expr(), 1.expr())
                }};

                // Get the length of the key
                // If the resulting key is odd then subtract 1 so we still use the previous multiplier.
                // TODO(Brecht): is_long_even_c1 needs -1 while it should be even?
                let key_num_bytes_for_mult = ifx!{branch.is_extension() => {
                    let key_len = branch.ext_key_len(meta, -1);
                    matchx! {
                        branch.is_ext_even() - branch.is_long_even_c1.expr() => key_len.expr(),
                        branch.is_ext_odd() + branch.is_long_even_c1.expr() => key_len.expr() - 1.expr(),
                    }
                }};
                // Get the multiplier for this key length
                let mult_diff = a!(mult_diff, rot_first_child);
                require!((FixedTableTag::RMult, key_num_bytes_for_mult, mult_diff) => @"mult");

                // Calculate the extension node key RLC when in an extension node
                let key_rlc_post_ext = key_rlc_prev.expr() + ifx!{branch.is_extension() => {
                    let key_rlc_ext = DataTransition::new(meta, key.rlc);
                    // Currently, the extension node S and extension node C both have the same key RLC -
                    // however, sometimes extension node can be replaced by a shorter extension node
                    // (in terms of nibbles), this is still to be implemented.
                    // TODO: extension nodes of different nibbles length
                    require!(key_rlc_ext => key_rlc_ext.prev());

                    // Extension key rlc
                    // TODO(Brecht): refactor
                    let ext_key_rlc = matchx! {
                        branch.is_long_odd_c1.expr() + branch.is_long_even_c1.expr() => {
                            // We check the extension node intermediate RLC for the case when we have
                            // long odd nibbles (meaning there is an odd number of nibbles and this number
                            // is bigger than 1) and sel2 (branch `modified_node` needs
                            // to be multiplied by 1). Note that for the computation of
                            // the intermediate RLC we need `first_nibbles` and
                            // `second_nibbles`.
                            rlc::expr(
                                // Note that there can be at max 31 key bytes because 32 same bytes would mean
                                // the two keys being the same - update operation, not splitting into extension node.
                                // So, we do not need to look further than `s_main.bytes` even if `s_main.bytes[0]`
                                // is not used (when even number of nibbles).
                                &s_main.bytes.iter().skip(1).zip(s_main.bytes.iter()).map(|(byte, second_nibble)| {
                                    let byte = a!(byte, -1);
                                    let second_nibble = a!(second_nibble);
                                    let first_nibble = (byte.expr() - second_nibble.expr()) * invert!(16);
                                    // In this constraint we check whether the list of `second_nibbles` is correct.
                                    // For example having `first_nibble = 9 = ((9*16 + 5) - 5) / 16` we check:
                                    // `s_main.bytes[1] = first_nibble * 16 + 5`.
                                    // Note that first_nibble and second_nibble need to be between 0 and 15 - this
                                    // is checked in a lookup below.
                                    require!(byte => first_nibble.expr() * 16.expr() + second_nibble.expr());
                                    // Collect bytes for rlc calculation
                                    key_mult_prev.expr() * (first_nibble.expr() + second_nibble.expr() * 16.expr() * r[0].expr())
                                }).collect::<Vec<_>>(),
                                &r,
                            ) + ifx!{branch.is_long_odd_c1 => {
                                    16.expr() * (a!(s_main.bytes[0], -1) - 16.expr()) * key_mult_prev.expr()
                            }}
                        },
                        branch.is_long_odd_c16 => {
                            rlc::expr(
                                &s_main.bytes.iter().enumerate().map(|(idx, &byte)| key_mult_prev.expr() * (a!(byte, -1) - if idx == 0 { 16.expr() } else {0.expr()})).collect::<Vec<_>>(),
                                &r,
                            )
                        },
                        branch.is_long_even_c16 => {
                            rlc::expr(
                                &s_main.bytes.iter().skip(1).map(|byte| key_mult_prev.expr() * a!(byte, -1)).collect::<Vec<_>>(),
                                &r,
                            )
                        },
                        branch.is_short() => {
                            (a!(s_main.rlp2, -1) - 16.expr()) * key_mult_prev.expr() * ifx!{branch.is_short_c1 => { 16.expr() } elsex { 1.expr() }}
                        },
                    };
                    // This value is stored is currently stored in `key_rlc_ext`
                    // TODO(Brecht): don't store it?
                    require!(key_rlc_ext => key_rlc_prev.expr() + ext_key_rlc.expr());
                    ext_key_rlc.expr()
                }};

                // Now update the key RLC and multiplier for the branch nibble.
                let mult = key_mult_prev.expr() * mult_diff.expr();
                let (rlc_mult, mult_mult) = ifx!{branch.is_key_odd() => {
                    // The least significant nibble still needs to be added using the same multiplier
                    (16.expr(), 1.expr())
                } elsex {
                    // The least significant nibble is added, update the multiplier for the next nibble
                    (1.expr(), r[0].expr())
                }};
                require!(key_rlc => key_rlc_post_ext.expr() + modified_node_index.expr() * mult.expr() * rlc_mult.expr());
                require!(key_mult => mult.expr() * mult_mult.expr());

                // Update `is_key_odd`.
                ifx!{after_first_level => {
                    ifx!{branch.is_extension() => {
                        // We need to take account the nibbles of the extension node.
                        // `is_key_odd` alternates when there's an even number of nibbles, remains the same otherwise
                        ifx!{branch.is_even() => {
                            require!(branch.is_key_odd() => not!(branch_prev.is_key_odd()));
                        } elsex {
                            require!(branch.is_key_odd() => branch_prev.is_key_odd());
                        }}
                    } elsex {
                        // `is_key_odd` simply alernates for regular branches.
                        require!(branch.is_key_odd() => not!(branch_prev.is_key_odd()));
                    }}
                } elsex {
                    // In the first level we just have to ensure the initial values are set
                    ifx!{branch.is_extension() => {
                        require!(branch.is_key_odd() => branch.is_even());
                    } elsex {
                        require!(branch.is_key_odd() => true);
                    }}
                }}

                // We need to check that `second_nibbles` are between 0 and 15.
                cb.set_range_s(FixedTableTag::RangeKeyLen16.expr());
            }}

            ifx! {f!(position_cols.q_not_first_ext_s), a!(ctx.branch.is_extension_node_s), branch.is_extension() => {
                // RLC bytes zero check
                cb.set_length(branch.ext_num_rlp_bytes(meta) + branch.ext_key_num_bytes(meta) - 2.expr());
            }}
        });

        BranchKeyConfig {
            _marker: PhantomData,
        }
    }
}
