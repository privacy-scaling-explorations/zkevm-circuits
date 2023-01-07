use gadgets::util::{and, not, Expr};
use halo2_proofs::{
    arithmetic::FieldExt,
    plonk::{Expression, VirtualCells},
    poly::Rotation,
};
use std::marker::PhantomData;

use crate::{
    constraints,
    evm_circuit::util::rlc,
    mpt_circuit::helpers::BaseConstraintBuilder,
    mpt_circuit::FixedTableTag,
    mpt_circuit::{helpers::BranchNodeInfo, param::BRANCH_ROWS_NUM},
    mpt_circuit::{helpers::ColumnTransition, MPTContext},
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

The constraints in `extension_node_key.rs` check the intermediate
key RLC (address RLC) in the extension node is properly computed. Here, we need to take into
account the extension node nibbles and the branch `modified_node`.

Other constraints for extension nodes, like checking that the branch hash
is in the extension node (the bytes `[30 252 ... 174]` in extension node rows present the hash
of the underlying branch) or checking the hash of the extension is in the parent node are
checking in `extension_node.rs`.
*/

#[derive(Clone, Debug)]
pub(crate) struct ExtensionNodeKeyConfig<F> {
    _marker: PhantomData<F>,
}

/*
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

impl<F: FieldExt> ExtensionNodeKeyConfig<F> {
    pub fn configure(
        meta: &mut VirtualCells<'_, F>,
        cb: &mut BaseConstraintBuilder<F>,
        ctx: MPTContext<F>,
    ) -> Self {
        let position_cols = ctx.position_cols;
        let branch = ctx.branch;
        let s_main = ctx.s_main;
        let accs = ctx.accumulators;
        let r = ctx.r;

        constraints!([meta, cb], {
            let c16inv = Expression::Constant(F::from(16).invert().unwrap());

            let rot_into_branch_init = -BRANCH_ROWS_NUM + 1;
            let rot_to_first_child = rot_into_branch_init + 1;
            let rot_to_previous_first_child = rot_to_first_child - BRANCH_ROWS_NUM;

            let not_first_level = a!(position_cols.not_first_level);

            let is_extension_s_row = a!(branch.is_extension_node_s);
            let is_extension_c_row = a!(branch.is_extension_node_c);
            let ext = BranchNodeInfo::new(meta, s_main.clone(), true, rot_into_branch_init);

            let modified_node_index = a!(branch.modified_node_index, rot_to_first_child);
            let key_rlc_branch = a!(accs.key.rlc, rot_to_first_child);
            let key_rlc_mult_branch = a!(accs.key.mult, rot_to_first_child);
            let key_rlc_ext = ColumnTransition::new(meta, accs.key.rlc);
            // We are in extension row C, rot_into_branch_init - 1 brings us to the account
            // leaf storage codehash in the first storage proof level.
            let is_first_storage_level = a!(
                ctx.account_leaf.is_in_added_branch,
                rot_into_branch_init - 1
            );

            ifx! {f!(position_cols.q_not_first_ext_c) => {
                // If there are for example two nibbles in the
                // extension node `n1` and `n2` and if we assume that there have been
                // even nibbles in the levels above, then: key_rlc = key_rlc_prev + n1 *
                // key_rlc_mult_prev * 16 + n2 * key_rlc_mult_prev * 1 +
                //     modified_node * key_rlc_mult_prev * r * 16

                ifx!{is_extension_c_row => {
                    ifx!{ext.is_extension() => {
                        // Currently, the extension node S and extension node C both have the same key RLC -
                        // however, sometimes extension node can be replaced by a shorter extension node
                        // (in terms of nibbles), this is still to be implemented.
                        // TODO: extension nodes of different nibbles length
                        require!(key_rlc_ext => key_rlc_ext.prev());
                    }}

                    // rlc_prev is the RLC from the previous level. For example, if the extension node
                    // is an a branch, then rlc_prev is the intermediate key RLC computed in this branch.
                    // rlc_prev = 0 if first level
                    // rlc_prev = key_rlc_prev_level if not first level
                    let after_first_level = not_first_level.expr() * not::expr(is_first_storage_level.expr());
                    let rlc_prev = selectx!{after_first_level => {
                        a!(accs.key.rlc, rot_to_previous_first_child)
                    }};
                    // The multiplier to be used for the first nibble.
                    let mult_prev = selectx!{after_first_level => {
                        a!(accs.key.mult, rot_to_previous_first_child)
                    } elsex {
                        1
                    }};

                    // It needs to be checked that `mult_diff` value corresponds to the number
                    // of the extension node nibbles. The information about the number of nibbles
                    // is encoded in `s_main.rlp2` - except in `short` case, but in this case we
                    // only have one nibble and we already know what value should have
                    // `mult_diff`. Thus, we check whether `(RMult, s_main.rlp2,
                    // mult_diff)` is in `fixed_table`. key_len = s_rlp2 - 128 - 1   if
                    // long even key_len = s_rlp2 - 128 - 1   if is_ext_long_odd_c1
                    // key_len = s_rlp2 - 128       if is_ext_long_odd_c16
                    // key_len = 1                  if short
                    let mult_diff = a!(accs.mult_diff, rot_to_first_child);
                    ifx! {ext.is_extension() => {
                        let key_len = selectx!{ext.is_long() => {
                            (a!(s_main.rlp2, -1) - 128.expr()) - ext.is_long_even() - ext.is_long_odd_c1.expr()
                        } elsex {
                            selectx!{ext.is_short_c1 => {
                                0.expr()
                            } elsex {
                                1.expr()
                            }}
                        }};
                        require!((FixedTableTag::RMult, key_len, mult_diff) => @"mult");
                    }}

                    // Extension key rlc
                    let mut ext_key_rlc = selectx!{ext.is_long_odd_c1.expr() + ext.is_long_even_c1.expr() => {
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
                                let first_nibble = (byte.expr() - second_nibble.expr()) * c16inv.expr();
                                // In this constraint we check whether the list of `second_nibbles` is correct.
                                // For example having `first_nibble = 9 = ((9*16 + 5) - 5) / 16` we check:
                                // `s_main.bytes[1] = first_nibble * 16 + 5`.
                                // Note that first_nibble and second_nibble need to be between 0 and 15 - this
                                // is checked in a lookup below.
                                require!(byte => first_nibble.expr() * 16.expr() + second_nibble.expr());
                                // Collect bytes for rlc calculation
                                mult_prev.expr() * (first_nibble.expr() + second_nibble.expr() * 16.expr() * r[0].expr())
                            }).collect::<Vec<_>>(),
                            &r,
                        ) + selectx!{ext.is_long_odd_c1 => {
                             16.expr() * (a!(s_main.bytes[0], -1) - 16.expr()) * mult_prev.expr()
                        }}
                    }};
                    ext_key_rlc = ext_key_rlc + selectx!{ext.is_long_odd_c16 => {
                        rlc::expr(
                            &s_main.bytes.iter().enumerate().map(|(idx, &byte)| mult_prev.expr() * (a!(byte, -1) - if idx == 0 { 16.expr() } else {0.expr()})).collect::<Vec<_>>(),
                            &r,
                        )
                    }};
                    ext_key_rlc = ext_key_rlc + selectx!{ext.is_long_even_c16 => {
                        rlc::expr(
                            &s_main.bytes.iter().skip(1).map(|byte| mult_prev.expr() * a!(byte, -1)).collect::<Vec<_>>(),
                            &r,
                        )
                    }};
                    ext_key_rlc = ext_key_rlc + selectx!{ext.is_short() => {
                        (1.expr() + 15.expr() * ext.is_short_c1.expr()) * (a!(s_main.rlp2, -1) - 16.expr()) * mult_prev.expr()
                    }};

                    // Take into account the branch nibble
                    // TODO(Brecht): just merge this with branch_key.rs
                    let key_mult = mult_prev.expr() * mult_diff.expr();
                    ifx! {ext.is_extension() => {
                        require!(key_rlc_ext => rlc_prev.expr() + ext_key_rlc.expr());
                        ifx!{ext.is_c16() => {
                            require!(key_rlc_branch => key_rlc_ext.expr() + modified_node_index.expr() * key_mult.expr() * 16.expr());
                            require!(key_rlc_mult_branch => key_mult.expr());
                        }}
                        ifx!{ext.is_c1() => {
                            require!(key_rlc_branch => key_rlc_ext.expr() + modified_node_index.expr() * key_mult.expr());
                            require!(key_rlc_mult_branch => key_mult.expr() * r[0].expr());
                        }}
                    }}

                    // It needs to be checked that `second_nibbles` are between 0 and 15.
                    cb.set_range_s(FixedTableTag::RangeKeyLen16.expr());
                }}
            }}

            // RLC bytes zero check
            ifx! {f!(position_cols.q_not_first_ext_s), is_extension_s_row => {
                ifx!{ext.is_short() => {
                    // We need to ensure `s_main.bytes` are all 0 when short - the only nibble is in `s_main.rlp2`.
                    cb.set_range_length_s(0.expr());
                }}
                ifx!{ext.is_long() => {
                    // `s_main.bytes[i] = 0` after last extension node nibble, [s_main.rlp_bytes(), c_main.rlp_bytes()].concat()[3..35]
                    cb.set_range_length(1.expr() + (a!(s_main.bytes[0]) - 128.expr()));
                }}
            }}
        });

        ExtensionNodeKeyConfig {
            _marker: PhantomData,
        }
    }
}
