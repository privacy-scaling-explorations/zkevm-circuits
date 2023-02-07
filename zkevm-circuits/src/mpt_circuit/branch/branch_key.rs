use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::Region,
    plonk::{Error, VirtualCells},
    poly::Rotation,
};

use crate::{
    circuit,
    circuit_tools::{CellManager, DataTransition},
    mpt_circuit::{helpers::BranchNodeInfo, param::BRANCH_ROWS_NUM},
    mpt_circuit::{
        helpers::KeyData, witness_row::MptWitnessRow, MPTConfig, MPTContext, ProofValues,
    },
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
    key_data: KeyData<F>,
}

impl<F: FieldExt> BranchKeyConfig<F> {
    pub(crate) fn configure(
        meta: &mut VirtualCells<'_, F>,
        cb: &mut MPTConstraintBuilder<F>,
        ctx: MPTContext<F>,
    ) -> Self {
        let position_cols = ctx.position_cols;
        let key = ctx.accumulators.key;
        let mult_diff = ctx.accumulators.mult_diff;
        let r = ctx.r.clone();

        let mut cm = CellManager::new(meta, 1, &ctx.managed_columns, 0);
        let ctx_key_data: Option<KeyData<F>>;

        circuit!([meta, cb.base], {
            ifx! {f!(position_cols.q_not_first_ext_c), a!(ctx.branch.is_extension_node_c) => {
                let rot_branch_init = -BRANCH_ROWS_NUM + 1;
                let rot_first_child = rot_branch_init + 1;

                let branch = BranchNodeInfo::new(meta, ctx.clone(), false, rot_branch_init);
                let modified_index = a!(ctx.branch.modified_index, rot_first_child);
                let key_rlc = a!(key.rlc, rot_first_child);
                let key_mult = a!(key.mult, rot_first_child);

                // `is_key_odd` needs to be boolean
                require!(branch.is_key_odd() => bool);

                // Load the last key values
                let key_data = KeyData::load(&mut cb.base, &mut cm, &ctx.memory["key"], 0.expr());

                // Calculate the extension node key RLC when in an extension node
                let key_rlc_post_ext = ifx!{branch.is_extension() => {
                    let key_rlc_ext = DataTransition::new(meta, key.rlc);
                    // Extension key rlc
                    let ext_key_rlc = key_data.rlc.expr() + branch.ext_key_rlc(meta, &mut cb.base, key_data.mult.expr());
                    // Currently, the extension node S and extension node C both have the same key RLC -
                    // however, sometimes extension node can be replaced by a shorter extension node
                    // (in terms of nibbles), this is still to be implemented.
                    // TODO: extension nodes of different nibbles length
                    require!(key_rlc_ext => key_rlc_ext.prev());
                    // Store it
                    require!(key_rlc_ext => ext_key_rlc);
                    ext_key_rlc.expr()
                } elsex {
                    key_data.rlc.expr()
                }};

                // Get the length of the key
                let key_num_bytes_for_mult = ifx!{branch.is_extension() => {
                    // Unless both parts of the key are odd, subtract 1 from the key length.
                    let key_len = branch.ext_key_len(meta, -1);
                    key_len - ifx! {not!(key_data.is_odd.expr() * branch.is_key_part_in_ext_odd()) => { 1.expr() }}
                }};
                // Get the multiplier for this key length
                let mult_diff = a!(mult_diff, rot_first_child);
                require!((FixedTableTag::RMult, key_num_bytes_for_mult, mult_diff) => @"mult");

                // Now update the key RLC and multiplier for the branch nibble.
                let mult = key_data.mult.expr() * mult_diff.expr();
                let (nibble_mult, mult_mult) = ifx!{branch.is_key_odd() => {
                    // The nibble will be added as the most significant nibble using the same multiplier
                    (16.expr(), 1.expr())
                } elsex {
                    // The nibble will be added as the least significant nibble, the multiplier needs to advance
                    (1.expr(), r[0].expr())
                }};
                require!(key_rlc => key_rlc_post_ext.expr() + modified_index.expr() * nibble_mult.expr() * mult.expr());
                require!(key_mult => mult.expr() * mult_mult.expr());

                // Update key parity
                ifx!{branch.is_extension() => {
                    // We need to take account the nibbles of the extension node.
                    // The parity alternates when there's an even number of nibbles, remains the same otherwise
                    ifx!{branch.is_key_part_in_ext_even() => {
                        require!(branch.is_key_odd() => not!(key_data.is_odd));
                    } elsex {
                        require!(branch.is_key_odd() => key_data.is_odd);
                    }}
                } elsex {
                    // The parity simply alternates for regular branches.
                    require!(branch.is_key_odd() => not!(key_data.is_odd));
                }}

                KeyData::store(&mut cb.base, &ctx.memory["key"], [
                    key_rlc.expr(),
                    key_mult.expr(),
                    branch.nibbles_counter().expr(),
                    branch.is_key_odd(),
                    branch.contains_placeholder_leaf(meta, true),
                    branch.contains_placeholder_leaf(meta, false),
                ]);

                // We need to check that the nibbles we stored in s are between 0 and 15.
                cb.set_range_s(FixedTableTag::RangeKeyLen16.expr());

                ctx_key_data = Some(key_data);
            }}

            ifx! {f!(position_cols.q_not_first_ext_s), a!(ctx.branch.is_extension_node_s) => {
                let rot_branch_init = -BRANCH_ROWS_NUM + 2;
                let branch = BranchNodeInfo::new(meta, ctx.clone(), true, rot_branch_init);
                ifx! {branch.is_extension() => {
                    // RLC bytes zero check
                    // TODO(Brecht): fix
                    //cb.set_length(1.expr() + branch.ext_num_bytes_on_key_row(meta, 0));
                }}
            }}
        });

        BranchKeyConfig {
            key_data: ctx_key_data.unwrap(),
        }
    }

    pub(crate) fn assign(
        &self,
        region: &mut Region<'_, F>,
        _witness: &[MptWitnessRow<F>],
        _mpt_config: &MPTConfig<F>,
        pv: &mut ProofValues<F>,
        offset: usize,
    ) -> Result<(), Error> {
        self.key_data
            .witness_load(region, offset, &pv.memory["key"], 0)?;
        self.key_data.witness_store(
            region,
            offset,
            &mut pv.memory["key"],
            pv.key_rlc,
            pv.key_rlc_mult,
            pv.nibbles_num,
            pv.is_placeholder_leaf_s,
            pv.is_placeholder_leaf_c,
        )?;
        Ok(())
    }
}
