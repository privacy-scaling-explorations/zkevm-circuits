use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, VirtualCells},
    poly::Rotation,
};
use itertools::Itertools;
use std::marker::PhantomData;

use crate::{
    mpt_circuit::columns::{AccumulatorCols, MainCols, PositionCols},
    mpt_circuit::helpers::{
        bytes_expr_into_rlc, compute_rlc, get_bool_constraint, get_is_extension_node,
        get_is_extension_node_even_nibbles, get_is_extension_node_long_odd_nibbles,
        get_is_extension_node_one_nibble, get_branch_len, key_len_lookup, get_is_inserted_extension_node
    },
    mpt_circuit::witness_row::MptWitnessRow,
    mpt_circuit::{
        param::{
            ACCOUNT_LEAF_ROWS, ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND,
            ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND, BRANCH_ROWS_NUM, C_RLP_START, C_START, HASH_WIDTH,
            IS_BRANCH_C16_POS, IS_BRANCH_C1_POS, IS_BRANCH_C_PLACEHOLDER_POS,
            IS_BRANCH_S_PLACEHOLDER_POS, IS_C_EXT_NODE_NON_HASHED_POS,
            IS_EXT_LONG_EVEN_C16_POS, IS_EXT_LONG_EVEN_C1_POS, IS_EXT_LONG_ODD_C16_POS,
            IS_EXT_LONG_ODD_C1_POS, IS_EXT_SHORT_C16_POS, IS_EXT_SHORT_C1_POS,
            IS_S_EXT_LONGER_THAN_55_POS, IS_S_EXT_NODE_NON_HASHED_POS, NIBBLES_COUNTER_POS,
            RLP_NUM,
        },
    },
    mpt_circuit::{MPTConfig, ProofValues},
    table::KeccakTable,
};

use super::BranchCols;
use super::extension::{extension_node_rlp, extension_node_rlc, extension_node_selectors, check_intermediate_mult};

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

The constraints in `extension_node.rs` check:
 - RLP of the node
 - that the branch hash is in the extension node (the bytes `[30 252 ... 174]` in extension node rows present the hash
of the underlying branch)
 - that the hash of the extension is in the parent node.
*/

#[derive(Clone, Debug)]
pub(crate) struct ExtensionNodeConfig<F> {
    _marker: PhantomData<F>,
}

/*
Let's say we have branch1 and branch2 below it.

branch1 S row 0 || branch1 C row 0
...
branch1 S row 15 || branch1 C row 15

branch2 S row 0 || branch2 C row 0
...
branch2 S row 15 || branch2 C row 15

Hash of branch2 S is in one of the branch1 rows (in S columns).
Hash of branch2 C is in one of the branch1 rows (in C columns).

In what follows, we write branch without S and C - it is the same for both cases.

Key key1 determines the position of branch2 hash in branch1 (0-15).
To check this, branch2 RLC (over all RLP bytes - all 1+16 rows, 1 is for branch init row)
is checked to have a hash in branch1, at modified_node index
(modified_node depends on key key1).

However, with extension node it's a bit different.

branch1 S row 0 || branch1 C row 0
...
branch1 S row 15 || branch1 C row 15
extension1 S
extension1 C

branch2 S row 0 || branch2 C row 0
...
branch2 S row 15 || branch2 C row 15
extension2 S
extension2 C

There are additional rows immediately after branch 16 rows - one row for
extension node S and one row for extension node C. These rows are empty when
we have a regular branch.

Let's say branch2 is extension node. In this case, extension2 row contains:
  - key bytes that present the extension
  - hash of branch2

---
Example 1:

Key extension of length 2:
[228, 130, 0,          149,        160, 114,                    253,                     150,133,18,192,156,19,241,162,51,210,24,1,151,16,48,7,177,42,60,49,34,230,254,242,79,132,165,90,75,249]
[rlp, rlp, key byte 1, key byte 2, rlp, hash of branch2 byte 0, hash of branch2 byte 1, ...]
[0, 149] presents key extension:
  - 0 because it's even length (in branch it would be 16, see terminator)
  - 149 = 9*16 + 5
Key extension is [9, 5].

Two constraints are needed:
  - the hash of extension node (extension node RLC is needed) needs to be
    checked whether it's in branch1
  - the hash of branch2 is in extension node.

Also, it needs to be checked that key extension corresponds to key1 (not in this chip).

---
Example 2:

Key extension of length 1:
[226, 16,        160,172,105,12...
[rlp, key byte1, ...
[16] presents key extension:
  - 16 = 0 + 16
Key extension is [0].

*/

impl<F: FieldExt> ExtensionNodeConfig<F> {
    #[allow(clippy::too_many_arguments)]
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: impl Fn(&mut VirtualCells<'_, F>) -> Expression<F> + Clone,
        inter_root: Column<Advice>,
        position_cols: PositionCols<F>,
        is_account_leaf_in_added_branch: Column<Advice>,
        branch: BranchCols<F>,
        s_main: MainCols<F>,
        c_main: MainCols<F>,
        accs: AccumulatorCols<F>,
        keccak_table: KeccakTable,
        power_of_randomness: [Expression<F>; HASH_WIDTH],
        fixed_table: [Column<Fixed>; 3],
        is_s: bool,
        check_zeros: bool,
    ) -> Self {
        let config = ExtensionNodeConfig {
            _marker: PhantomData,
        };
        let one = Expression::Constant(F::from(1_u64));
        let c128 = Expression::Constant(F::from(128));
        let c160_inv = Expression::Constant(F::from(160_u64).invert().unwrap());
        let c192 = Expression::Constant(F::from(192));
        let mut rot_into_branch_init = -17;
        if !is_s {
            rot_into_branch_init = -18;
        }

        if is_s {
            extension_node_rlp(
                meta,
                q_enable.clone(),
                position_cols.clone(),
                s_main.clone(),
                c_main.clone(),
                rot_into_branch_init,
            );
        }

        extension_node_rlc(
            meta,
            q_enable.clone(),
            position_cols.clone(),
            s_main.clone(),
            c_main.clone(),
            accs.clone(),
            power_of_randomness.clone(),
            is_s,
        );

        extension_node_selectors(
            meta,
            q_enable.clone(),
            position_cols.clone(),
            s_main.clone(),
            c_main.clone(),
            is_account_leaf_in_added_branch.clone(),
            rot_into_branch_init,
            false,
            is_s,
            false,
        );

        // Note: acc_mult is checked in `extension_node_key.rs`.

        /*
        Check whether branch hash is in the extension node row - we check that the branch hash RLC
        (computed over the first 17 rows) corresponds to the extension node hash stored in
        the extension node row. That means `(branch_RLC, extension_node_hash_RLC`) needs to
        be in a keccak table.
        */
        meta.lookup_any("Extension node branch hash in extension row", |meta| {
            let q_enable = q_enable(meta);
            let q_not_first = meta.query_fixed(position_cols.q_not_first, Rotation::cur());

            let c_rlp2 = meta.query_advice(c_main.rlp2, Rotation::cur());
            let is_branch_hashed = c_rlp2 * c160_inv.clone();

            let mut acc = meta.query_advice(accs.acc_s.rlc, Rotation(-1));
            let mut mult = meta.query_advice(accs.acc_s.mult, Rotation(-1));
            if !is_s {
                acc = meta.query_advice(accs.acc_c.rlc, Rotation(-2));
                mult = meta.query_advice(accs.acc_c.mult, Rotation(-2));
            }
            // TODO: acc currently doesn't have branch ValueNode info (which 128 if nil)
            let branch_acc = acc + c128.clone() * mult;

            let mut sc_hash = vec![];
            // Note: extension node has branch hash always in c_advices.
            for column in c_main.bytes.iter() {
                sc_hash.push(meta.query_advice(*column, Rotation::cur()));
            }
            let hash_rlc = bytes_expr_into_rlc(&sc_hash, power_of_randomness[0].clone());

            let selector =
                q_not_first * q_enable * is_branch_hashed;

            let mut table_map = Vec::new();
            let keccak_is_enabled = meta.query_advice(keccak_table.is_enabled, Rotation::cur());
            table_map.push((selector.clone(), keccak_is_enabled));

            let keccak_input_rlc = meta.query_advice(keccak_table.input_rlc, Rotation::cur());
            table_map.push((selector.clone() * branch_acc, keccak_input_rlc));

            let branch_len = get_branch_len(meta, s_main.clone(), rot_into_branch_init, is_s);

            let keccak_input_len = meta.query_advice(keccak_table.input_len, Rotation::cur());
            table_map.push((selector.clone() * branch_len, keccak_input_len));

            let keccak_output_rlc = meta.query_advice(keccak_table.output_rlc, Rotation::cur());
            table_map.push((selector * hash_rlc, keccak_output_rlc));

            table_map
        });

        meta.create_gate(
            "Extension node branch hash in extension row (non-hashed branch)",
            |meta| {
                let mut constraints = vec![];
                let q_not_first = meta.query_fixed(position_cols.q_not_first, Rotation::cur());
                let q_enable = q_enable(meta);

                let c_rlp2 = meta.query_advice(c_main.rlp2, Rotation::cur());
                // c_rlp2 = 160 when branch is hashed (longer than 31) and c_rlp2 = 0 otherwise
                let is_branch_hashed = c_rlp2 * c160_inv.clone();

                let mut acc = meta.query_advice(accs.acc_s.rlc, Rotation(-1));
                let mut mult = meta.query_advice(accs.acc_s.mult, Rotation(-1));
                if !is_s {
                    acc = meta.query_advice(accs.acc_c.rlc, Rotation(-2));
                    mult = meta.query_advice(accs.acc_c.mult, Rotation(-2));
                }
                // TODO: acc currently doesn't have branch ValueNode info (which 128 if nil)
                let branch_acc = acc + c128.clone() * mult;

                let mut branch_in_ext = vec![];
                // Note: extension node has branch hash always in c_advices.
                for column in c_main.bytes.iter() {
                    branch_in_ext.push(meta.query_advice(*column, Rotation::cur()));
                }
                let rlc = bytes_expr_into_rlc(&branch_in_ext, power_of_randomness[0].clone());

                /*
                Check whether branch is in extension node row (non-hashed branch) -
                we check that the branch RLC is the same as the extension node branch part RLC
                (RLC computed over `c_main.bytes`).

                Note: there need to be 0s after branch ends in the extension node `c_main.bytes`
                (see below).
                */
                constraints.push((
                    "Non-hashed branch in extension node",
                    q_not_first * q_enable * (one.clone() - is_branch_hashed) * (branch_acc - rlc),
                ));

                constraints
            },
        );

        let sel_branch_non_hashed = |meta: &mut VirtualCells<F>| {
            let q_not_first = meta.query_fixed(position_cols.q_not_first, Rotation::cur());
            let q_enable = q_enable(meta);

            let c_rlp2 = meta.query_advice(c_main.rlp2, Rotation::cur());
            // c_rlp2 = 160 when branch is hashed (longer than 31) and c_rlp2 = 0 otherwise
            let is_branch_hashed = c_rlp2 * c160_inv.clone();

            q_not_first * q_enable * (one.clone() - is_branch_hashed)
        };

        /*
        There are 0s after non-hashed branch ends in `c_main.bytes`.
        */
        if check_zeros {
            for ind in 1..HASH_WIDTH {
                key_len_lookup(
                    meta,
                    sel_branch_non_hashed,
                    ind,
                    c_main.bytes[0],
                    c_main.bytes[ind],
                    192,
                    fixed_table,
                )
            }
        }

        /*
        Note: Correspondence between nibbles in C and bytes in S is checked in
        extension_node_key.
        */

        /*
        When we have an extension node in the first level of the account trie,
        its hash needs to be compared to the root of the trie.

        Note: the branch counterpart is implemented in `branch_hash_in_parent.rs`.
        */
        meta.lookup_any(
            "Account first level extension node hash - compared to root",
            |meta| {
                let q_enable = q_enable(meta);

                let q_not_first = meta.query_fixed(position_cols.q_not_first, Rotation::cur());
                let not_first_level =
                    meta.query_advice(position_cols.not_first_level, Rotation::cur());

                let acc_c = meta.query_advice(accs.acc_c.rlc, Rotation::cur());
                let root = meta.query_advice(inter_root, Rotation::cur());

                let selector = q_not_first * q_enable * (one.clone() - not_first_level);

                let mut table_map = Vec::new();
                let keccak_is_enabled = meta.query_advice(keccak_table.is_enabled, Rotation::cur());
                table_map.push((selector.clone(), keccak_is_enabled));

                let keccak_input_rlc = meta.query_advice(keccak_table.input_rlc, Rotation::cur());
                table_map.push((selector.clone() * acc_c, keccak_input_rlc));

                let mut rot = 0;
                if !is_s {
                    rot = -1;
                }
                let ext_len =
                    meta.query_advice(s_main.rlp1, Rotation(rot)) - c192.clone() + one.clone();

                let keccak_input_len = meta.query_advice(keccak_table.input_len, Rotation::cur());
                table_map.push((selector.clone() * ext_len, keccak_input_len));

                let keccak_output_rlc = meta.query_advice(keccak_table.output_rlc, Rotation::cur());
                table_map.push((selector * root, keccak_output_rlc));

                table_map
            },
        );

        /*
        When extension node is in the first level of the storage trie, we need to check whether
        `hash(ext_node) = storage_trie_root`. We do this by checking whether
        `(ext_node_RLC, storage_trie_root_RLC)` is in the keccak table.

        Note: extension node in the first level cannot be shorter than 32 bytes (it is always hashed).
        */
        meta.lookup_any(
            "Extension node in first level of storage trie - hash compared to the storage root",
            |meta| {
                let q_enable = q_enable(meta);
                let not_first_level = meta.query_advice(position_cols.not_first_level, Rotation::cur());

                let mut is_branch_placeholder = meta.query_advice(
                    s_main.bytes[IS_BRANCH_S_PLACEHOLDER_POS - RLP_NUM],
                    Rotation(rot_into_branch_init),
                );
                let is_inserted_ext_node = get_is_inserted_extension_node(
                    meta, c_main.rlp1, c_main.rlp2, rot_into_branch_init, is_s);

                if !is_s {
                    is_branch_placeholder = meta.query_advice(
                        s_main.bytes[IS_BRANCH_C_PLACEHOLDER_POS - RLP_NUM],
                        Rotation(rot_into_branch_init),
                    );
                }

                // Check if there is an account leaf above the extension node (corresponds to the check
                // whether the extension node is in the first level for the case when extension node
                // in the account proof).
                let is_account_leaf_in_added_branch = meta.query_advice(
                    is_account_leaf_in_added_branch,
                    Rotation(rot_into_branch_init - 1),
                );

                let is_extension_node =
                    get_is_extension_node(meta, s_main.bytes, rot_into_branch_init);

                // Note: acc_c in both cases.
                let acc = meta.query_advice(accs.acc_c.rlc, Rotation::cur());

                let mut sc_hash = vec![];
                // Note: storage root is always in `s_main.bytes`.
                for column in s_main.bytes.iter() {
                    if is_s {
                        sc_hash.push(meta.query_advice(
                            *column,
                            Rotation(
                                rot_into_branch_init
                                    - (ACCOUNT_LEAF_ROWS - ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND),
                            ),
                        ));
                    } else {
                        sc_hash.push(meta.query_advice(
                            *column,
                            Rotation(
                                rot_into_branch_init
                                    - (ACCOUNT_LEAF_ROWS - ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND),
                            ),
                        ));
                    }
                }
                let hash_rlc = bytes_expr_into_rlc(&sc_hash, power_of_randomness[0].clone());

                let selector = q_enable
                    * not_first_level
                    * is_extension_node
                    * is_account_leaf_in_added_branch
                    * (one.clone() - is_inserted_ext_node)
                    * (one.clone() - is_branch_placeholder);

                let mut table_map = Vec::new();
                let keccak_is_enabled = meta.query_advice(keccak_table.is_enabled, Rotation::cur());
                table_map.push((selector.clone(), keccak_is_enabled));

                let keccak_input_rlc = meta.query_advice(keccak_table.input_rlc, Rotation::cur());
                table_map.push((selector.clone() * acc, keccak_input_rlc));

                let mut rot = 0;
                if !is_s {
                    rot = -1;
                }
                let ext_len =
                    meta.query_advice(s_main.rlp1, Rotation(rot)) - c192.clone() + one.clone();

                let keccak_input_len = meta.query_advice(keccak_table.input_len, Rotation::cur());
                table_map.push((selector.clone() * ext_len, keccak_input_len));

                let keccak_output_rlc = meta.query_advice(keccak_table.output_rlc, Rotation::cur());
                table_map.push((selector * hash_rlc, keccak_output_rlc));

                table_map
            },
        );

        /*
        Check whether the extension node hash is in the parent branch.
        That means we check whether
        `(extension_node_RLC, node_hash_RLC)` is in the keccak table where `node` is a parent
        brach child at `modified_node` position.
        */
        meta.lookup_any("Extension node hash in parent branch", |meta| {
            let q_enable = q_enable(meta);
            let not_first_level = meta.query_advice(position_cols.not_first_level, Rotation::cur());

            let is_account_leaf_in_added_branch = meta.query_advice(
                is_account_leaf_in_added_branch,
                Rotation(rot_into_branch_init - 1),
            );

            let is_inserted_ext_node = get_is_inserted_extension_node(
                meta, c_main.rlp1, c_main.rlp2, rot_into_branch_init, is_s);

            // When placeholder extension, we don't check its hash in a parent.
            let mut is_branch_placeholder = s_main.bytes[IS_BRANCH_S_PLACEHOLDER_POS - RLP_NUM];
            if !is_s {
                is_branch_placeholder = s_main.bytes[IS_BRANCH_C_PLACEHOLDER_POS - RLP_NUM];
            }
            let is_branch_placeholder =
                meta.query_advice(is_branch_placeholder, Rotation(rot_into_branch_init));

            let mut is_ext_node_non_hashed = s_main.bytes[IS_S_EXT_NODE_NON_HASHED_POS - RLP_NUM];
            if !is_s {
                is_ext_node_non_hashed = s_main.bytes[IS_C_EXT_NODE_NON_HASHED_POS - RLP_NUM];
            }
            let is_ext_node_non_hashed =
                meta.query_advice(is_ext_node_non_hashed, Rotation(rot_into_branch_init));

            let acc_c = meta.query_advice(accs.acc_c.rlc, Rotation::cur());

            // Any rotation that lands into branch can be used instead of -21.
            let mut mod_node_hash_rlc_cur = meta.query_advice(accs.s_mod_node_rlc, Rotation(-21));
            if !is_s {
                mod_node_hash_rlc_cur = meta.query_advice(accs.c_mod_node_rlc, Rotation(-21));
            }

            let selector = not_first_level
                * q_enable
                * (one.clone() - is_account_leaf_in_added_branch)
                * (one.clone() - is_branch_placeholder)
                * (one.clone() - is_inserted_ext_node)
                * (one.clone() - is_ext_node_non_hashed);

            let mut table_map = Vec::new();
            let keccak_is_enabled = meta.query_advice(keccak_table.is_enabled, Rotation::cur());
            table_map.push((selector.clone(), keccak_is_enabled));

            let keccak_input_rlc = meta.query_advice(keccak_table.input_rlc, Rotation::cur());
            table_map.push((selector.clone() * acc_c, keccak_input_rlc));

            let mut rot = 0;
            if !is_s {
                rot = -1;
            }
            let ext_len =
                meta.query_advice(s_main.rlp1, Rotation(rot)) - c192.clone() + one.clone();

            let keccak_input_len = meta.query_advice(keccak_table.input_len, Rotation::cur());
            table_map.push((selector.clone() * ext_len, keccak_input_len));

            let keccak_output_rlc = meta.query_advice(keccak_table.output_rlc, Rotation::cur());
            table_map.push((selector * mod_node_hash_rlc_cur, keccak_output_rlc));

            table_map
        });

        meta.create_gate(
            "Extension node in parent branch (non-hashed extension node)",
            |meta| {
                let q_enable = q_enable(meta);
                let q_not_first = meta.query_fixed(position_cols.q_not_first, Rotation::cur());
                let not_first_level =
                    meta.query_advice(position_cols.not_first_level, Rotation::cur());

                let is_inserted_ext_node = get_is_inserted_extension_node(
                    meta, c_main.rlp1, c_main.rlp2, rot_into_branch_init, is_s);

                let is_account_leaf_in_added_branch = meta.query_advice(
                    is_account_leaf_in_added_branch,
                    Rotation(rot_into_branch_init - 1),
                );

                // When placeholder extension, we don't check its hash in a parent.
                let mut is_branch_placeholder = s_main.bytes[IS_BRANCH_S_PLACEHOLDER_POS - RLP_NUM];
                if !is_s {
                    is_branch_placeholder = s_main.bytes[IS_BRANCH_C_PLACEHOLDER_POS - RLP_NUM];
                }
                let is_branch_placeholder =
                    meta.query_advice(is_branch_placeholder, Rotation(rot_into_branch_init));

                let mut is_ext_node_non_hashed =
                    s_main.bytes[IS_S_EXT_NODE_NON_HASHED_POS - RLP_NUM];
                if !is_s {
                    is_ext_node_non_hashed = s_main.bytes[IS_C_EXT_NODE_NON_HASHED_POS - RLP_NUM];
                }
                let is_ext_node_non_hashed =
                    meta.query_advice(is_ext_node_non_hashed, Rotation(rot_into_branch_init));

                let mut constraints = vec![];

                let acc_c = meta.query_advice(accs.acc_c.rlc, Rotation::cur());
                let mut mod_node_hash_rlc_cur =
                    meta.query_advice(accs.s_mod_node_rlc, Rotation(-21));
                if !is_s {
                    mod_node_hash_rlc_cur = meta.query_advice(accs.c_mod_node_rlc, Rotation(-21));
                }

                /*
                When an extension node is not hashed, we do not check whether it is in a parent
                branch using a lookup (see above), instead we need to check whether the branch child
                at `modified_node` position is exactly the same as the extension node.
                */
                constraints.push((
                    "Non-hashed extension node in parent branch",
                    q_not_first
                        * not_first_level
                        * q_enable
                        * (one.clone() - is_account_leaf_in_added_branch)
                        * (one.clone() - is_branch_placeholder)
                        * is_ext_node_non_hashed
                        * (one.clone() - is_inserted_ext_node)
                        * (mod_node_hash_rlc_cur - acc_c),
                ));

                constraints
            },
        );

        /*
        We need to make sure the total number of nibbles is 64. This constraint ensures the number
        of nibbles used (stored in branch init) is correctly computed - nibbles up until this
        extension node + nibbles in this extension node.
        Once in a leaf, the remaining nibbles stored in a leaf need to be added to the count.
        The final count needs to be 64.
        */
        if is_s {
            meta.create_gate("Extension node number of nibbles", |meta| {
                let mut constraints = vec![];
                let q_not_first = meta.query_fixed(position_cols.q_not_first, Rotation::cur());
                let q_enable = q_enable(meta);
                let not_first_level =
                    meta.query_advice(position_cols.not_first_level, Rotation::cur());

                // Only check if there is an account above the branch.
                let is_first_storage_level = meta.query_advice(
                    is_account_leaf_in_added_branch,
                    Rotation(rot_into_branch_init - 1),
                );

                let is_ext_longer_than_55 = meta.query_advice(
                    s_main.bytes[IS_S_EXT_LONGER_THAN_55_POS - RLP_NUM],
                    Rotation(rot_into_branch_init),
                );

                let is_short =
                    get_is_extension_node_one_nibble(meta, s_main.bytes, rot_into_branch_init);
                let is_even_nibbles =
                    get_is_extension_node_even_nibbles(meta, s_main.bytes, rot_into_branch_init);
                let is_long_odd_nibbles = get_is_extension_node_long_odd_nibbles(
                    meta,
                    s_main.bytes,
                    rot_into_branch_init,
                );

                /*
                Note: for regular branches, the constraint that `nibbles_count` increases
                by 1 is in `branch.rs`.
                */

                let nibbles_count_cur = meta.query_advice(
                    s_main.bytes[NIBBLES_COUNTER_POS - RLP_NUM],
                    Rotation(rot_into_branch_init),
                );
                let mut nibbles_count_prev = meta.query_advice(
                    s_main.bytes[NIBBLES_COUNTER_POS - RLP_NUM],
                    Rotation(rot_into_branch_init - BRANCH_ROWS_NUM),
                );

                /*
                nibbles_count_prev needs to be 0 when in first account level or
                in first storage level
                */
                nibbles_count_prev =
                    (one.clone() - is_first_storage_level) * nibbles_count_prev.clone();
                nibbles_count_prev = not_first_level * nibbles_count_prev.clone();

                /*
                When there is only one nibble in the extension node, `nibbles_count` changes
                for 2: one nibble and `modified_node` in a branch.
                */
                constraints.push((
                    "Nibbles number when one nibble",
                    q_not_first.clone()
                        * q_enable.clone()
                        * is_short
                        * (nibbles_count_cur.clone()
                            - nibbles_count_prev.clone()
                            - one.clone()
                            - one.clone()), // -1 for nibble, - 1 is for branch position
                ));

                let s_rlp2 = meta.query_advice(s_main.rlp2, Rotation::cur());
                let mut num_nibbles =
                    (s_rlp2.clone() - c128.clone() - one.clone()) * (one.clone() + one.clone());
                /*
                When there is an even number of nibbles in the extension node,
                we compute the number of nibbles as: `(s_rlp2 - 128 - 1) * 2`.
                By `s_rlp2 - 128` we get the number of bytes where nibbles are compressed, but
                then we need to subtract 1 because `s_main.bytes[0]` does not contain any nibbles
                (it is just 0 when even number of nibbles).

                In the example below it is: `(130 - 128 - 1) * 2`.
                `[228,130,0,149,160,114,253...`
                */
                constraints.push((
                    "Nibbles number when even number of nibbles & ext not longer than 55",
                    q_not_first.clone()
                        * q_enable.clone()
                        * is_even_nibbles.clone()
                        * (one.clone() - is_ext_longer_than_55.clone())
                        * (nibbles_count_cur.clone()
                            - nibbles_count_prev.clone()
                            - num_nibbles.clone()
                            - one.clone()), // - 1 is for branch position
                ));

                num_nibbles = (s_rlp2 - c128.clone()) * (one.clone() + one.clone()) - one.clone();

                /*
                When there is an odd number of nibbles in the extension node,
                we compute the number of nibbles as: `(s_rlp2 - 128) * 2`.
                By `s_rlp2 - 128` we get the number of bytes where nibbles are compressed. We
                multiply by 2 to get the nibbles, but then subtract 1 because in
                `s_main.bytes[0]` there is only 1 nibble.
                */
                constraints.push((
                    "Nibbles num when odd number (>1) of nibbles & ext not longer than 55",
                    q_not_first.clone()
                        * q_enable.clone()
                        * is_long_odd_nibbles.clone()
                        * (one.clone() - is_ext_longer_than_55.clone())
                        * (nibbles_count_cur.clone()
                            - nibbles_count_prev.clone()
                            - num_nibbles.clone()
                            - one.clone()), // - 1 is for branch position
                ));

                let s_bytes0 = meta.query_advice(s_main.bytes[0], Rotation::cur());
                num_nibbles =
                    (s_bytes0.clone() - c128.clone() - one.clone()) * (one.clone() + one.clone());

                /*
                When there is an even number of nibbles in the extension node and the extension
                node is longer than 55 bytes, the number of bytes containing the nibbles
                is given by `s_main.bytes[0]`.
                We compute the number of nibbles as: `(s_bytes0 - 128 - 1) * 2`.
                By `s_bytes0 - 128` we get the number of bytes where nibbles are compressed, but
                then we need to subtract 1 because `s_main.bytes[1]` does not contain any nibbles
                (it is just 0 when even number of nibbles).
                */
                constraints.push((
                    "Nibbles num when even number of nibbles & ext longer than 55",
                    q_not_first.clone()
                        * q_enable.clone()
                        * is_even_nibbles
                        * is_ext_longer_than_55.clone()
                        * (nibbles_count_cur.clone()
                            - nibbles_count_prev.clone()
                            - num_nibbles.clone()
                            - one.clone()), // - 1 is for branch position
                ));

                num_nibbles = (s_bytes0 - c128.clone()) * (one.clone() + one.clone()) - one.clone();

                /*
                When there is an odd number of nibbles in the extension node and the extension,
                node is longer than 55 bytes, the number of bytes containing the nibbles
                is given by `s_main.bytes[0]`.
                We compute the number of nibbles as: `(s_main.bytes[0] - 128) * 2`.
                By `s_main.bytes[0] - 128` we get the number of bytes where nibbles are compressed. We
                multiply by 2 to get the nibbles, but then subtract 1 because in
                `s_main.bytes[1]` there is only 1 nibble.

                Example:
                `[248,58,159,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,217,128,196,130,32,0,1,128,196,130,32,0,1,128,128,128,128,128,128,128,128,128,128,128,128,128]`
                */
                constraints.push((
                    "Nibbles num when odd number (>1) of nibbles & ext longer than 55",
                    q_not_first
                        * q_enable
                        * is_long_odd_nibbles
                        * is_ext_longer_than_55
                        * (nibbles_count_cur - nibbles_count_prev - num_nibbles - one.clone()), // - 1 is for branch position
                ));

                constraints
            });

            check_intermediate_mult(
                meta,
                q_enable.clone(),
                position_cols.clone(),
                s_main.clone(),
                accs,
                rot_into_branch_init,
                fixed_table,
                power_of_randomness[1].clone(),
            );
        }

        // Note: range_lookups are in extension_node_key.

        config
    }

    pub fn assign(
        &self,
        region: &mut Region<'_, F>,
        mpt_config: &MPTConfig<F>,
        pv: &mut ProofValues<F>,
        row: &MptWitnessRow<F>,
        offset: usize,
        is_s: bool,
    ) {
        if pv.is_extension_node {
            if is_s {
                // [228,130,0,149,160,114,253,150,133,18,192,156,19,241,162,51,210,24,1,151,16,
                // 48,7,177,42,60,49,34,230,254,242,79,132,165,90,75,249]

                // One nibble:
                // [226,16,160,172,105,12...
                // Could also be non-hashed branch:
                // [223,16,221,198,132,32,0,0,0,1,198,132,32,0,0,0,1,128,128,128,128,128,128,
                // 128,128,128,128,128,128,128,128,128]

                // [247,160,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
                // 213,128,194,32,1,128,194,32,1,128,128,128,128,128,128,128,128,128,128,128,
                // 128,128] [248,58,159,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
                // 0,0,0,0,0,0,0,0,0,0,0,0,217,128,196,130,32,0,1,128,196,130,32,0,1,128,128,
                // 128,128,128,128,128,128,128,128,128,128,128]

                // Intermediate RLC value and mult (after key)
                // to know which mult we need to use in c_advices.
                pv.acc_s = F::zero();
                pv.acc_mult_s = F::one();
                let len: usize;
                let len_full_bytes: usize; // how many pairs of nibbles
                if row.get_byte(1) <= 32 {
                    // key length is 1
                    len_full_bytes = 0;
                    len = 2 // [length byte, key]
                } else if row.get_byte(0) < 248 {
                    len_full_bytes = (row.get_byte(1) - 128) as usize - 1;
                    len = len_full_bytes + 1 + 2; // +1 for the first position which might contain 0 or 1 nibble
                } else {
                    len_full_bytes = (row.get_byte(1) - 128) as usize - 1;
                    len = len_full_bytes + 1 + 3; // +1 for the first position which might contain 0 or 1 nibble
                }
                mpt_config.compute_acc_and_mult(
                    &row.bytes,
                    &mut pv.acc_s,
                    &mut pv.acc_mult_s,
                    0,
                    len,
                );

                // Final RLC value.
                pv.acc_c = pv.acc_s;
                pv.acc_mult_c = pv.acc_mult_s;
                let mut start = C_RLP_START + 1;
                let mut len = HASH_WIDTH + 1;
                if row.get_byte(C_RLP_START + 1) == 0 {
                    // non-hashed branch in extension node
                    start = C_START;
                    len = HASH_WIDTH;
                }
                mpt_config.compute_acc_and_mult(
                    &row.bytes,
                    &mut pv.acc_c,
                    &mut pv.acc_mult_c,
                    start,
                    len,
                );

                let mut nibbles_rlc_mult = F::one();
                for ind in 0..len_full_bytes {
                    nibbles_rlc_mult *= mpt_config.randomness;
                }

                // We don't need to store `pv.acc_mult_c`, so we can store `nibbles_rlc_mult` using `acc_mult_c`.

                mpt_config
                    .assign_acc(region, pv.acc_s, pv.acc_mult_s, pv.acc_c, nibbles_rlc_mult, offset)
                    .ok();
            } else {
                // We use intermediate value from previous row (because
                // up to acc_s it's about key and this is the same
                // for both S and C).
                pv.acc_c = pv.acc_s;
                pv.acc_mult_c = pv.acc_mult_s;
                let mut start = C_RLP_START + 1;
                let mut len = HASH_WIDTH + 1;
                if row.get_byte(C_RLP_START + 1) == 0 {
                    // non-hashed branch in extension node
                    start = C_START;
                    len = HASH_WIDTH;
                }
                mpt_config.compute_acc_and_mult(
                    &row.bytes,
                    &mut pv.acc_c,
                    &mut pv.acc_mult_c,
                    start,
                    len,
                );

                mpt_config
                    .assign_acc(region, pv.acc_s, pv.acc_mult_s, pv.acc_c, F::zero(), offset)
                    .ok();
            }
            region
                .assign_advice(
                    || "assign key_rlc".to_string(),
                    mpt_config.accumulators.key.rlc,
                    offset,
                    || Value::known(pv.extension_node_rlc),
                )
                .ok();
        }
    }
}
