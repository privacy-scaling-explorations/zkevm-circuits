use halo2::{
    circuit::Chip,
    plonk::{
        Advice, Column, ConstraintSystem, Expression, Fixed, VirtualCells,
    },
    poly::Rotation,
};
use pairing::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::{
    helpers::{compute_rlc, into_words_expr},
    mpt::FixedTableTag,
    param::{
        HASH_WIDTH, IS_EXTENSION_EVEN_KEY_LEN_POS, IS_EXTENSION_KEY_LONG_POS,
        IS_EXTENSION_KEY_SHORT_POS, IS_EXTENSION_NODE_POS,
        IS_EXTENSION_ODD_KEY_LEN_POS, KECCAK_INPUT_WIDTH, KECCAK_OUTPUT_WIDTH,
        LAYOUT_OFFSET,
    },
};

#[derive(Clone, Debug)]
pub(crate) struct ExtensionNodeConfig {}

pub(crate) struct ExtensionNodeChip<F> {
    config: ExtensionNodeConfig,
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

impl<F: FieldExt> ExtensionNodeChip<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: impl Fn(&mut VirtualCells<'_, F>) -> Expression<F>,
        not_first_level: Column<Fixed>,
        q_not_first: Column<Fixed>,
        s_rlp1: Column<Advice>,
        s_rlp2: Column<Advice>,
        c_rlp2: Column<Advice>,
        s_advices: [Column<Advice>; HASH_WIDTH],
        c_advices: [Column<Advice>; HASH_WIDTH],
        acc_s: Column<Advice>,
        acc_mult_s: Column<Advice>,
        acc_c: Column<Advice>,
        acc_mult_c: Column<Advice>,
        keccak_table: [Column<Fixed>; KECCAK_INPUT_WIDTH + KECCAK_OUTPUT_WIDTH],
        sc_keccak: [Column<Advice>; KECCAK_OUTPUT_WIDTH],
        r_table: Vec<Expression<F>>,
        is_s: bool,
    ) -> ExtensionNodeConfig {
        let config = ExtensionNodeConfig {};
        let one = Expression::Constant(F::from(1_u64));
        let c128 = Expression::Constant(F::from(128));
        let c226 = Expression::Constant(F::from(226));
        let mut rot_into_branch_init = -17;
        if !is_s {
            rot_into_branch_init = -18;
        }

        // Note that is_extension_node is not explicitly checked (for example, what if
        // the attacker sets is_extension_node = 1 for a regular branch or the other way around),
        // however, this check is done implicitly with key RLC constraints (the final key RLC
        // will fail if is_extension_node is set to 1 for a regular branch or if is_extension_node
        // is set to 0 for an extension node).
        meta.create_gate("Extension node selectors", |meta| {
            let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
            let q_enable = q_enable(meta);
            let mut constraints = vec![];

            // Get into branch init:
            let is_extension_node = meta.query_advice(
                s_advices[IS_EXTENSION_NODE_POS - LAYOUT_OFFSET],
                Rotation(rot_into_branch_init),
            );

            // NOTE: is_key_even and is_key_odd is for number of nibbles that
            // are compactly encoded.
            let is_key_even = meta.query_advice(
                s_advices[IS_EXTENSION_EVEN_KEY_LEN_POS - LAYOUT_OFFSET],
                Rotation(rot_into_branch_init),
            );
            let is_key_odd = meta.query_advice(
                s_advices[IS_EXTENSION_ODD_KEY_LEN_POS - LAYOUT_OFFSET],
                Rotation(rot_into_branch_init),
            );
            let is_short = meta.query_advice(
                s_advices[IS_EXTENSION_KEY_SHORT_POS - LAYOUT_OFFSET],
                Rotation(rot_into_branch_init),
            );
            let is_long = meta.query_advice(
                s_advices[IS_EXTENSION_KEY_LONG_POS - LAYOUT_OFFSET],
                Rotation(rot_into_branch_init),
            );
            let bool_check_is_extension_node = is_extension_node.clone()
                * (one.clone() - is_extension_node.clone());
            let bool_check_is_key_even =
                is_key_even.clone() * (one.clone() - is_key_even.clone());
            let bool_check_is_key_odd =
                is_key_odd.clone() * (one.clone() - is_key_odd.clone());
            let bool_check_is_short =
                is_short.clone() * (one.clone() - is_short.clone());
            let bool_check_is_long =
                is_long.clone() * (one.clone() - is_long.clone());

            constraints.push((
                "bool is_extension_node",
                q_not_first.clone()
                    * q_enable.clone()
                    * bool_check_is_extension_node,
            ));
            constraints.push((
                "bool is_key_even",
                q_not_first.clone() * q_enable.clone() * bool_check_is_key_even,
            ));
            constraints.push((
                "bool is_key_odd",
                q_not_first.clone() * q_enable.clone() * bool_check_is_key_odd,
            ));
            constraints.push((
                "bool is_short",
                q_not_first.clone() * q_enable.clone() * bool_check_is_short,
            ));
            constraints.push((
                "bool is_long",
                q_not_first.clone() * q_enable.clone() * bool_check_is_long,
            ));

            constraints.push((
                "is_key_even + is_key_odd = 1",
                q_not_first.clone()
                    * q_enable.clone()
                    * (is_key_even.clone() + is_key_odd.clone() - one.clone()),
            ));
            constraints.push((
                "is_short + is_long = 1",
                q_not_first.clone()
                    * q_enable.clone()
                    * (is_short.clone() + is_long.clone() - one.clone()),
            ));

            /*
            If key_len = 1 (is_short = 1, is_long = 0)
            [226,16,160,172,105,12...
            there is no byte specifying key length, but in this case the first byte is 226.
            So, when s_rlp1 = 226, we need to ensure is_key_odd = 1, is_key_even = 0
            (is_key_even = 0 can be omitted because of the constraints above).

            If key_len > 1 (is_short = 0, is_long = 1)
            [228,130,0,149,160,114,253,150,133,18,192,156,19,241,162,51,210,24,1,151,16,48,7,177,42,60,49,34,230,254,242,79,132,165,90,75,249]
            the second byte specifies the key_len (we need to subract 128 to get it).
            */

            let s_rlp1 = meta.query_advice(s_rlp1, Rotation::cur());
            let s_advices0 = meta.query_advice(s_advices[0], Rotation::cur());

            // This prevents setting is_short = 1 when it's not short (s_rlp1 > 226 in that case):
            // Using this constraints and bool & sum (is_short + is_long) constraints above
            // the selectors are ensured to be set properly.
            constraints.push((
                "is_short implies s_rlp1 = 226",
                q_not_first.clone()
                    * q_enable.clone()
                    * is_short.clone()
                    * (s_rlp1 - c226),
            ));
            constraints.push((
                "is_short implies is_key_odd",
                q_not_first.clone()
                    * q_enable.clone()
                    * is_short.clone()
                    * is_key_odd.clone(),
            ));

            // This prevents setting is_key_even = 1 when it's not even,
            // because when it's not even s_advices0 != 0 (hexToCompact adds 16).
            // Using this constraints and bool & sum (is_key_even + is_key_odd) constraints above
            // the selectors are ensured to be set properly.
            constraints.push((
                "is_long & is_key_even implies s_advices0 = 0",
                q_not_first.clone()
                    * q_enable.clone()
                    * is_long.clone()
                    * is_key_even.clone()
                    * s_advices0,
            ));

            constraints
        });

        // Check whether branch hash is in extension node row.
        meta.lookup_any(|meta| {
            let q_enable = q_enable(meta);
            let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());

            let mut acc = meta.query_advice(acc_s, Rotation(-1));
            let mut mult = meta.query_advice(acc_mult_s, Rotation(-1));
            if !is_s {
                acc = meta.query_advice(acc_c, Rotation(-2));
                mult = meta.query_advice(acc_mult_c, Rotation(-2));
            }
            // TODO: acc currently doesn't have branch ValueNode info (which 128 if nil)
            let branch_acc = acc + c128 * mult;

            let mut constraints = vec![];
            constraints.push((
                q_not_first.clone() * q_enable.clone() * branch_acc, // TODO: replace with acc once ValueNode is added
                meta.query_fixed(keccak_table[0], Rotation::cur()),
            ));

            let mut sc_hash = vec![];
            // Note: extension node has branch hash always in c_advices.
            for column in c_advices.iter() {
                sc_hash.push(meta.query_advice(*column, Rotation::cur()));
            }
            let words = into_words_expr(sc_hash);
            for (ind, word) in words.iter().enumerate() {
                let keccak_table_i =
                    meta.query_fixed(keccak_table[ind + 1], Rotation::cur());
                constraints.push((
                    q_not_first.clone() * q_enable.clone() * word.clone(),
                    keccak_table_i,
                ));
            }

            constraints
        });

        // TODO: check that key bytes are 0 after key len

        // Check whether RLC are properly computed.
        meta.create_gate("Extension node RLC", |meta| {
            let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
            let q_enable = q_enable(meta);
            let mut constraints = vec![];

            let s_rlp1 = meta.query_advice(s_rlp1, Rotation::cur());
            let mut rlc = s_rlp1;
            let s_rlp2 = meta.query_advice(s_rlp2, Rotation::cur());
            rlc = rlc + s_rlp2 * r_table[0].clone();

            let s_advices_rlc =
                compute_rlc(meta, s_advices.to_vec(), 1, one, r_table.clone());
            rlc = rlc + s_advices_rlc;

            let acc_s = meta.query_advice(acc_s, Rotation::cur());
            constraints.push((
                "acc_s",
                q_not_first.clone() * q_enable.clone() * (rlc - acc_s.clone()),
            ));

            let c_rlp2 = meta.query_advice(c_rlp2, Rotation::cur());
            let c160 = Expression::Constant(F::from(160_u64));
            constraints.push((
                "c_rlp2",
                q_not_first.clone()
                    * q_enable.clone()
                    * (c_rlp2.clone() - c160),
            ));

            let acc_mult_s = meta.query_advice(acc_mult_s, Rotation::cur());
            rlc = acc_s + c_rlp2 * acc_mult_s.clone();

            let c_advices_rlc =
                compute_rlc(meta, c_advices.to_vec(), 0, acc_mult_s, r_table);
            rlc = rlc + c_advices_rlc;

            let acc_c = meta.query_advice(acc_c, Rotation::cur());
            constraints.push(("acc_c", q_not_first * q_enable * (rlc - acc_c)));

            constraints
        });

        // Check whether extension node S and C have the same key.
        if !is_s {
            meta.create_gate("Extension node key same for S and C", |meta| {
                let q_not_first =
                    meta.query_fixed(q_not_first, Rotation::cur());
                let q_enable = q_enable(meta);
                let mut constraints = vec![];

                let s_rlp1_prev = meta.query_advice(s_rlp1, Rotation::prev());
                let s_rlp1 = meta.query_advice(s_rlp1, Rotation::cur());
                let s_rlp2_prev = meta.query_advice(s_rlp2, Rotation::prev());
                let s_rlp2 = meta.query_advice(s_rlp2, Rotation::cur());

                constraints.push((
                    "s_rlp1",
                    q_not_first.clone()
                        * q_enable.clone()
                        * (s_rlp1 - s_rlp1_prev),
                ));
                constraints.push((
                    "s_rlp2",
                    q_not_first.clone()
                        * q_enable.clone()
                        * (s_rlp2 - s_rlp2_prev),
                ));
                for col in s_advices.iter() {
                    let s_prev = meta.query_advice(*col, Rotation::prev());
                    let s = meta.query_advice(*col, Rotation::cur());
                    constraints.push((
                        "s_advices",
                        q_not_first.clone() * q_enable.clone() * (s - s_prev),
                    ));
                }

                constraints
            });
        }

        // Check whether extension node hash is in parent branch.
        meta.lookup_any(|meta| {
            let q_enable = q_enable(meta);
            let not_first_level =
                meta.query_fixed(not_first_level, Rotation::cur());

            let mut constraints = vec![];

            let acc_c = meta.query_advice(acc_c, Rotation::cur());
            constraints.push((
                not_first_level.clone() * q_enable.clone() * acc_c,
                meta.query_fixed(keccak_table[0], Rotation::cur()),
            ));

            for (ind, column) in sc_keccak.iter().enumerate() {
                // Any rotation that lands into branch can be used instead of -21.
                let keccak = meta.query_advice(*column, Rotation(-21));
                let keccak_table_i =
                    meta.query_fixed(keccak_table[ind + 1], Rotation::cur());
                constraints.push((
                    not_first_level.clone() * q_enable.clone() * keccak,
                    keccak_table_i,
                ));
            }

            constraints
        });

        config
    }

    pub fn construct(config: ExtensionNodeConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }
}

impl<F: FieldExt> Chip<F> for ExtensionNodeChip<F> {
    type Config = ExtensionNodeConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}
