use halo2::{
    circuit::Chip,
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed},
    poly::Rotation,
};
use pairing::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::{
    helpers::into_words_expr,
    param::{HASH_WIDTH, KECCAK_INPUT_WIDTH, KECCAK_OUTPUT_WIDTH},
};

#[derive(Clone, Debug)]
pub(crate) struct ExtensionNodeConfig {}

pub(crate) struct ExtensionNodeChip<F> {
    config: ExtensionNodeConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> ExtensionNodeChip<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_not_first: Column<Fixed>,
        is_last_branch_child: Column<Advice>,
        is_extension_node: Column<Advice>,
        c_advices: [Column<Advice>; HASH_WIDTH],
        acc: Column<Advice>,
        acc_mult: Column<Advice>,
        keccak_table: [Column<Fixed>; KECCAK_INPUT_WIDTH + KECCAK_OUTPUT_WIDTH],
        is_s: bool,
    ) -> ExtensionNodeConfig {
        let config = ExtensionNodeConfig {};
        let one = Expression::Constant(F::from(1_u64));

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
          - the hash of extension node (extension node RLC hash is needed) needs to be
            checked whether it's at modified_node in branch1
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

        ---

        */

        // TODO: check extension node selector

        // Check whether branch hash is in extension node row.
        meta.lookup_any(|meta| {
            let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());

            let mut rot_into_last_child = -1;
            if !is_s {
                rot_into_last_child = -2;
            }

            // We need to do the lookup only if we are in the last branch child.
            let is_after_last_branch_child = meta.query_advice(
                is_last_branch_child,
                Rotation(rot_into_last_child),
            );

            // is_extension_node is in branch init row
            let mut is_extension_node_cur =
                meta.query_advice(is_extension_node, Rotation(-17));
            if !is_s {
                is_extension_node_cur =
                    meta.query_advice(is_extension_node, Rotation(-18));
            }

            // TODO: acc currently doesn't have branch ValueNode info (which 128 if nil)
            let acc = meta.query_advice(acc, Rotation(rot_into_last_child));
            let c128 = Expression::Constant(F::from(128));
            let mult =
                meta.query_advice(acc_mult, Rotation(rot_into_last_child));
            let branch_acc = acc + c128 * mult;

            let mut constraints = vec![];
            constraints.push((
                q_not_first.clone()
                    * is_after_last_branch_child.clone()
                    * is_extension_node_cur.clone()
                    * branch_acc, // TODO: replace with acc once ValueNode is added
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
                    q_not_first.clone()
                        * is_after_last_branch_child.clone()
                        * is_extension_node_cur.clone()
                        * word.clone(),
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
