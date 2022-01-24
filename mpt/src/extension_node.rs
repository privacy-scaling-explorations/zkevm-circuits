use halo2::{
    circuit::Chip,
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed},
    poly::Rotation,
};
use pairing::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::param::{KECCAK_INPUT_WIDTH, KECCAK_OUTPUT_WIDTH};

#[derive(Clone, Debug)]
pub(crate) struct ExtensionNodeConfig {}

pub(crate) struct ExtensionNodeChip<F> {
    config: ExtensionNodeConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> ExtensionNodeChip<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        not_first_level: Column<Fixed>,
        is_extension_node: Column<Advice>,
        acc: Column<Advice>,
        acc_mult: Column<Advice>,
        keccak_table: [Column<Fixed>; KECCAK_INPUT_WIDTH + KECCAK_OUTPUT_WIDTH],
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
            let not_first_level =
                meta.query_fixed(not_first_level, Rotation::cur());
            // TODO: not_first_level?

            let acc = meta.query_advice(acc, Rotation(-2));

            let is_extension_node =
                meta.query_advice(is_extension_node, Rotation(-18));

            // TODO: acc currently doesn't have branch ValueNode info (which 128 if nil)
            let c128 = Expression::Constant(F::from(128));
            let mult = meta.query_advice(acc_mult, Rotation(-2));
            let branch_acc = acc + c128 * mult;

            let mut constraints = vec![];
            constraints.push((
                not_first_level.clone()
                    * is_extension_node.clone()
                    * branch_acc, // TODO: replace with acc once ValueNode is added
                meta.query_fixed(keccak_table[0], Rotation::cur()),
            ));
            // TODO: express ext row c_advices in words
            /*
            for (ind, column) in sc_keccak.iter().enumerate() {
                // Any rotation that lands into branch can be used instead of -19.
                let keccak = meta.query_advice(*column, Rotation(-19));
                let keccak_table_i =
                    meta.query_fixed(keccak_table[ind + 1], Rotation::cur());
                constraints.push((
                    not_first_level.clone()
                        * is_extension_node.clone()
                        * keccak,
                    keccak_table_i,
                ));
            }
            */

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
