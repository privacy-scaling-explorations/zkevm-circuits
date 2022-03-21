use halo2_proofs::{
    circuit::Chip,
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, Selector, VirtualCells},
    poly::Rotation,
};
use pairing::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::{
    helpers::range_lookups,
    mpt::FixedTableTag,
    param::{BRANCH_0_C_START, BRANCH_0_S_START, HASH_WIDTH, RLP_NUM},
};

#[derive(Clone, Debug)]
pub(crate) struct BranchConfig {}

pub(crate) struct BranchChip<F> {
    config: BranchConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> BranchChip<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: Selector,
        q_not_first: Column<Fixed>,
        s_rlp1: Column<Advice>,
        s_rlp2: Column<Advice>,
        c_rlp1: Column<Advice>,
        c_rlp2: Column<Advice>,
        s_advices: [Column<Advice>; HASH_WIDTH],
        c_advices: [Column<Advice>; HASH_WIDTH],
        is_branch_init: Column<Advice>,
        is_branch_child: Column<Advice>,
        is_last_branch_child: Column<Advice>,
        node_index: Column<Advice>,
        is_modified: Column<Advice>, // whether this branch node is modified
        modified_node: Column<Advice>, // index of the modified node
        is_at_first_nibble: Column<Advice>, // needed when leaf is turned into branch
        first_nibble: Column<Advice>, /* needed when leaf is turned into branch - first nibble of
                                      * the key stored in a leaf (because the existing leaf will
                                      * jump to this position in added branch) */
        fixed_table: [Column<Fixed>; 3],
    ) -> BranchConfig {
        let config = BranchConfig {};
        let one = Expression::Constant(F::one());

        let sel = |meta: &mut VirtualCells<F>| {
            let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
            let is_branch_init = meta.query_advice(is_branch_init, Rotation::cur());

            q_not_first * (one.clone() - is_branch_init)
        };

        // Range check for s_advices and c_advices being bytes.
        range_lookups(
            meta,
            sel,
            s_advices.to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );
        range_lookups(
            meta,
            sel,
            c_advices.to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );

        // Empty nodes have 0 at s_rlp2, have 128 at s_advices[0] and 0 everywhere else:
        // [0, 0, 128, 0, ..., 0]
        // While non-empty nodes have 160 at s_rlp2 and then any byte at *_advices:
        // [0, 160, a0, ..., a31]
        meta.create_gate("empty and non-empty", |meta| {
            let q_enable = meta.query_selector(q_enable);
            let mut constraints = vec![];

            let is_branch_child_cur = meta.query_advice(is_branch_child, Rotation::cur());
            let s_rlp2 = meta.query_advice(s_rlp2, Rotation::cur());
            let c_rlp2 = meta.query_advice(c_rlp2, Rotation::cur());

            // Note that s_rlp1 and c_rlp1 store RLP stream length data (subtracted
            // by the number of bytes in branch rows until that position).

            let c128 = Expression::Constant(F::from(128_u64));
            let c160 = Expression::Constant(F::from(160_u64));

            // In empty nodes: s_rlp2 = 0. In non-empty nodes: s_rlp2 = 160.
            constraints.push((
                "s_rlp2 = 0 or s_rlp2 = 160",
                q_enable.clone()
                    * is_branch_child_cur.clone()
                    * s_rlp2.clone()
                    * (s_rlp2.clone() - c160.clone()),
            ));
            constraints.push((
                "c_rlp2 = 0 or c_rlp2 = 160",
                q_enable.clone()
                    * is_branch_child_cur.clone()
                    * c_rlp2.clone()
                    * (c_rlp2.clone() - c160.clone()),
            ));

            // No further constraints needed for non-empty nodes (rlp2 needs to be 160
            // and values need to be bytes which is constrained by the lookups
            // on s_advices and c_advices).

            let s_advice0 = meta.query_advice(s_advices[0], Rotation::cur());
            constraints.push((
                "s_advices[0] = 128 in empty",
                q_enable.clone()
                    * is_branch_child_cur.clone()
                    * (s_rlp2.clone() - c160.clone())
                    * (s_advice0 - c128.clone()), /* If s_rlp2 = 0, then s_advices[0] can be any
                                                   * value (0-255). */
            ));
            let c_advice0 = meta.query_advice(c_advices[0], Rotation::cur());
            constraints.push((
                "c_advices[0] = 128 in empty",
                q_enable.clone()
                    * is_branch_child_cur.clone()
                    * (c_rlp2.clone() - c160.clone())
                    * (c_advice0 - c128), /* If c_rlp2 = 0, then c_advices[0] can be any value
                                           * (0-255). */
            ));

            for col in s_advices.iter().skip(1) {
                let s = meta.query_advice(*col, Rotation::cur());
                constraints.push((
                    "s_advices[i] = 0 for i > 0 in empty",
                    q_enable.clone()
                        * is_branch_child_cur.clone()
                        * (s_rlp2.clone() - c160.clone())
                        * s,
                ));
            }
            for col in c_advices.iter().skip(1) {
                let c = meta.query_advice(*col, Rotation::cur());
                constraints.push((
                    "c_advices[i] = 0 for i > 0 in empty",
                    q_enable.clone()
                        * is_branch_child_cur.clone()
                        * (c_rlp2.clone() - c160.clone())
                        * c,
                ));
            }

            // Note that the attacker could put 160 in an empty node (the constraints
            // above doesn't/can't prevent this) and thus try to
            // modify the branch RLC (used for checking the hash of a branch), like:
            // [0, 160, 128, 0, ..., 0]
            // But then the constraints related to branch RLP would fail - first RLP bytes
            // specifies the length of the stream and this value is checked with
            // the actual length - the actual length being computed as 33 values in
            // non-empty nodes and 1 value in empty node.

            constraints
        });

        meta.create_gate("branch equalities", |meta| {
            let q_enable = meta.query_selector(q_enable);
            let mut constraints = vec![];

            let is_branch_child_cur = meta.query_advice(is_branch_child, Rotation::cur());
            let node_index_cur = meta.query_advice(node_index, Rotation::cur());
            let modified_node = meta.query_advice(modified_node, Rotation::cur());
            let is_modified = meta.query_advice(is_modified, Rotation::cur());
            let is_at_first_nibble = meta.query_advice(is_at_first_nibble, Rotation::cur());
            let first_nibble = meta.query_advice(first_nibble, Rotation::cur());

            // is_modified is:
            //   0 when node_index_cur != modified_node
            //   1 when node_index_cur == modified_node (it's checked elsewhere for
            // booleanity)
            constraints.push((
                "is modified",
                q_enable.clone()
                    * is_branch_child_cur.clone()
                    * is_modified.clone()
                    * (node_index_cur.clone() - modified_node.clone()),
            ));

            // is_at_first_nibble is:
            //   0 when node_index_cur != first_nibble
            //   1 when node_index_cur == first_nibble (it's checked elsewhere for
            // booleanity)
            constraints.push((
                "is at first nibble",
                q_enable.clone()
                    * is_branch_child_cur.clone()
                    * is_at_first_nibble.clone()
                    * (node_index_cur.clone() - first_nibble.clone()),
            ));

            let s_rlp2 = meta.query_advice(s_rlp2, Rotation::cur());
            let c_rlp2 = meta.query_advice(c_rlp2, Rotation::cur());

            // We don't need to compare s_rlp1 = c_rlp1 because there is stored
            // info about S and C RLP length
            constraints.push((
                "rlp 2",
                q_enable.clone()
                    * is_branch_child_cur.clone()
                    * (s_rlp2 - c_rlp2)
                    * (node_index_cur.clone() - modified_node.clone()),
            ));

            for (ind, col) in s_advices.iter().enumerate() {
                let s = meta.query_advice(*col, Rotation::cur());
                let c = meta.query_advice(c_advices[ind], Rotation::cur());
                constraints.push((
                    "s = c when NOT is_modified",
                    q_enable.clone()
                        * is_branch_child_cur.clone()
                        * (s.clone() - c.clone())
                        * (node_index_cur.clone() - modified_node.clone()),
                ));

                // When it's NOT placeholder branch, is_modified = is_at_first_nibble.
                // When it's placeholder branch, is_modified != is_at_first_nibble.
                // This is used instead of having is_branch_s_placeholder and
                // is_branch_c_placeholder columns - we only have this info in
                // branch init where we don't need additional columns.
                // When there is a placeholder branch, there are only two nodes - one at
                // is_modified and one at is_at_first_nibble - at other
                // positions there need to be nil nodes.

                // TODO: This might be optimized once the check for branch is added - check
                // that when s_rlp2 = 0, it needs to be s = 0 and c = 0, except the first byte
                // is 128. So, only s_rlp2 could be checked here instead of all
                // s and c.
                constraints.push((
                    "s = 0 when placeholder and is neither is_modified or is_at_first_nibble",
                    q_enable.clone()
                        * is_branch_child_cur.clone()
                        * (is_modified.clone() - is_at_first_nibble.clone()) // this is 0 when NOT placeholder
                        * (one.clone() - is_modified.clone())
                        * (one.clone() - is_at_first_nibble.clone())
                        * s,
                ));
                constraints.push((
                    "c = 0 when placeholder and is neither is_modified or is_at_first_nibble",
                    q_enable.clone()
                        * is_branch_child_cur.clone()
                        * (is_modified.clone() - is_at_first_nibble.clone()) // this is 0 when NOT placeholder
                        * (one.clone() - is_modified.clone())
                        * (one.clone() - is_at_first_nibble.clone())
                        * c,
                ));
            }

            // TODO: use permutation argument to make sure modified_node is the same in all
            // branch rows.

            // TODO: use permutation argument to make sure first_nibble is the same in all
            // branch rows.

            constraints
        });

        meta.create_gate("RLP length", |meta| {
            let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
            let mut constraints = vec![];

            let is_branch_init_prev = meta.query_advice(is_branch_init, Rotation::prev());
            let two_rlp_bytes_s = meta.query_advice(s_rlp1, Rotation::prev());
            let three_rlp_bytes_s = meta.query_advice(s_rlp2, Rotation::prev());
            let two_rlp_bytes_c = meta.query_advice(c_rlp1, Rotation::prev());
            let three_rlp_bytes_c = meta.query_advice(c_rlp2, Rotation::prev());

            let rlp_byte1_s =
                meta.query_advice(s_advices[BRANCH_0_S_START - RLP_NUM + 1], Rotation::prev());
            let rlp_byte2_s =
                meta.query_advice(s_advices[BRANCH_0_S_START - RLP_NUM + 2], Rotation::prev());
            let rlp_byte1_c =
                meta.query_advice(s_advices[BRANCH_0_C_START - RLP_NUM + 1], Rotation::prev());
            let rlp_byte2_c =
                meta.query_advice(s_advices[BRANCH_0_C_START - RLP_NUM + 2], Rotation::prev());

            let one = Expression::Constant(F::one());
            let c32 = Expression::Constant(F::from(32_u64));
            let c256 = Expression::Constant(F::from(256_u64));
            let c160_inv = Expression::Constant(F::from(160_u64).invert().unwrap());

            let s_rlp1_cur = meta.query_advice(s_rlp1, Rotation::cur());
            let s_rlp2_cur = meta.query_advice(s_rlp2, Rotation::cur());
            let c_rlp1_cur = meta.query_advice(c_rlp1, Rotation::cur());
            let c_rlp2_cur = meta.query_advice(c_rlp2, Rotation::cur());

            // s bytes in this row:
            // If empty, then s_rlp2 = 0:
            // s_rlp2 * c160_inv * c32 + 1 = 1
            // If non-empty, then s_rlp2 = 160:
            // s_rlp2 * c160_inv * c32 + 1 = 33
            let s_bytes = s_rlp2_cur * c160_inv.clone() * c32.clone() + one.clone();
            let c_bytes = c_rlp2_cur * c160_inv * c32 + one.clone();

            // Short:
            // [1,0,1,0,248,81,0,248,81,0,3,0,0,0,...
            // Long:
            // [0,1,0,1,249,2,17,249,2,17,7,0,0,0,...

            // is_branch_child with node_index = 0
            constraints.push((
                "first branch children two RLP meta bytes S",
                q_not_first.clone()
                    * is_branch_init_prev.clone()
                    * two_rlp_bytes_s
                    * (rlp_byte1_s.clone() - s_bytes.clone() - s_rlp1_cur.clone()),
            ));
            constraints.push((
                "first branch children two RLP meta bytes C",
                q_not_first.clone()
                    * is_branch_init_prev.clone()
                    * two_rlp_bytes_c
                    * (rlp_byte1_c.clone() - c_bytes.clone() - c_rlp1_cur.clone()),
            ));
            constraints.push((
                "first branch children three RLP meta bytes S",
                q_not_first.clone()
                    * is_branch_init_prev.clone()
                    * three_rlp_bytes_s
                    * (rlp_byte1_s * c256.clone() + rlp_byte2_s
                        - s_bytes.clone()
                        - s_rlp1_cur.clone()),
            ));
            constraints.push((
                "first branch children three RLP meta bytes C",
                q_not_first.clone()
                    * is_branch_init_prev.clone()
                    * three_rlp_bytes_c
                    * (rlp_byte1_c * c256 + rlp_byte2_c - c_bytes.clone() - c_rlp1_cur.clone()),
            ));

            // is_branch_child with node_index > 0
            let is_branch_child_cur = meta.query_advice(is_branch_child, Rotation::cur());
            let s_rlp1_prev = meta.query_advice(s_rlp1, Rotation::prev());
            let c_rlp1_prev = meta.query_advice(c_rlp1, Rotation::prev());
            constraints.push((
                "branch children (node_index > 0) S",
                q_not_first.clone()
                    * is_branch_child_cur.clone()
                    * (one.clone() - is_branch_init_prev.clone())
                    * (s_rlp1_prev - s_bytes.clone() - s_rlp1_cur.clone()),
            ));
            constraints.push((
                "branch children (node_index > 0) C",
                q_not_first.clone()
                    * is_branch_child_cur.clone()
                    * (one.clone() - is_branch_init_prev.clone())
                    * (c_rlp1_prev - c_bytes.clone() - c_rlp1_cur.clone()),
            ));

            // In final branch child s_rlp1 and c_rlp1 need to be 1 (because RLP length
            // specifies also ValueNode which occupies 1 byte).
            // TODO: ValueNode
            let is_last_branch_child = meta.query_advice(is_last_branch_child, Rotation::cur());
            constraints.push((
                "branch last child S",
                q_not_first.clone()
                    * is_last_branch_child.clone()
                    * (s_rlp1_cur.clone() - one.clone()),
            ));
            constraints.push((
                "branch last child C",
                q_not_first.clone() * is_last_branch_child.clone() * (c_rlp1_cur.clone() - one),
            ));

            constraints
        });

        meta.create_gate("branch children selectors", |meta| {
            let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());

            let mut constraints = vec![];
            let is_branch_child_prev = meta.query_advice(is_branch_child, Rotation::prev());
            let is_branch_child_cur = meta.query_advice(is_branch_child, Rotation::cur());
            let is_branch_init_prev = meta.query_advice(is_branch_init, Rotation::prev());
            let is_last_branch_child_prev =
                meta.query_advice(is_last_branch_child, Rotation::prev());
            let is_last_branch_child_cur = meta.query_advice(is_last_branch_child, Rotation::cur());

            // TODO: is_compact_leaf + is_branch_child + is_branch_init + ... = 1
            // It's actually more complex that just sum = 1.
            // For example, we have to allow is_last_branch_child to have value 1 only
            // when is_branch_child. So we need to add constraint like:
            // (is_branch_child - is_last_branch_child) * is_last_branch_child
            // There are already constraints "is last branch child 1 and 2" below
            // to make sure that is_last_branch_child is 1 only when node_index = 15.

            // TODO: not_first_level constraints (needs to be 0 or 1 and needs to
            // be strictly decreasing)

            // if we have branch child, we can only have branch child or branch init in the
            // previous row
            constraints.push((
                "before branch children",
                q_not_first.clone()
                    * is_branch_child_cur.clone()
                    * (is_branch_child_prev.clone() - one.clone())
                    * (is_branch_init_prev.clone() - one.clone()),
            ));

            // If we have is_branch_init in the previous row, we have
            // is_branch_child with node_index = 0 in the current row.
            constraints.push((
                "first branch children 1",
                q_not_first.clone()
                    * is_branch_init_prev.clone()
                    * (is_branch_child_cur.clone() - one.clone()), // is_branch_child has to be 1
            ));
            // We could have only one constraint using sum, but then we would need
            // to limit node_index (to prevent values like -1). Now, node_index is
            // limited by ensuring it's first value is 0, its last value is 15,
            // and it's increasing by 1.
            let node_index_cur = meta.query_advice(node_index, Rotation::cur());
            constraints.push((
                "first branch children 2",
                q_not_first.clone()
                    * is_branch_init_prev.clone()
                    * node_index_cur.clone(), // node_index has to be 0
            ));

            // When is_branch_child changes back to 0, previous node_index has to be 15.
            let node_index_prev = meta.query_advice(node_index, Rotation::prev());
            constraints.push((
                "last branch children",
                q_not_first.clone()
                    * (one.clone() - is_branch_init_prev.clone()) // ignore if previous row was is_branch_init (here is_branch_child changes too)
                    * (is_branch_child_prev.clone()
                        - is_branch_child_cur.clone()) // for this to work properly make sure to have constraints like is_branch_child + is_keccak_leaf + ... = 1
                    * (node_index_prev
                        - Expression::Constant(F::from(15_u64))), // node_index has to be 15
            ));

            // When node_index is not 15, is_last_branch_child needs to be 0.
            constraints.push((
                "is last branch child 1",
                q_not_first.clone()
                    * is_last_branch_child_cur
                    * (node_index_cur.clone() // for this to work properly is_last_branch_child needs to have value 1 only when is_branch_child
                        - Expression::Constant(F::from(15_u64))),
            ));
            // When node_index is 15, is_last_branch_child needs to be 1.
            constraints.push((
                "is last branch child 2",
                q_not_first.clone()
                    * (one.clone() - is_branch_init_prev.clone()) // ignore if previous row was is_branch_init (here is_branch_child changes too)
                    * (is_last_branch_child_prev - one.clone())
                    * (is_branch_child_prev
                        - is_branch_child_cur.clone()), /* for this to work properly make sure
                                                         * to have constraints like
                                                         * is_branch_child + is_keccak_leaf +
                                                         * ... = 1 */
            ));

            // node_index is increasing by 1 for is_branch_child
            let node_index_prev = meta.query_advice(node_index, Rotation::prev());
            constraints.push((
                "node index increasing for branch children",
                q_not_first.clone()
                    * is_branch_child_cur.clone()
                    * node_index_cur.clone() // ignore if node_index = 0
                    * (node_index_cur.clone() - node_index_prev - one.clone()),
            ));

            // modified_node needs to be the same for all branch nodes
            let modified_node_prev = meta.query_advice(modified_node, Rotation::prev());
            let modified_node_cur = meta.query_advice(modified_node, Rotation::cur());
            constraints.push((
                "modified node the same for all branch children",
                q_not_first.clone()
                    * is_branch_child_cur
                    * node_index_cur // ignore if node_index = 0
                    * (modified_node_cur.clone() - modified_node_prev),
            ));

            constraints
        });

        config
    }

    pub fn construct(config: BranchConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }
}

impl<F: FieldExt> Chip<F> for BranchChip<F> {
    type Config = BranchConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}
