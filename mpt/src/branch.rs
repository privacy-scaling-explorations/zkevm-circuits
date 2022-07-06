use halo2_proofs::{
    circuit::Chip,
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, Selector, VirtualCells},
    poly::Rotation,
};
use pairing::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::{
    helpers::{get_bool_constraint, range_lookups},
    mpt::FixedTableTag,
    param::{
        BRANCH_0_C_START, BRANCH_0_S_START, HASH_WIDTH, IS_BRANCH_C_PLACEHOLDER_POS,
        IS_BRANCH_S_PLACEHOLDER_POS, LAYOUT_OFFSET, RLP_NUM,
    },
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
        q_enable: Column<Fixed>,
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
        is_at_drifted_pos: Column<Advice>, // needed when leaf is turned into branch
        drifted_pos: Column<Advice>, /* needed when leaf is turned into branch - first nibble of
                                      * the key stored in a leaf (because the existing leaf will
                                      * jump to this position in added branch) */
        is_node_hashed_s: Column<Advice>,
        is_node_hashed_c: Column<Advice>,
        fixed_table: [Column<Fixed>; 3],
    ) -> BranchConfig {
        let config = BranchConfig {};
        let one = Expression::Constant(F::one());

        let sel = |meta: &mut VirtualCells<F>| {
            let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
            let is_branch_init = meta.query_advice(is_branch_init, Rotation::cur());

            q_not_first * (one.clone() - is_branch_init)
        };

        // Note: branch init row contains selectors related to drifted_pos,
        // modified_node, branch placeholders, extension node selectors.
        // There is no need for drifted_pos / modified_node constraints there as
        // these are just read from there and then selectors in branch node rows are set
        // and restricted there. Branch placeholder needs to be checked if boolean
        // (however, if 1 is set instead of 0 or the other way around, the
        // constraints related to address/ key RLC will fail).
        // Extension node related selectors are checked in extension node chips.

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

        meta.create_gate(
            "branch S and C equal at NON modified_node position",
            |meta| {
                let q_enable = meta.query_fixed(q_enable, Rotation::cur());
                let mut constraints = vec![];

                let is_branch_child_cur = meta.query_advice(is_branch_child, Rotation::cur());
                let node_index_cur = meta.query_advice(node_index, Rotation::cur());
                let modified_node = meta.query_advice(modified_node, Rotation::cur());
                let is_modified = meta.query_advice(is_modified, Rotation::cur());
                let is_at_drifted_pos = meta.query_advice(is_at_drifted_pos, Rotation::cur());

                let s_rlp2 = meta.query_advice(s_rlp2, Rotation::cur());
                let c_rlp2 = meta.query_advice(c_rlp2, Rotation::cur());

                // We do not compare s_rlp1 = c_rlp1 because there is stored
                // info about S and C RLP length.
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

                    // When it's NOT placeholder branch, is_modified = is_at_drifted_pos.
                    // When it's placeholder branch, is_modified != is_at_drifted_pos.
                    // This is used instead of having is_branch_s_placeholder and
                    // is_branch_c_placeholder columns - we only have this info in
                    // branch init where we don't need additional columns.
                    // When there is a placeholder branch, there are only two nodes - one at
                    // is_modified and one at is_at_drifted_pos - at other
                    // positions there need to be nil nodes.

                    // TODO: This might be optimized once the check for branch is added - check
                    // that when s_rlp2 = 0, it needs to be s = 0 and c = 0, except the first byte
                    // is 128. So, only s_rlp2 could be checked here instead of all
                    // s and c.
                    constraints.push((
                        "s = 0 when placeholder and is neither is_modified or is_at_drifted_pos",
                        q_enable.clone()
                        * is_branch_child_cur.clone()
                        * (is_modified.clone() - is_at_drifted_pos.clone()) // this is 0 when NOT placeholder
                        * (one.clone() - is_modified.clone())
                        * (one.clone() - is_at_drifted_pos.clone())
                        * s,
                    ));
                    constraints.push((
                        "c = 0 when placeholder and is neither is_modified or is_at_drifted_pos",
                        q_enable.clone()
                        * is_branch_child_cur.clone()
                        * (is_modified.clone() - is_at_drifted_pos.clone()) // this is 0 when NOT placeholder
                        * (one.clone() - is_modified.clone())
                        * (one.clone() - is_at_drifted_pos.clone())
                        * c,
                    ));
                }

                constraints
            },
        );

        meta.create_gate("RLP length", |meta| {
            let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
            let mut constraints = vec![];

            let is_branch_init_prev = meta.query_advice(is_branch_init, Rotation::prev());
            /*
            rlp1, rlp2: 1, 1 means 1 RLP byte
            rlp1, rlp2: 1, 0 means 2 RLP bytes
            rlp1, rlp2: 0, 1 means 3 RLP bytes
            */

            let s1 = meta.query_advice(s_rlp1, Rotation::prev());
            let s2 = meta.query_advice(s_rlp2, Rotation::prev());
            let c1 = meta.query_advice(s_advices[0], Rotation::prev());
            let c2 = meta.query_advice(s_advices[1], Rotation::prev());

            let one_rlp_byte_s = s1.clone() * s2.clone();
            let two_rlp_bytes_s = s1.clone() * (one.clone() - s2.clone());
            let three_rlp_bytes_s = (one.clone() - s1.clone()) * s2.clone();

            let one_rlp_byte_c = c1.clone() * c2.clone();
            let two_rlp_bytes_c = c1.clone() * (one.clone() - c2.clone());
            let three_rlp_bytes_c = (one.clone() - c1.clone()) * c2.clone();

            let rlp_byte0_s =
                meta.query_advice(s_advices[BRANCH_0_S_START - RLP_NUM], Rotation::prev());
            let rlp_byte1_s =
                meta.query_advice(s_advices[BRANCH_0_S_START - RLP_NUM + 1], Rotation::prev());
            let rlp_byte2_s =
                meta.query_advice(s_advices[BRANCH_0_S_START - RLP_NUM + 2], Rotation::prev());

            let rlp_byte0_c =
                meta.query_advice(s_advices[BRANCH_0_C_START - RLP_NUM], Rotation::prev());
            let rlp_byte1_c =
                meta.query_advice(s_advices[BRANCH_0_C_START - RLP_NUM + 1], Rotation::prev());
            let rlp_byte2_c =
                meta.query_advice(s_advices[BRANCH_0_C_START - RLP_NUM + 2], Rotation::prev());

            let one = Expression::Constant(F::one());
            let c32 = Expression::Constant(F::from(32_u64));
            let c192 = Expression::Constant(F::from(192_u64));
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

            let is_node_hashed_s = meta.query_advice(is_node_hashed_s, Rotation::cur());
            let is_node_hashed_c = meta.query_advice(is_node_hashed_c, Rotation::cur());

            // The following value can be either 1 or 33 (if hashed node),
            // depending on whether it's empty or non-empty row.
            let mut bytes_num_in_row_s = s_rlp2_cur.clone() * c160_inv.clone() * c32.clone() + one.clone();
            let mut bytes_num_in_row_c = c_rlp2_cur.clone() * c160_inv * c32 + one.clone();

            bytes_num_in_row_s = is_node_hashed_s.clone() * (s_rlp2_cur.clone() - c192.clone() + one.clone())
                + (one.clone() - is_node_hashed_s.clone()) * bytes_num_in_row_s.clone();
            bytes_num_in_row_c = is_node_hashed_c.clone() * (c_rlp2_cur.clone() - c192.clone() + one.clone())
                + (one.clone() - is_node_hashed_c.clone()) * bytes_num_in_row_c.clone();

            // One RLP byte:
            // [1,1,1,1,217,0,0,217,0,0,1,...
            // Two RLP bytes:
            // [1,0,1,0,248,81,0,248,81,0,3,0,0,0,...
            // Three RLP bytes:
            // [0,1,0,1,249,2,17,249,2,17,7,0,0,0,...

            // Note: s_rlp1 stores the number of the remaining bytes in the branch. If there
            // are 81 bytes in the branch, and the first branch children contains 33 bytes,
            // then s_rlp1 in this row will have s_rlp1 = 81 - 33.

            // is_branch_child with node_index = 0
            // rlp_byte1_s stores the number of bytes in the branch (81 in the example with two RLP bytes)

            constraints.push((
                "first branch children one RLP meta byte S",
                q_not_first.clone()
                    * is_branch_init_prev.clone()
                    * one_rlp_byte_s
                    * (rlp_byte0_s.clone() - c192.clone() - bytes_num_in_row_s.clone() - s_rlp1_cur.clone()),
            ));
            constraints.push((
                "first branch children one RLP meta byte C",
                q_not_first.clone()
                    * is_branch_init_prev.clone()
                    * one_rlp_byte_c
                    * (rlp_byte0_c.clone() - c192.clone() - bytes_num_in_row_c.clone() - c_rlp1_cur.clone()),
            ));

            constraints.push((
                "first branch children two RLP meta bytes S",
                q_not_first.clone()
                    * is_branch_init_prev.clone()
                    * two_rlp_bytes_s
                    * (rlp_byte1_s.clone() - bytes_num_in_row_s.clone() - s_rlp1_cur.clone()),
            ));
            constraints.push((
                "first branch children two RLP meta bytes C",
                q_not_first.clone()
                    * is_branch_init_prev.clone()
                    * two_rlp_bytes_c
                    * (rlp_byte1_c.clone() - bytes_num_in_row_c.clone() - c_rlp1_cur.clone()),
            ));

            constraints.push((
                "first branch children three RLP meta bytes S",
                q_not_first.clone()
                    * is_branch_init_prev.clone()
                    * three_rlp_bytes_s
                    * (rlp_byte1_s * c256.clone() + rlp_byte2_s
                        - bytes_num_in_row_s.clone()
                        - s_rlp1_cur.clone()),
            ));
            constraints.push((
                "first branch children three RLP meta bytes C",
                q_not_first.clone()
                    * is_branch_init_prev.clone()
                    * three_rlp_bytes_c
                    * (rlp_byte1_c * c256 + rlp_byte2_c - bytes_num_in_row_c.clone() - c_rlp1_cur.clone()),
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
                    * (s_rlp1_prev - bytes_num_in_row_s.clone() - s_rlp1_cur.clone()),
            ));
            constraints.push((
                "branch children (node_index > 0) C",
                q_not_first.clone()
                    * is_branch_child_cur.clone()
                    * (one.clone() - is_branch_init_prev.clone())
                    * (c_rlp1_prev - bytes_num_in_row_c.clone() - c_rlp1_cur.clone()),
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

            // If we have branch child, we can only have branch child or branch init in the
            // previous row.
            constraints.push((
                "before branch children",
                q_not_first.clone()
                    * is_branch_child_cur.clone()
                    * (is_branch_child_prev.clone() - one.clone())
                    * (is_branch_init_prev.clone() - one.clone()),
            ));

            // If we have is_branch_init in the previous row, we have
            // is_branch_child = 1 in the current row.
            constraints.push((
                "first branch children 1",
                q_not_first.clone()
                    * is_branch_init_prev.clone()
                    * (is_branch_child_cur.clone() - one.clone()), // is_branch_child has to be 1
            ));
            // We could have only one constraint using sum, but then we would need
            // to limit node_index (to prevent values like -1). Now, node_index is
            // limited by ensuring its first value is 0, its last value is 15,
            // and it's increasing by 1.
            // If we have is_branch_init in the previous row, we have
            // node_index = 0 in the current row.
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
                        - is_branch_child_cur.clone()) // is_branch_child changes
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

            // modified_node = drifted_pos when NOT placeholder.
            // We check modified_node = drifted_pos in first branch node and then check
            // in each branch node: modified_node_prev = modified_node_cur and
            // drifted_pos_prev = drifted_pos_cur, this way we can use only Rotation(-1).
            let drifted_pos_prev = meta.query_advice(drifted_pos, Rotation::prev());
            let drifted_pos_cur = meta.query_advice(drifted_pos, Rotation::cur());
            let node_index_cur = meta.query_advice(node_index, Rotation::cur());
            let is_branch_placeholder_s = meta.query_advice(
                s_advices[IS_BRANCH_S_PLACEHOLDER_POS - LAYOUT_OFFSET],
                Rotation::prev(),
            );
            let is_branch_placeholder_c = meta.query_advice(
                s_advices[IS_BRANCH_C_PLACEHOLDER_POS - LAYOUT_OFFSET],
                Rotation::prev(),
            );
            constraints.push((
                "drifted_pos = modified_node in node_index = 0 when NOT placeholder",
                q_not_first.clone()
                    * (one.clone()
                        - is_branch_placeholder_s.clone()
                        - is_branch_placeholder_c.clone())
                    * is_branch_init_prev
                    * (drifted_pos_cur.clone() - modified_node_cur.clone()),
            ));
            constraints.push((
                "drifted_pos_prev = drifted_pos_cur in node_index > 0 when NOT placeholder",
                q_not_first.clone()
                    * (one.clone()
                        - is_branch_placeholder_s.clone()
                        - is_branch_placeholder_c.clone())
                    * node_index_cur.clone() // ignore if node_index = 0
                    * (drifted_pos_prev.clone() - drifted_pos_cur.clone()),
            ));
            // Constraint for modified_node being the same for all branch nodes is above.

            let is_branch_child_cur = meta.query_advice(is_branch_child, Rotation::cur());
            let is_modified = meta.query_advice(is_modified, Rotation::cur());
            let is_at_drifted_pos = meta.query_advice(is_at_drifted_pos, Rotation::cur());
            let drifted_pos = meta.query_advice(drifted_pos, Rotation::cur());
            // is_modified is:
            //   0 when node_index_cur != modified_node
            //   1 when node_index_cur == modified_node (it's checked in selectors.rs for
            // booleanity)
            constraints.push((
                "is_modified",
                q_not_first.clone()
                    * is_branch_child_cur.clone()
                    * is_modified.clone()
                    * (node_index_cur.clone() - modified_node_cur.clone()),
            ));

            // is_at_drifted_pos is:
            //   0 when node_index_cur != drifted_pos
            //   1 when node_index_cur == drifted_pos (it's checked in selectors.rs for
            // booleanity)
            constraints.push((
                "is_at_drifted pos",
                q_not_first.clone()
                    * is_branch_child_cur.clone()
                    * is_at_drifted_pos.clone()
                    * (node_index_cur.clone() - drifted_pos.clone()),
            ));

            constraints
        });

        meta.create_gate("branch placeholder selectors", |meta| {
            // Not merged with gate above because this needs to be checked in the first row
            // too and we need to avoid rotation -1.
            let mut constraints = vec![];
            let is_branch_init_cur = meta.query_advice(is_branch_init, Rotation::cur());

            let is_branch_placeholder_s = meta.query_advice(
                s_advices[IS_BRANCH_S_PLACEHOLDER_POS - LAYOUT_OFFSET],
                Rotation::cur(),
            );
            let is_branch_placeholder_c = meta.query_advice(
                s_advices[IS_BRANCH_C_PLACEHOLDER_POS - LAYOUT_OFFSET],
                Rotation::cur(),
            );
            let q_enable = meta.query_fixed(q_enable, Rotation::cur());
            constraints.push((
                "bool check branch is_branch_placeholder_s",
                get_bool_constraint(
                    q_enable.clone() * is_branch_init_cur.clone(),
                    is_branch_placeholder_s.clone(),
                ),
            ));
            constraints.push((
                "bool check branch is_branch_placeholder_c",
                get_bool_constraint(
                    q_enable.clone() * is_branch_init_cur,
                    is_branch_placeholder_c.clone(),
                ),
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
