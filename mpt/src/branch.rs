pub mod branch_hash_in_parent;
pub mod branch_key;
pub mod branch_parallel;
pub mod branch_rlc;
pub mod branch_init;
pub mod extension_node;
pub mod extension_node_key;

use halo2_proofs::{
    plonk::{Column, ConstraintSystem, Error, Expression, Fixed, VirtualCells, Advice},
    poly::Rotation, circuit::Region,
};
use pairing::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::{
    helpers::{get_bool_constraint, range_lookups, get_is_extension_node, bytes_into_rlc},
    mpt::{FixedTableTag, MainCols, BranchCols, DenoteCols, MPTConfig, ProofVariables},
    param::{
        BRANCH_0_C_START, BRANCH_0_S_START, IS_BRANCH_C_PLACEHOLDER_POS,
        IS_BRANCH_S_PLACEHOLDER_POS, RLP_NUM, NIBBLES_COUNTER_POS, BRANCH_ROWS_NUM, BRANCH_0_KEY_POS, DRIFTED_POS, IS_EXT_LONG_EVEN_C16_POS, IS_EXT_LONG_EVEN_C1_POS, IS_EXT_LONG_ODD_C16_POS, IS_EXT_LONG_ODD_C1_POS, IS_EXT_SHORT_C16_POS, IS_EXT_SHORT_C1_POS, S_RLP_START, S_START, C_RLP_START, C_START, HASH_WIDTH,
    }, witness_row::MptWitnessRow, storage_leaf::StorageLeaf, account_leaf::AccountLeaf,
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

[1 0 1 0 248 241 0 248 241 0 1 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0]
[0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1]
[0 160 164 92 78 34 81 137 173 236 78 208 145 118 128 60 46 5 176 8 229 165 42 222 110 4 252 228 93 243 26 160 241 85 0 160 95 174 59 239 229 74 221 53 227 115 207 137 94 29 119 126 56 209 55 198 212 179 38 213 219 36 111 62 46 43 176 168 1]
[0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1]
[0 160 60 157 212 182 167 69 206 32 151 2 14 23 149 67 58 187 84 249 195 159 106 68 203 199 199 65 194 33 215 102 71 138 0 160 60 157 212 182 167 69 206 32 151 2 14 23 149 67 58 187 84 249 195 159 106 68 203 199 199 65 194 33 215 102 71 138 1]
[0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1]
[0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1]
[0 160 21 230 18 20 253 84 192 151 178 53 157 0 9 105 229 121 222 71 120 109 159 109 9 218 254 1 50 139 117 216 194 252 0 160 21 230 18 20 253 84 192 151 178 53 157 0 9 105 229 121 222 71 120 109 159 109 9 218 254 1 50 139 117 216 194 252 1]
[0 160 229 29 220 149 183 173 68 40 11 103 39 76 251 20 162 242 21 49 103 245 160 99 143 218 74 196 2 61 51 34 105 123 0 160 229 29 220 149 183 173 68 40 11 103 39 76 251 20 162 242 21 49 103 245 160 99 143 218 74 196 2 61 51 34 105 123 1]
[0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1]
[0 160 0 140 67 252 58 164 68 143 34 163 138 133 54 27 218 38 80 20 142 115 221 100 73 161 165 75 83 53 8 58 236 1 0 160 0 140 67 252 58 164 68 143 34 163 138 133 54 27 218 38 80 20 142 115 221 100 73 161 165 75 83 53 8 58 236 1 1]
[0 160 149 169 206 0 129 86 168 48 42 127 100 73 109 90 171 56 216 28 132 44 167 14 46 189 224 213 37 0 234 165 140 236 0 160 149 169 206 0 129 86 168 48 42 127 100 73 109 90 171 56 216 28 132 44 167 14 46 189 224 213 37 0 234 165 140 236 1]
[0 160 42 63 45 28 165 209 201 220 231 99 153 208 48 174 250 66 196 18 123 250 55 107 64 178 159 49 190 84 159 179 138 235 0 160 42 63 45 28 165 209 201 220 231 99 153 208 48 174 250 66 196 18 123 250 55 107 64 178 159 49 190 84 159 179 138 235 1]
[0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1]
[0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1]
[0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1]
[0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1]
[0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 16]
[0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 17]

Note that when `BRANCH.IS_CHILD` row presents a nil node, there is only one byte non-zero:
128 at `s_main.bytes[0] / c_main.bytes[0]`.
*/

#[derive(Default)]
pub(crate) struct Branch {
    pub(crate) is_branch_init: bool,
    pub(crate) is_branch_child: bool,
    pub(crate) is_last_branch_child: bool,
    pub(crate) node_index: u8,
    pub(crate) is_modified: bool, 
    pub(crate) modified_node: u8,
    pub(crate) is_at_drifted_pos: bool,
    pub(crate) drifted_pos: u8,
    pub(crate) is_extension_node_s: bool,
    pub(crate) is_extension_node_c: bool,
}

#[derive(Clone, Debug)]
pub(crate) struct BranchConfig<F> {
    _marker: PhantomData<F>,
}

impl<F: FieldExt> BranchConfig<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: Column<Fixed>,
        q_not_first: Column<Fixed>,
        not_first_level: Column<Advice>,
        is_account_leaf_in_added_branch: Column<Advice>,
        s_main: MainCols,
        c_main: MainCols,
        branch: BranchCols,
        denoter: DenoteCols,
        fixed_table: [Column<Fixed>; 3],
    ) -> Self {
        let config = BranchConfig { _marker: PhantomData };
        let one = Expression::Constant(F::one());
        let c320 = Expression::Constant(F::from(320));

        /*
        The gate `Branch S and C equal at NON modified_node position` ensures that the only change in
        `S` and `C` proof occur at `modified_node` (denoting which child of the branch is changed) position.
        This is needed because the circuit allows only one change at at time.
        */
        meta.create_gate(
            "Branch S and C equal at NON modified_node position & only two non-nil nodes when placeholder",
            |meta| {
                let q_enable = meta.query_fixed(q_enable, Rotation::cur());
                let mut constraints = vec![];

                let is_branch_child_cur = meta.query_advice(branch.is_child, Rotation::cur());
                let node_index_cur = meta.query_advice(branch.node_index, Rotation::cur());
                let modified_node = meta.query_advice(branch.modified_node, Rotation::cur());

                let s_rlp2 = meta.query_advice(s_main.rlp2, Rotation::cur());
                let c_rlp2 = meta.query_advice(c_main.rlp2, Rotation::cur());

                /*
                We check `s_main.rlp2 = c_main.rlp2` everywhere except at `modified_node`.

                Note: We do not compare `s_main.rlp1 = c_main.rlp1` because there is no information
                about branch. We use `rlp1` to store information about `S` branch and
                `C` branch RLP length (see the gate below).
                */
                constraints.push((
                    "rlp2",
                    q_enable.clone()
                        * is_branch_child_cur.clone()
                        * (s_rlp2 - c_rlp2)
                        * (node_index_cur.clone() - modified_node.clone()),
                ));

                for (ind, col) in s_main.bytes.iter().enumerate() {
                    let s = meta.query_advice(*col, Rotation::cur());
                    let c = meta.query_advice(c_main.bytes[ind], Rotation::cur());

                    /*
                    Similarly as above for `rlp2` we check here that `s_main.bytes[i] = c_main.bytes[i]`
                    except at `modified_node`.
                    */
                    constraints.push((
                        "s = c when NOT is_modified",
                        q_enable.clone()
                            * is_branch_child_cur.clone()
                            * (s.clone() - c.clone())
                            * (node_index_cur.clone() - modified_node.clone()),
                    ));
                }

                let mut sum_rlp2_s = Expression::Constant(F::zero());
                let mut sum_rlp2_c = Expression::Constant(F::zero());
                /*
                So many rotation is not optimal, but most of these rotations are used elsewhere, so
                it should not be much of an overhead. Alternative approach would be to have a column
                specifying whether there is a placeholder branch or not (we currently have this info
                only in branch init). Another alternative would be to have a column where we add
                `rlp2` value from the current row in each of the 16 rows. Both alternative would
                require additional column.
                */
                for ind in 0..16 {
                    let s_rlp2 = meta.query_advice(s_main.rlp2, Rotation(-ind));
                    let c_rlp2 = meta.query_advice(c_main.rlp2, Rotation(-ind)); 
                    sum_rlp2_s = sum_rlp2_s.clone() + s_rlp2;
                    sum_rlp2_c = sum_rlp2_c.clone() + c_rlp2;
                }
 
                let is_last_child = meta.query_advice(branch.is_last_child, Rotation::cur());
                let is_branch_placeholder_s =
                    meta.query_advice(s_main.bytes[IS_BRANCH_S_PLACEHOLDER_POS - RLP_NUM], Rotation(-16));
                let is_branch_placeholder_c =
                    meta.query_advice(s_main.bytes[IS_BRANCH_C_PLACEHOLDER_POS - RLP_NUM], Rotation(-16));

                /*
                This constraint applies for when we have a placeholder branch.
                In this case, both branches are the same - the placeholder branch and its
                parallel counterpart, which is not a placeholder, but a regular branch (newly added branch).
                The regular branch has only two non-nil nodes, because the placeholder branch
                appears only when an existing leaf drifts down into a newly added branch.
                Besides an existing leaf, we have a leaf that was being added and that caused
                a new branch to be added. So we need to check that there are exactly two non-nil nodes
                (otherwise the attacker could add two or more new leaves at the same time).

                The non-nil nodes need to be at `is_modified` and `is_at_drifted_pos`, elsewhere
                there have to be zeros. When there is no placeholder branch, this constraint is ignored.
                */
                constraints.push((
                    "Only two nil-nodes when placeholder branch S",
                    q_enable.clone()
                    * is_last_child.clone()
                    * is_branch_placeholder_c.clone() // C is correct here
                    * (sum_rlp2_s - c320.clone()) // There are constraints which ensure there is only 0 or 160 at rlp2 for branch children.
                ));
                constraints.push((
                    "Only two nil-nodes when placeholder branch C",
                    q_enable.clone()
                    * is_last_child.clone()
                    * is_branch_placeholder_s // S is correct here
                    * (sum_rlp2_c - c320)
                ));

                constraints
            },
        );

        /*
        We need to check that the length of the branch corresponds to the bytes at the beginning of
        the RLP stream that specify the length of the RLP stream. There are three possible scenarios:

        Branch (length 21 = 213 - 192) with one byte of RLP meta data
        [213,128,194,32,1,128,194,32,1,128,128,128,128,128,128,128,128,128,128,128,128,128]

        Branch (length 83) with two bytes of RLP meta data
        [248,81,128,128,...

        Branch (length 340) with three bytes of RLP meta data
        [249,1,81,128,16,...

        For which 
        */
        meta.create_gate("RLP length", |meta| {
            let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
            let mut constraints = vec![];

            let is_branch_init_prev = meta.query_advice(branch.is_init, Rotation::prev());
            /*
            rlp1, rlp2: 1, 1 means 1 RLP byte
            rlp1, rlp2: 1, 0 means 2 RLP bytes
            rlp1, rlp2: 0, 1 means 3 RLP bytes
            */

            let s1 = meta.query_advice(s_main.rlp1, Rotation::prev());
            let s2 = meta.query_advice(s_main.rlp2, Rotation::prev());
            let c1 = meta.query_advice(s_main.bytes[0], Rotation::prev());
            let c2 = meta.query_advice(s_main.bytes[1], Rotation::prev());

            // There should never be:
            // rlp1, rlp2: 0, 0
            constraints.push((
                "not both zeros: rlp1, rlp2",
                q_not_first.clone()
                    * is_branch_init_prev.clone()
                    * (one.clone() - s1.clone())
                    * (one.clone() - s2.clone()),
            ));
            // There should never be:
            // s_advices[0], s_advices[1]: 0, 0
            constraints.push((
                "not both zeros: s_advices[0], s_advices[1]",
                q_not_first.clone()
                    * is_branch_init_prev.clone()
                    * (one.clone() - c1.clone())
                    * (one.clone() - c2.clone()),
            ));

            let one_rlp_byte_s = s1.clone() * s2.clone();
            let two_rlp_bytes_s = s1.clone() * (one.clone() - s2.clone());
            let three_rlp_bytes_s = (one.clone() - s1.clone()) * s2.clone();

            let one_rlp_byte_c = c1.clone() * c2.clone();
            let two_rlp_bytes_c = c1.clone() * (one.clone() - c2.clone());
            let three_rlp_bytes_c = (one.clone() - c1.clone()) * c2.clone();

            let rlp_byte0_s =
                meta.query_advice(s_main.bytes[BRANCH_0_S_START - RLP_NUM], Rotation::prev());
            let rlp_byte1_s =
                meta.query_advice(s_main.bytes[BRANCH_0_S_START - RLP_NUM + 1], Rotation::prev());
            let rlp_byte2_s =
                meta.query_advice(s_main.bytes[BRANCH_0_S_START - RLP_NUM + 2], Rotation::prev());

            let rlp_byte0_c =
                meta.query_advice(s_main.bytes[BRANCH_0_C_START - RLP_NUM], Rotation::prev());
            let rlp_byte1_c =
                meta.query_advice(s_main.bytes[BRANCH_0_C_START - RLP_NUM + 1], Rotation::prev());
            let rlp_byte2_c =
                meta.query_advice(s_main.bytes[BRANCH_0_C_START - RLP_NUM + 2], Rotation::prev());

            let one = Expression::Constant(F::one());
            let c32 = Expression::Constant(F::from(32_u64));
            let c192 = Expression::Constant(F::from(192_u64));
            let c256 = Expression::Constant(F::from(256_u64));
            let c160_inv = Expression::Constant(F::from(160_u64).invert().unwrap());

            let s_rlp1_cur = meta.query_advice(s_main.rlp1, Rotation::cur());
            let s_rlp2_cur = meta.query_advice(s_main.rlp2, Rotation::cur());
            let c_rlp1_cur = meta.query_advice(c_main.rlp1, Rotation::cur());
            let c_rlp2_cur = meta.query_advice(c_main.rlp2, Rotation::cur());
            let s_advices0_cur = meta.query_advice(s_main.bytes[0], Rotation::cur());
            let c_advices0_cur = meta.query_advice(c_main.bytes[0], Rotation::cur());

            // s bytes in this row:
            // If empty, then s_rlp2 = 0:
            // s_rlp2 * c160_inv * c32 + 1 = 1
            // If non-empty, then s_rlp2 = 160:
            // s_rlp2 * c160_inv * c32 + 1 = 33

            let is_node_hashed_s = meta.query_advice(denoter.is_node_hashed_s, Rotation::cur());
            let is_node_hashed_c = meta.query_advice(denoter.is_node_hashed_c, Rotation::cur());

            // The following value can be either 1 or 33 (if hashed node),
            // depending on whether it's empty or non-empty row.
            let mut bytes_num_in_row_s = s_rlp2_cur.clone() * c160_inv.clone() * c32.clone() + one.clone();
            let mut bytes_num_in_row_c = c_rlp2_cur.clone() * c160_inv * c32 + one.clone();

            bytes_num_in_row_s = is_node_hashed_s.clone() * (s_advices0_cur.clone() - c192.clone() + one.clone())
                + (one.clone() - is_node_hashed_s.clone()) * bytes_num_in_row_s.clone();
            bytes_num_in_row_c = is_node_hashed_c.clone() * (c_advices0_cur.clone() - c192.clone() + one.clone())
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
            let is_branch_child_cur = meta.query_advice(branch.is_child, Rotation::cur());
            let s_rlp1_prev = meta.query_advice(s_main.rlp1, Rotation::prev());
            let c_rlp1_prev = meta.query_advice(c_main.rlp1, Rotation::prev());
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
            let is_last_branch_child = meta.query_advice(branch.is_last_child, Rotation::cur());
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
            let is_branch_child_prev = meta.query_advice(branch.is_child, Rotation::prev());
            let is_branch_child_cur = meta.query_advice(branch.is_child, Rotation::cur());
            let is_branch_init_prev = meta.query_advice(branch.is_init, Rotation::prev());
            let is_last_branch_child_prev =
                meta.query_advice(branch.is_last_child, Rotation::prev());
            let is_last_branch_child_cur = meta.query_advice(branch.is_last_child, Rotation::cur());

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
            let node_index_cur = meta.query_advice(branch.node_index, Rotation::cur());
            constraints.push((
                "first branch children 2",
                q_not_first.clone()
                    * is_branch_init_prev.clone()
                    * node_index_cur.clone(), // node_index has to be 0
            ));

            // When is_branch_child changes back to 0, previous node_index has to be 15.
            let node_index_prev = meta.query_advice(branch.node_index, Rotation::prev());
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
            let node_index_prev = meta.query_advice(branch.node_index, Rotation::prev());
            constraints.push((
                "node index increasing for branch children",
                q_not_first.clone()
                    * is_branch_child_cur.clone()
                    * node_index_cur.clone() // ignore if node_index = 0
                    * (node_index_cur.clone() - node_index_prev - one.clone()),
            ));

            // modified_node needs to be the same for all branch nodes
            let modified_node_prev = meta.query_advice(branch.modified_node, Rotation::prev());
            let modified_node_cur = meta.query_advice(branch.modified_node, Rotation::cur());
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
            let drifted_pos_prev = meta.query_advice(branch.drifted_pos, Rotation::prev());
            let drifted_pos_cur = meta.query_advice(branch.drifted_pos, Rotation::cur());
            let node_index_cur = meta.query_advice(branch.node_index, Rotation::cur());
            let is_branch_placeholder_s = meta.query_advice(
                s_main.bytes[IS_BRANCH_S_PLACEHOLDER_POS - RLP_NUM],
                Rotation::prev(),
            );
            let is_branch_placeholder_c = meta.query_advice(
                s_main.bytes[IS_BRANCH_C_PLACEHOLDER_POS - RLP_NUM],
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

            let is_branch_child_cur = meta.query_advice(branch.is_child, Rotation::cur());
            let is_modified = meta.query_advice(branch.is_modified, Rotation::cur());
            let is_at_drifted_pos = meta.query_advice(branch.is_at_drifted_pos, Rotation::cur());
            let drifted_pos = meta.query_advice(branch.drifted_pos, Rotation::cur());
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
            let is_branch_init_cur = meta.query_advice(branch.is_init, Rotation::cur());

            let is_branch_placeholder_s = meta.query_advice(
                s_main.bytes[IS_BRANCH_S_PLACEHOLDER_POS - RLP_NUM],
                Rotation::cur(),
            );
            let is_branch_placeholder_c = meta.query_advice(
                s_main.bytes[IS_BRANCH_C_PLACEHOLDER_POS - RLP_NUM],
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

        // TODO: reset to 0 after account leaf
        meta.create_gate("Branch number of nibbles (not first level)", |meta| {
            let mut constraints = vec![];
            let q_enable = meta.query_fixed(q_enable, Rotation::cur());
            let not_first_level = meta.query_advice(not_first_level, Rotation::cur());
            let is_branch_init_cur = meta.query_advice(branch.is_init, Rotation::cur());
            let is_extension_node = get_is_extension_node(meta, s_main.bytes, 0);

            // Only check if there is an account above the branch.
            let is_account_leaf_in_added_branch = meta.query_advice(
                is_account_leaf_in_added_branch,
                Rotation(-1),
            );

            let nibbles_count_cur = meta.query_advice(
                s_main.bytes[NIBBLES_COUNTER_POS - RLP_NUM],
                Rotation::cur(),
            );
            let nibbles_count_prev = meta.query_advice(
                s_main.bytes[NIBBLES_COUNTER_POS - RLP_NUM],
                Rotation(- BRANCH_ROWS_NUM),
            );

            constraints.push((
                "nibbles_count",
                q_enable.clone()
                    * is_branch_init_cur.clone()
                    * (one.clone() - is_extension_node.clone()) // extension node counterpart constraint is in extension_node.rs
                    * (one.clone() - is_account_leaf_in_added_branch)
                    * not_first_level.clone()
                    * (nibbles_count_cur.clone() - nibbles_count_prev.clone() - one.clone()),
            ));

            constraints
        });

        meta.create_gate("Branch number of nibbles (first level)", |meta| {
            let mut constraints = vec![];
            let q_enable = meta.query_fixed(q_enable, Rotation::cur());
            let not_first_level = meta.query_advice(not_first_level, Rotation::cur());
            let is_branch_init_cur = meta.query_advice(branch.is_init, Rotation::cur());
            let is_extension_node = get_is_extension_node(meta, s_main.bytes, 0);

            // Only check if there is an account above the branch.
            let is_account_leaf_in_added_branch = meta.query_advice(
                is_account_leaf_in_added_branch,
                Rotation(-1),
            );

            let nibbles_count_cur = meta.query_advice(
                s_main.bytes[NIBBLES_COUNTER_POS - RLP_NUM],
                Rotation::cur(),
            );

            constraints.push((
                "nibbles_count first level account",
                q_enable.clone()
                    * is_branch_init_cur.clone()
                    * (one.clone() - is_extension_node.clone()) // extension node counterpart constraint is in extension_node.rs
                    * (one.clone() - not_first_level.clone())
                    * (nibbles_count_cur.clone() - one.clone()),
            ));

            constraints.push((
                "nibbles_count first level storage",
                q_enable.clone()
                    * is_branch_init_cur.clone()
                    * (one.clone() - is_extension_node.clone()) // extension node counterpart constraint is in extension_node.rs
                    * is_account_leaf_in_added_branch
                    * (nibbles_count_cur.clone() - one.clone()),
            ));

            constraints
        });
        
        /*
        Range lookups ensure that `s_main.bytes` and `c_main.bytes` columns are all bytes (between 0 - 255).

        Note: We do not check this for branch init row here.
        Branch init row contains selectors related to drifted_pos,
        modified_node, branch placeholders, extension node selectors. The constraints for these
        selectors are in `branch_init.rs`.
        Range lookups for extension node rows are in `extension_node_key.rs`.
        */
        let sel = |meta: &mut VirtualCells<F>| {
            let q_not_first = meta.query_fixed(q_not_first, Rotation::cur());
            let is_branch_init = meta.query_advice(branch.is_init, Rotation::cur());
            let is_branch_child = meta.query_advice(branch.is_child, Rotation::cur());

            q_not_first * (one.clone() - is_branch_init) * is_branch_child
        }; 
        range_lookups(
            meta,
            sel,
            s_main.bytes.to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );
        range_lookups(
            meta,
            sel,
            c_main.bytes.to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );

        config
    }

    pub(crate) fn assign_branch_init(
        &self,
        region: &mut Region<'_, F>,
        witness: &[MptWitnessRow<F>],
        mpt_config: &MPTConfig<F>,
        pv: &mut ProofVariables<F>,
        offset: usize,
    ) -> Result<(), Error> {
        let row = &witness[offset];

        pv.modified_node = row.get_byte(BRANCH_0_KEY_POS);
        pv.node_index = 0;
        pv.drifted_pos = row.get_byte(DRIFTED_POS);

        // Get the child that is being changed and convert it to words to enable
        // lookups:
        let mut s_hash = witness[offset + 1 + pv.modified_node as usize].s_hash_bytes().to_vec();
        let mut c_hash = witness[offset + 1 + pv.modified_node as usize].c_hash_bytes().to_vec();
        pv.s_mod_node_hash_rlc = bytes_into_rlc(&s_hash, mpt_config.acc_r);
        pv.c_mod_node_hash_rlc = bytes_into_rlc(&c_hash, mpt_config.acc_r);

        if row.get_byte(IS_BRANCH_S_PLACEHOLDER_POS) == 1 {
            // We put hash of a node that moved down to the added branch.
            // This is needed to check the hash of leaf_in_added_branch.
            s_hash = witness[offset + 1 + pv.drifted_pos as usize].s_hash_bytes().to_vec();
            pv.s_mod_node_hash_rlc = bytes_into_rlc(&s_hash, mpt_config.acc_r);
            pv.is_branch_s_placeholder = true
        } else {
            pv.is_branch_s_placeholder = false
        }
        if row.get_byte(IS_BRANCH_C_PLACEHOLDER_POS) == 1 {
            c_hash = witness[offset + 1 + pv.drifted_pos as usize].c_hash_bytes().to_vec();
            pv.c_mod_node_hash_rlc = bytes_into_rlc(&c_hash, mpt_config.acc_r);
            pv.is_branch_c_placeholder = true
        } else {
            pv.is_branch_c_placeholder = false
        }
        // If no placeholder branch, we set drifted_pos = modified_node. This
        // is needed just to make some other constraints (s_mod_node_hash_rlc
        // and c_mod_node_hash_rlc correspond to the proper node) easier to
        // write.
        if row.get_byte(IS_BRANCH_S_PLACEHOLDER_POS) == 0
            && row.get_byte(IS_BRANCH_C_PLACEHOLDER_POS) == 0
        {
            pv.drifted_pos = pv.modified_node
        }

        let account_leaf = AccountLeaf::default();
        let storage_leaf = StorageLeaf::default();
        let mut branch = Branch::default();
        branch.is_branch_init = true;

        row.assign(
            region,
            mpt_config,
            account_leaf,
            storage_leaf, 
            branch,
            offset,
        )?;

        // reassign (it was assigned to 0 in assign_row) branch_acc and
        // branch_mult to proper values

        // Branch (length 83) with two bytes of RLP meta data
        // [248,81,128,128,...

        // Branch (length 340) with three bytes of RLP meta data
        // [249,1,81,128,16,...

        let s_len = [0, 1, 2].map(|i| row.get_byte(BRANCH_0_S_START + i) as u64);
        pv.acc_s = F::from(s_len[0]);
        pv.acc_mult_s = mpt_config.acc_r;

        if s_len[0] == 249 {
            pv.acc_s += F::from(s_len[1]) * pv.acc_mult_s; 
            pv.acc_mult_s *= mpt_config.acc_r;
            pv.acc_s += F::from(s_len[2]) * pv.acc_mult_s;
            pv.acc_mult_s *= mpt_config.acc_r;

            pv.rlp_len_rem_s = s_len[1] as i32 * 256 + s_len[2] as i32;
        } else if s_len[0] == 248 {
            pv.acc_s += F::from(s_len[1]) * pv.acc_mult_s; 
            pv.acc_mult_s *= mpt_config.acc_r;

            pv.rlp_len_rem_s = s_len[1] as i32;
        } else {
            pv.rlp_len_rem_s = s_len[0] as i32 - 192;
        }

        let c_len = [0, 1, 2].map(|i| row.get_byte(BRANCH_0_C_START + i) as u64);
        pv.acc_c = F::from(c_len[0]);
        pv.acc_mult_c = mpt_config.acc_r;

        if c_len[0] == 249 {
            pv.acc_c += F::from(c_len[1]) * pv.acc_mult_c;
            pv.acc_mult_c *= mpt_config.acc_r;
            pv.acc_c += F::from(c_len[2]) * pv.acc_mult_c;
            pv.acc_mult_c *= mpt_config.acc_r;

            pv.rlp_len_rem_c = c_len[1] as i32 * 256 + c_len[2] as i32;
        } else if c_len[0] == 248 {
            pv.acc_c += F::from(c_len[1]) * pv.acc_mult_c;
            pv.acc_mult_c *= mpt_config.acc_r;

            pv.rlp_len_rem_c = c_len[1] as i32;
        } else {
            pv.rlp_len_rem_c = c_len[0] as i32 - 192;
        }

        mpt_config.assign_acc(
            region,
            pv.acc_s,
            pv.acc_mult_s,
            pv.acc_c,
            pv.acc_mult_c,
            offset,
        )?;

        pv.is_even = row.get_byte(IS_EXT_LONG_EVEN_C16_POS)
            + row.get_byte(IS_EXT_LONG_EVEN_C1_POS)
            == 1;
        pv.is_odd = row.get_byte(IS_EXT_LONG_ODD_C16_POS)
            + row.get_byte(IS_EXT_LONG_ODD_C1_POS)
            + row.get_byte(IS_EXT_SHORT_C16_POS)
            + row.get_byte(IS_EXT_SHORT_C1_POS)
            == 1;
        pv.is_short = row.get_byte(IS_EXT_SHORT_C16_POS)
            + row.get_byte(IS_EXT_SHORT_C1_POS)
            == 1;
        pv.is_long = row.get_byte(IS_EXT_LONG_EVEN_C16_POS)
            + row.get_byte(IS_EXT_LONG_EVEN_C1_POS)
            + row.get_byte(IS_EXT_LONG_ODD_C16_POS)
            + row.get_byte(IS_EXT_LONG_ODD_C1_POS)
            == 1;
        pv.is_extension_node = pv.is_even == true || pv.is_odd == true;
 
        // Assign how many nibbles have been used in the previous extension node + branch.
        pv.nibbles_num = pv.nibbles_num + 1; // one nibble is used for position in branch
        if pv.is_extension_node {
            // Get into extension node S
            let row_ext = &witness[offset + BRANCH_ROWS_NUM as usize - 2];
            let ext_nibbles: usize;
            if row_ext.get_byte(1) <= 32 {
                ext_nibbles = 1
            } else if row_ext.get_byte(0) < 248 {
                if row_ext.get_byte(2) == 0 { // even number of nibbles
                    ext_nibbles = ((row_ext.get_byte(1) - 128) as usize - 1) * 2;
                } else {
                    ext_nibbles = (row_ext.get_byte(1) - 128) as usize * 2 - 1;
                }
            } else {
                if row_ext.get_byte(3) == 0 { // even number of nibbles
                    ext_nibbles = ((row_ext.get_byte(2) - 128) as usize - 1) * 2;
                } else {
                    ext_nibbles = (row_ext.get_byte(2) - 128) as usize * 2 - 1;
                }
            }

            pv.nibbles_num += ext_nibbles;
        }
        region.assign_advice(
            || "assign number of nibbles".to_string(),
            mpt_config.s_main.bytes[NIBBLES_COUNTER_POS - RLP_NUM],
            offset,
            || Ok(F::from(pv.nibbles_num as u64)),
        )?; 
 
        Ok(())
    }

    pub(crate) fn assign_branch_child(
        &self,
        region: &mut Region<'_, F>,
        witness: &[MptWitnessRow<F>],
        mpt_config: &MPTConfig<F>,
        pv: &mut ProofVariables<F>,
        offset: usize,
    ) -> Result<(), Error> {
        let row = &witness[offset];

        let mut node_mult_diff_s = F::one();
        let mut node_mult_diff_c = F::one();
        
        if row.get_byte(S_RLP_START + 1) == 160 {
            pv.rlp_len_rem_s -= 33;
        } else if row.get_byte(S_RLP_START + 1) == 0 && row.get_byte(S_START) > 192 {
            let len = row.get_byte(S_START) as i32 - 192;
            pv.rlp_len_rem_s -= len + 1;
            for _ in 0..len {
                node_mult_diff_s *= mpt_config.acc_r;
            }
        } else if row.get_byte(S_RLP_START + 1) == 0 {
            pv.rlp_len_rem_s -= 1;
        }
        if row.get_byte(C_RLP_START + 1) == 160 {
            pv.rlp_len_rem_c -= 33;
        } else if row.get_byte(C_RLP_START + 1) == 0 && row.get_byte(C_START) > 192 {
            let len = row.get_byte(C_START) as i32 - 192;
            pv.rlp_len_rem_c -= len + 1;
            for _ in 0..len {
                node_mult_diff_c *= mpt_config.acc_r;
            }
        } else if row.get_byte(C_RLP_START + 1) == 0 {
            pv.rlp_len_rem_c -= 1;
        }

        region.assign_advice(
            || "node_mult_diff_s".to_string(),
            mpt_config.accumulators.node_mult_diff_s,
            offset,
            || Ok(node_mult_diff_s),
        )?;
        region.assign_advice(
            || "node_mult_diff_c".to_string(),
            mpt_config.accumulators.node_mult_diff_c,
            offset,
            || Ok(node_mult_diff_c),
        )?;

        if pv.node_index == 0 {
            // If it's not extension node, rlc and rlc_mult in extension row
            // will be the same as for branch rlc.
            pv.extension_node_rlc = pv.key_rlc;

            pv.key_rlc_prev = pv.key_rlc;
            pv.key_rlc_mult_prev = pv.key_rlc_mult;

            if pv.is_extension_node
            // Extension node
            // We need nibbles here to be able to compute key RLC
            {
                // For key RLC, we need to first take into account
                // extension node key.
                // witness[offset + 16]
                let ext_row = &witness[offset + 16];
                let mut key_len_pos = 1;
                if ext_row.get_byte(0) == 248 {
                    key_len_pos = 2;
                }

                if pv.key_rlc_sel {
                    // Note: it can't be is_even = 1 && is_short = 1.
                    if pv.is_even && pv.is_long {
                        // extension node part:
                        let key_len = ext_row.get_byte(key_len_pos) as usize - 128 - 1; // -1 because the first byte is 0 (is_even)
                        mpt_config.compute_acc_and_mult(
                            &ext_row.bytes,
                            &mut pv.extension_node_rlc,
                            &mut pv.key_rlc_mult,
                            key_len_pos + 2, /* first position behind key_len_pos
                                * is 0 (because is_even), we start
                                * with the next one */
                            key_len,
                        );
                        pv.mult_diff = F::one();
                        for _ in 0..key_len {
                            pv.mult_diff *= mpt_config.acc_r;
                        }
                        pv.key_rlc = pv.extension_node_rlc;
                        // branch part:
                        pv.key_rlc += F::from(pv.modified_node as u64)
                            * F::from(16)
                            * pv.key_rlc_mult;
                        // key_rlc_mult stays the same
                        pv.key_rlc_sel = !pv.key_rlc_sel;
                    } else if pv.is_odd && pv.is_long {
                        // extension node part:
                        pv.extension_node_rlc +=
                            F::from((ext_row.get_byte(key_len_pos + 1) - 16) as u64)
                                * F::from(16)
                                * pv.key_rlc_mult;

                        let ext_row_c = &witness[offset + 17];
                        let key_len = ext_row.get_byte(key_len_pos) as usize - 128;

                        pv.mult_diff = F::one();
                        for k in 0..key_len-1 {
                            let second_nibble = ext_row_c.get_byte(S_START + k);
                            let first_nibble =
                                (ext_row.get_byte(key_len_pos + 2 + k) - second_nibble) / 16;
                            assert_eq!(
                                first_nibble * 16 + second_nibble,
                                ext_row.get_byte(key_len_pos + 2 + k),
                            );
                            pv.extension_node_rlc +=
                                F::from(first_nibble as u64) * pv.key_rlc_mult;

                            pv.key_rlc_mult *= mpt_config.acc_r;
                            pv.mult_diff *= mpt_config.acc_r;

                            pv.extension_node_rlc +=
                                F::from(second_nibble as u64)
                                    * F::from(16)
                                    * pv.key_rlc_mult;
                        }

                        pv.key_rlc = pv.extension_node_rlc;
                        // branch part:
                        pv.key_rlc +=
                            F::from(pv.modified_node as u64) * pv.key_rlc_mult;
                        pv.key_rlc_mult *= mpt_config.acc_r;
                    } else if pv.is_short {
                        pv.extension_node_rlc +=
                            F::from((ext_row.get_byte(1) - 16) as u64)
                                * F::from(16)
                                * pv.key_rlc_mult;
                        pv.key_rlc = pv.extension_node_rlc;
                        // branch part:
                        pv.key_rlc +=
                            F::from(pv.modified_node as u64) * pv.key_rlc_mult;
                        pv.key_rlc_mult *= mpt_config.acc_r;
                        pv.mult_diff = mpt_config.acc_r;
                    }
                } else {
                    if pv.is_even && pv.is_long {
                        // extension node part:
                        let ext_row_c = &witness[offset + 17];
                        let key_len = ext_row.get_byte(key_len_pos) as usize - 128 - 1; // -1 because the first byte is 0 (is_even)

                        pv.mult_diff = F::one();
                        for k in 0..key_len {
                            let second_nibble = ext_row_c.get_byte(S_START + k);
                            let first_nibble =
                                (ext_row.get_byte(key_len_pos + 2 + k) - second_nibble) / 16;
                            assert_eq!(
                                first_nibble * 16 + second_nibble,
                                ext_row.get_byte(key_len_pos + 2 + k),
                            );
                            pv.extension_node_rlc +=
                                F::from(first_nibble as u64) * pv.key_rlc_mult;

                            pv.key_rlc_mult *= mpt_config.acc_r;
                            pv.mult_diff *= mpt_config.acc_r;

                            pv.extension_node_rlc += F::from(16)
                                * F::from(second_nibble as u64)
                                * pv.key_rlc_mult;
                        }

                        pv.key_rlc = pv.extension_node_rlc;
                        // branch part:
                        pv.key_rlc +=
                            F::from(pv.modified_node as u64) * pv.key_rlc_mult;
                        pv.key_rlc_mult *= mpt_config.acc_r;
                        pv.key_rlc_sel = !pv.key_rlc_sel;
                    } else if pv.is_odd && pv.is_long {
                        pv.extension_node_rlc +=
                            F::from((ext_row.get_byte(key_len_pos + 1) - 16) as u64) * pv.key_rlc_mult;

                        pv.key_rlc_mult *= mpt_config.acc_r;

                        let key_len = ext_row.get_byte(key_len_pos) as usize - 128;

                        mpt_config.compute_acc_and_mult(
                            &ext_row.bytes,
                            &mut pv.extension_node_rlc,
                            &mut pv.key_rlc_mult,
                            key_len_pos + 2, /* the first position after key_len_pos
                                * is single nibble which is taken into
                                * account above, we start
                                * with fourth */
                            key_len - 1, // one byte is occupied by single nibble
                        );
                        pv.mult_diff = F::one();
                        for _ in 0..key_len {
                            pv.mult_diff *= mpt_config.acc_r;
                        }
                        pv.key_rlc = pv.extension_node_rlc;
                        // branch part:
                        pv.key_rlc += F::from(pv.modified_node as u64)
                            * F::from(16)
                            * pv.key_rlc_mult;
                        // key_rlc_mult stays the same
                    } else if pv.is_short {
                        pv.extension_node_rlc +=
                            F::from((ext_row.get_byte(1) - 16) as u64) * pv.key_rlc_mult;

                        pv.key_rlc = pv.extension_node_rlc;

                        pv.key_rlc_mult *= mpt_config.acc_r;
                        // branch part:
                        pv.key_rlc += F::from(pv.modified_node as u64)
                            * F::from(16)
                            * pv.key_rlc_mult;
                        pv.mult_diff = mpt_config.acc_r;
                    }
                }
            } else {
                if pv.key_rlc_sel {
                    pv.key_rlc += F::from(pv.modified_node as u64)
                        * F::from(16)
                        * pv.key_rlc_mult;
                    // key_rlc_mult stays the same
                } else {
                    pv.key_rlc +=
                        F::from(pv.modified_node as u64) * pv.key_rlc_mult;
                    pv.key_rlc_mult *= mpt_config.acc_r;
                }
                pv.key_rlc_sel = !pv.key_rlc_sel;
            }
            row.assign_branch_row(
                region,
                mpt_config,
                pv.node_index,
                pv.modified_node,
                pv.key_rlc,
                pv.key_rlc_mult,
                pv.mult_diff,
                pv.s_mod_node_hash_rlc,
                pv.c_mod_node_hash_rlc,
                pv.drifted_pos,
                pv.rlp_len_rem_s,
                pv.rlp_len_rem_c,
                offset,
            )?;
        } else {
            // Note that key_rlc and key_rlc_mult are set the same in all
            // branch children to avoid some rotations - constraint for this
            // equality is in extension_node_key.
            row.assign_branch_row(
                region,
                mpt_config,
                pv.node_index,
                pv.modified_node,
                pv.key_rlc,
                pv.key_rlc_mult,
                pv.mult_diff,
                pv.s_mod_node_hash_rlc,
                pv.c_mod_node_hash_rlc,
                pv.drifted_pos,
                pv.rlp_len_rem_s,
                pv.rlp_len_rem_c,
                offset,
            )?;
        }
        // sel1 is to distinguish whether the S node is empty.
        // sel2 is to distinguish whether the C node is empty.
        // Note that 128 comes from the RLP byte denoting empty leaf.
        // Having 128 for *_mod_node_hash_rlc means there is no node at
        // this position in branch - for example,
        // s_mode_node_hash_rlc = 128 and c_words is some other value
        // when new value is added to the trie
        // (as opposed to just updating the value).
        // Note that there is a potential attack if a leaf node
        // is found with hash [128, 0, ..., 0],
        // but the probability is negligible.
        let mut sel1 = F::zero();
        let mut sel2 = F::zero();
        if pv.s_mod_node_hash_rlc == F::from(128 as u64) {
            sel1 = F::one();
        }
        if pv.c_mod_node_hash_rlc == F::from(128 as u64) {
            sel2 = F::one();
        }

        region.assign_advice(
            || "assign sel1".to_string(),
            mpt_config.denoter.sel1,
            offset,
            || Ok(sel1),
        )?;
        region.assign_advice(
            || "assign sel2".to_string(),
            mpt_config.denoter.sel2,
            offset,
            || Ok(sel2),
        )?;

        // reassign (it was assigned to 0 in assign_row) branch_acc and
        // branch_mult to proper values

        // We need to distinguish between empty and non-empty node:
        // empty node at position 1: 0
        // non-empty node at position 1: 160

        let c128 = F::from(128_u64);
        let c160 = F::from(160_u64);

        let compute_branch_acc_and_mult =
            |branch_acc: &mut F,
                branch_mult: &mut F,
                rlp_start: usize,
                start: usize| {
                if row.get_byte(rlp_start + 1) == 0 && row.get_byte(start) == 128 {
                    *branch_acc += c128 * *branch_mult;
                    *branch_mult *= mpt_config.acc_r;
                } else if row.get_byte(rlp_start + 1) == 160 {
                    *branch_acc += c160 * *branch_mult;
                    *branch_mult *= mpt_config.acc_r;
                    for i in 0..HASH_WIDTH {
                        *branch_acc +=
                            F::from(row.get_byte(start + i) as u64) * *branch_mult;
                        *branch_mult *= mpt_config.acc_r;
                    }
                } else {
                    *branch_acc += F::from(row.get_byte(start) as u64) * *branch_mult;
                    *branch_mult *= mpt_config.acc_r;
                    let len = row.get_byte(start) as usize - 192;
                    for i in 0..len {
                        *branch_acc +=
                            F::from(row.get_byte(start + 1 + i) as u64) * *branch_mult;
                        *branch_mult *= mpt_config.acc_r;
                    }
                }
            };

        // TODO: add branch ValueNode info

        compute_branch_acc_and_mult(
            &mut pv.acc_s,
            &mut pv.acc_mult_s,
            S_RLP_START,
            S_START,
        );
        compute_branch_acc_and_mult(
            &mut pv.acc_c,
            &mut pv.acc_mult_c,
            C_RLP_START,
            C_START,
        );
        mpt_config.assign_acc(
            region,
            pv.acc_s,
            pv.acc_mult_s,
            pv.acc_c,
            pv.acc_mult_c,
            offset,
        )?;

        // This is to avoid Poisoned Constraint in extension_node_key.
        region.assign_advice(
            || "assign key_rlc".to_string(),
            mpt_config.accumulators.key.rlc,
            offset,
            || Ok(pv.key_rlc),
        )?;
        region.assign_advice(
            || "assign key_rlc_mult".to_string(),
            mpt_config.accumulators.key.mult,
            offset,
            || Ok(pv.key_rlc_mult),
        )?;

        pv.node_index += 1;

        Ok(())
    }
}