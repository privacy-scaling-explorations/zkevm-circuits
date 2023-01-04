pub mod branch_hash_in_parent;
pub mod branch_init;
pub mod branch_key;
pub mod branch_parallel;
pub mod branch_rlc;
pub mod extension;
pub mod extension_node;
pub mod extension_node_modified;
pub mod extension_node_key;

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Fixed, VirtualCells},
    poly::Rotation,
};
use std::marker::PhantomData;

use crate::{
    mpt_circuit::account_leaf::AccountLeaf,
    mpt_circuit::columns::{AccumulatorCols, DenoteCols, MainCols, PositionCols},
    mpt_circuit::helpers::{
        bytes_expr_into_rlc, bytes_into_rlc, get_bool_constraint, get_is_extension_node,
        range_lookups,
    },
    mpt_circuit::param::{
        BRANCH_0_C_START, BRANCH_0_KEY_POS, BRANCH_0_S_START, BRANCH_ROWS_NUM, C_RLP_START,
        C_START, DRIFTED_POS, HASH_WIDTH, IS_BRANCH_C_PLACEHOLDER_POS, IS_BRANCH_S_PLACEHOLDER_POS,
        IS_C_BRANCH_NON_HASHED_POS, IS_EXT_LONG_EVEN_C16_POS, IS_EXT_LONG_EVEN_C1_POS,
        IS_EXT_LONG_ODD_C16_POS, IS_EXT_LONG_ODD_C1_POS, IS_EXT_SHORT_C16_POS, IS_EXT_SHORT_C1_POS,
        IS_S_BRANCH_NON_HASHED_POS, NIBBLES_COUNTER_POS, RLP_NUM, S_RLP_START, S_START,
    },
    mpt_circuit::storage_leaf::StorageLeaf,
    mpt_circuit::witness_row::MptWitnessRow,
    mpt_circuit::{FixedTableTag, MPTConfig, ProofValues},
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
    pub(crate) modified_node: u8,
    pub(crate) drifted_pos: u8,
    pub(crate) is_extension_node_s: bool,
    pub(crate) is_extension_node_c: bool,
    pub(crate) is_mod_ext_node_s_before_mod: bool,
    pub(crate) is_mod_ext_node_c_before_mod: bool,
    pub(crate) is_mod_ext_node_s_after_mod: bool,
    pub(crate) is_mod_ext_node_c_after_mod: bool,
    pub(crate) is_mod_ext_node_before_mod_selectors: bool,
    pub(crate) is_mod_ext_node_after_mod_selectors: bool,
}

#[derive(Clone, Debug)]
pub(crate) struct BranchCols<F> {
    pub(crate) is_init: Column<Advice>,
    pub(crate) is_child: Column<Advice>,
    pub(crate) is_last_child: Column<Advice>,
    pub(crate) node_index: Column<Advice>,
    pub(crate) is_modified: Column<Advice>, // whether this branch node is modified
    pub(crate) modified_node: Column<Advice>, // index of the modified node
    pub(crate) is_at_drifted_pos: Column<Advice>, // needed when leaf is turned into branch
    pub(crate) drifted_pos: Column<Advice>, /* needed when leaf is turned into branch - first
                                             * nibble of
                                             * the key stored in a leaf (because the existing
                                             * leaf will
                                             * jump to this position in added branch) */
    pub(crate) is_extension_node_s: Column<Advice>, /* contains extension node key (s_advices)
                                                     * and hash of
                                                     * the branch (c_advices) */
    pub(crate) is_extension_node_c: Column<Advice>,
    // The following four columns are only needed in special cases - when a new extension node is inserted
    // and replaces an existing extension node.
    pub(crate) is_mod_ext_node_s_before_mod: Column<Advice>,
    pub(crate) is_mod_ext_node_c_before_mod: Column<Advice>,
    pub(crate) is_mod_ext_node_s_after_mod: Column<Advice>,
    pub(crate) is_mod_ext_node_c_after_mod: Column<Advice>,
    pub(crate) is_mod_ext_node_before_mod_selectors: Column<Advice>,
    pub(crate) is_mod_ext_node_after_mod_selectors: Column<Advice>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> BranchCols<F> {
    pub(crate) fn new(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            is_init: meta.advice_column(),
            is_child: meta.advice_column(),
            is_last_child: meta.advice_column(),
            node_index: meta.advice_column(),
            is_modified: meta.advice_column(),
            modified_node: meta.advice_column(),
            is_at_drifted_pos: meta.advice_column(),
            drifted_pos: meta.advice_column(),
            is_extension_node_s: meta.advice_column(),
            is_extension_node_c: meta.advice_column(),
            is_mod_ext_node_s_before_mod: meta.advice_column(),
            is_mod_ext_node_c_before_mod: meta.advice_column(),
            is_mod_ext_node_s_after_mod: meta.advice_column(),
            is_mod_ext_node_c_after_mod: meta.advice_column(),
            is_mod_ext_node_before_mod_selectors: meta.advice_column(),
            is_mod_ext_node_after_mod_selectors: meta.advice_column(),
            _marker: PhantomData,
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct BranchConfig<F> {
    _marker: PhantomData<F>,
}

impl<F: FieldExt> BranchConfig<F> {
    #[allow(clippy::too_many_arguments)]
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        position_cols: PositionCols<F>,
        is_account_leaf_in_added_branch: Column<Advice>,
        s_main: MainCols<F>,
        c_main: MainCols<F>,
        accs: AccumulatorCols<F>,
        branch: BranchCols<F>,
        denoter: DenoteCols<F>,
        fixed_table: [Column<Fixed>; 3],
        randomness: Expression<F>,
    ) -> Self {
        let config = BranchConfig {
            _marker: PhantomData,
        };
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
                let q_enable = meta.query_fixed(position_cols.q_enable, Rotation::cur());
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
                    * is_branch_placeholder_c // C is correct here
                    * (sum_rlp2_s - c320.clone()) // There are constraints which ensure there is only 0 or 160 at rlp2 for branch children.
                ));
                constraints.push((
                    "Only two nil-nodes when placeholder branch C",
                    q_enable
                    * is_last_child
                    * is_branch_placeholder_s // S is correct here
                    * (sum_rlp2_c - c320)
                ));

                constraints
            },
        );

        /*
        We need to check that the length of the branch corresponds to the bytes at the beginning of
        the RLP stream that specify the length of the RLP stream. There are three possible cases:
        1. Branch (length 21 = 213 - 192) with one byte of RLP meta data
           [213,128,194,32,1,128,194,32,1,128,128,128,128,128,128,128,128,128,128,128,128,128]

        2. Branch (length 83) with two bytes of RLP meta data
           [248,81,128,128,...

        3. Branch (length 340) with three bytes of RLP meta data
           [249,1,81,128,16,...

        We specify the case as (note that `S` branch and
        `C` branch can be of different length. `s_rlp1, s_rlp2` is used for `S` and
        `s_main.bytes[0], s_main.bytes[1]` is used for `C`):
           rlp1, rlp2: 1, 1 means 1 RLP byte
           rlp1, rlp2: 1, 0 means 2 RLP bytes
           rlp1, rlp2: 0, 1 means 3 RLP bytes
        */
        meta.create_gate("RLP length", |meta| {
            let q_not_first = meta.query_fixed(position_cols.q_not_first, Rotation::cur());
            let mut constraints = vec![];

            let is_branch_init_prev = meta.query_advice(branch.is_init, Rotation::prev());

            let s1 = meta.query_advice(s_main.rlp1, Rotation::prev());
            let s2 = meta.query_advice(s_main.rlp2, Rotation::prev());
            let c1 = meta.query_advice(s_main.bytes[0], Rotation::prev());
            let c2 = meta.query_advice(s_main.bytes[1], Rotation::prev());

            /*
            There should never be `rlp1, rlp2: 0, 0` for `S` (we only have three cases, there is no case with
            both being 0).
            */
            constraints.push((
                "Not both zeros: rlp1, rlp2",
                q_not_first.clone()
                    * is_branch_init_prev.clone()
                    * (one.clone() - s1.clone())
                    * (one.clone() - s2.clone()),
            ));

            /*
            There should never be `rlp1, rlp2: 0, 0` for `C` (we only have three cases, there is no case with
            both being 0).
            */
            constraints.push((
                "Not both zeros: s_advices[0], s_advices[1]",
                q_not_first.clone()
                    * is_branch_init_prev.clone()
                    * (one.clone() - c1.clone())
                    * (one.clone() - c2.clone()),
            ));

            let one_rlp_byte_s = s1.clone() * s2.clone();
            let two_rlp_bytes_s = s1.clone() * (one.clone() - s2.clone());
            let three_rlp_bytes_s = (one.clone() - s1) * s2;

            let one_rlp_byte_c = c1.clone() * c2.clone();
            let two_rlp_bytes_c = c1.clone() * (one.clone() - c2.clone());
            let three_rlp_bytes_c = (one.clone() - c1) * c2;

            let rlp_byte0_s =
                meta.query_advice(s_main.bytes[BRANCH_0_S_START - RLP_NUM], Rotation::prev());
            let rlp_byte1_s = meta.query_advice(
                s_main.bytes[BRANCH_0_S_START - RLP_NUM + 1],
                Rotation::prev(),
            );
            let rlp_byte2_s = meta.query_advice(
                s_main.bytes[BRANCH_0_S_START - RLP_NUM + 2],
                Rotation::prev(),
            );

            let rlp_byte0_c =
                meta.query_advice(s_main.bytes[BRANCH_0_C_START - RLP_NUM], Rotation::prev());
            let rlp_byte1_c = meta.query_advice(
                s_main.bytes[BRANCH_0_C_START - RLP_NUM + 1],
                Rotation::prev(),
            );
            let rlp_byte2_c = meta.query_advice(
                s_main.bytes[BRANCH_0_C_START - RLP_NUM + 2],
                Rotation::prev(),
            );

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

            /*
            [0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 128 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1]
            [0 160 164 92 78 34 81 137 173 236 78 208 145 118 128 60 46 5 176 8 229 165 42 222 110 4 252 228 93 243 26 160 241 85 0 160 95 174 59 239 229 74 221 53 227 115 207 137 94 29 119 126 56 209 55 198 212 179 38 213 219 36 111 62 46 43 176 168 1]

            There is `s_rlp2 = 0` when there is a nil node and `s_rlp2 = 160` when non-nil node.
            The expression `s_rlp2 * c160_inv * c32 + 1` gives us the number of bytes used
            in a row (1 or 33 for nil node or non-nil node respectively).
            */

            let is_node_hashed_s = meta.query_advice(denoter.is_node_hashed_s, Rotation::cur());
            let is_node_hashed_c = meta.query_advice(denoter.is_node_hashed_c, Rotation::cur());

            // The following value can be either 1 or 33 (if hashed node),
            // depending on whether it's empty or non-empty row.
            let mut bytes_num_in_row_s = s_rlp2_cur * c160_inv.clone() * c32.clone() + one.clone();
            let mut bytes_num_in_row_c = c_rlp2_cur * c160_inv * c32 + one.clone();

            bytes_num_in_row_s = is_node_hashed_s.clone()
                * (s_advices0_cur - c192.clone() + one.clone())
                + (one.clone() - is_node_hashed_s) * bytes_num_in_row_s.clone();
            bytes_num_in_row_c = is_node_hashed_c.clone()
                * (c_advices0_cur - c192.clone() + one.clone())
                + (one.clone() - is_node_hashed_c) * bytes_num_in_row_c.clone();

            /*
            One RLP byte:
            [1,1,1,1,217,0,0,217,0,0,1,...
            Two RLP bytes:
            [1,0,1,0,248,81,0,248,81,0,3,0,0,0,...
            Three RLP bytes:
            [0,1,0,1,249,2,17,249,2,17,7,0,0,0,...
            */

            /*
            Note: `s_rlp1` stores the number of the remaining bytes in the branch. If there
            are 81 bytes in the branch, and the first branch children contains 33 bytes,
            then `s_rlp1` in this row will have `s_rlp1 = 81 - 33`.
            */

            /*
            We check that the first branch children has properly stored the number of the remaining
            bytes. For example, if there are 81 bytes in the branch and the first branch child
            contains 1 byte, then it needs to store the value `80 = 81 - 1`.
            */
            constraints.push((
                "First branch children RLP length (one RLP meta byte S)",
                q_not_first.clone()
                    * is_branch_init_prev.clone()
                    * one_rlp_byte_s
                    * (rlp_byte0_s
                        - c192.clone()
                        - bytes_num_in_row_s.clone()
                        - s_rlp1_cur.clone()),
            ));
            constraints.push((
                "First branch children RLP length (one RLP meta byte C)",
                q_not_first.clone()
                    * is_branch_init_prev.clone()
                    * one_rlp_byte_c
                    * (rlp_byte0_c - c192 - bytes_num_in_row_c.clone() - c_rlp1_cur.clone()),
            ));

            constraints.push((
                "First branch children RLP length (two RLP meta bytes S)",
                q_not_first.clone()
                    * is_branch_init_prev.clone()
                    * two_rlp_bytes_s
                    * (rlp_byte1_s.clone() - bytes_num_in_row_s.clone() - s_rlp1_cur.clone()),
            ));
            constraints.push((
                "First branch children RLP length (two RLP meta bytes C)",
                q_not_first.clone()
                    * is_branch_init_prev.clone()
                    * two_rlp_bytes_c
                    * (rlp_byte1_c.clone() - bytes_num_in_row_c.clone() - c_rlp1_cur.clone()),
            ));

            constraints.push((
                "First branch children RLP length (three RLP meta bytes S)",
                q_not_first.clone()
                    * is_branch_init_prev.clone()
                    * three_rlp_bytes_s
                    * (rlp_byte1_s * c256.clone() + rlp_byte2_s
                        - bytes_num_in_row_s.clone()
                        - s_rlp1_cur.clone()),
            ));
            constraints.push((
                "First branch children RLP length (three RLP meta bytes C)",
                q_not_first.clone()
                    * is_branch_init_prev.clone()
                    * three_rlp_bytes_c
                    * (rlp_byte1_c * c256 + rlp_byte2_c
                        - bytes_num_in_row_c.clone()
                        - c_rlp1_cur.clone()),
            ));

            // is_branch_child with node_index > 0
            let is_branch_child_cur = meta.query_advice(branch.is_child, Rotation::cur());
            let s_rlp1_prev = meta.query_advice(s_main.rlp1, Rotation::prev());
            let c_rlp1_prev = meta.query_advice(c_main.rlp1, Rotation::prev());

            /*
            We check that the non-first branch children has properly stored the number of the remaining
            bytes. For example, if there are 81 bytes in the branch, the first branch child
            contains 1 byte, the second child contains 33 bytes, then the third child
            needs to store the value `81 - 1 - 33`.
            */
            constraints.push((
                "Branch children node_index > 0 RLP S",
                q_not_first.clone()
                    * is_branch_child_cur.clone()
                    * (one.clone() - is_branch_init_prev.clone())
                    * (s_rlp1_prev - bytes_num_in_row_s - s_rlp1_cur.clone()),
            ));
            constraints.push((
                "Branch children node_index > 0 RLP C",
                q_not_first.clone()
                    * is_branch_child_cur
                    * (one.clone() - is_branch_init_prev)
                    * (c_rlp1_prev - bytes_num_in_row_c - c_rlp1_cur.clone()),
            ));

            /*
            In the final branch child `s_rlp1` and `c_rlp1` need to be 1 (because RLP length
            specifies also ValueNode which occupies 1 byte).
            */
            // TODO: ValueNode
            let is_last_branch_child = meta.query_advice(branch.is_last_child, Rotation::cur());
            constraints.push((
                "Branch last child RLP length S",
                q_not_first.clone() * is_last_branch_child.clone() * (s_rlp1_cur - one.clone()),
            ));
            constraints.push((
                "Branch last child RLP length C",
                q_not_first * is_last_branch_child * (c_rlp1_cur - one),
            ));

            constraints
        });

        meta.create_gate("Branch children selectors", |meta| {
            let q_not_first = meta.query_fixed(position_cols.q_not_first, Rotation::cur());

            let mut constraints = vec![];
            let is_branch_child_prev = meta.query_advice(branch.is_child, Rotation::prev());
            let is_branch_child_cur = meta.query_advice(branch.is_child, Rotation::cur());
            let is_branch_init_prev = meta.query_advice(branch.is_init, Rotation::prev());
            let is_last_branch_child_prev =
                meta.query_advice(branch.is_last_child, Rotation::prev());
            let is_last_branch_child_cur = meta.query_advice(branch.is_last_child, Rotation::cur());

            /*
            If we have  branch child, we can only have branch child or branch init in the previous row.
            */
            constraints.push((
                "Before branch child",
                q_not_first.clone()
                    * is_branch_child_cur.clone()
                    * (is_branch_child_prev.clone() - one.clone())
                    * (is_branch_init_prev.clone() - one.clone()),
            ));

            /*
            If we have `is_branch_init` in the previous row, we have `is_branch_child = 1` in the current row.
            */
            constraints.push((
                "is_branch_child branch is_branch_init",
                q_not_first.clone()
                    * is_branch_init_prev.clone()
                    * (is_branch_child_cur.clone() - one.clone()), // is_branch_child has to be 1
            ));

            /*
            We could have only one constraint using sum, but then we would need
            to limit `node_index` (to prevent values like -1). Now, `node_index` is
            limited by ensuring its first value is 0, its last value is 15,
            and it is being increased by 1.
            If we have `is_branch_init` in the previous row, we have
            `node_index = 0` in the current row.
            */
            let node_index_cur = meta.query_advice(branch.node_index, Rotation::cur());
            constraints.push((
                "node_index = 0 after is_branch_init",
                q_not_first.clone()
                    * is_branch_init_prev.clone()
                    * node_index_cur.clone(), // node_index has to be 0
            ));

            // When `is_branch_child` changes back to 0, previous `node_index` needs to be 15.
            let node_index_prev = meta.query_advice(branch.node_index, Rotation::prev());
            constraints.push((
                "Last branch child node_index",
                q_not_first.clone()
                    * (one.clone() - is_branch_init_prev.clone()) // ignore if previous row was is_branch_init (here is_branch_child changes too)
                    * (is_branch_child_prev.clone()
                        - is_branch_child_cur.clone()) // is_branch_child changes
                    * (node_index_prev
                        - Expression::Constant(F::from(15_u64))), // node_index has to be 15
            ));

            // When `node_index` is not 15, `is_last_child` needs to be 0.
            constraints.push((
                "is_last_child index",
                q_not_first.clone()
                    * is_last_branch_child_cur
                    * (node_index_cur.clone() // for this to work properly is_last_branch_child needs to have value 1 only when is_branch_child
                        - Expression::Constant(F::from(15_u64))),
            ));

            // When node_index is 15, is_last_child needs to be 1.
            constraints.push((
                "is_last_child when node_index = 15",
                q_not_first.clone()
                    * (one.clone() - is_branch_init_prev) // ignore if previous row was is_branch_init (here is_branch_child changes too)
                    * (is_last_branch_child_prev - one.clone())
                    * (is_branch_child_prev
                        - is_branch_child_cur.clone()), /* for this to work properly make sure
                                                         * to have constraints like
                                                         * is_branch_child + is_keccak_leaf +
                                                         * ... = 1 */
            ));

            // `node_index` is increased by 1 for each is_branch_child node.
            let node_index_prev = meta.query_advice(branch.node_index, Rotation::prev());
            constraints.push((
                "node_index increasing for branch children",
                q_not_first.clone()
                    * is_branch_child_cur.clone()
                    * node_index_cur.clone() // ignore if node_index = 0
                    * (node_index_cur.clone() - node_index_prev - one.clone()),
            ));

            let modified_node_prev = meta.query_advice(branch.modified_node, Rotation::prev());
            let modified_node_cur = meta.query_advice(branch.modified_node, Rotation::cur());

            /*
            `modified_node` (the index of the branch child that is modified)
            needs to be the same for all branch nodes.
            */
            constraints.push((
                "modified_node the same for all branch children",
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

            /*
            `drifted_pos` (the index of the branch child that drifted down into a newly added branch)
            needs to be the same for all branch nodes.
            */
            constraints.push((
                "drifted_pos the same for all branch children",
                q_not_first.clone()
                    * (one.clone()
                        - is_branch_placeholder_s
                        - is_branch_placeholder_c)
                    * node_index_cur.clone() // ignore if node_index = 0
                    * (drifted_pos_prev - drifted_pos_cur),
            ));

            let is_last_branch_child = meta.query_advice(branch.is_last_child, Rotation::cur());
            let is_branch_placeholder_s_from_last = meta.query_advice(
                s_main.bytes[IS_BRANCH_S_PLACEHOLDER_POS - RLP_NUM],
                Rotation(-16),
            );
            let is_branch_placeholder_c_from_last = meta.query_advice(
                s_main.bytes[IS_BRANCH_C_PLACEHOLDER_POS - RLP_NUM],
                Rotation(-16),
            );
            // Rotations could be avoided but we would need additional is_branch_placeholder column.
            for ind in 0..16 {
                let mut s_hash = vec![];
                let mut c_hash = vec![];
                for column in s_main.bytes.iter() {
                    s_hash.push(meta.query_advice(*column, Rotation(-15+ind)));
                }
                for column in c_main.bytes.iter() {
                    c_hash.push(meta.query_advice(*column, Rotation(-15+ind)));
                }
                let s_hash_rlc = bytes_expr_into_rlc(&s_hash, randomness.clone());
                let c_hash_rlc = bytes_expr_into_rlc(&c_hash, randomness.clone());

                let is_modified = meta.query_advice(branch.is_modified, Rotation(-15+ind));
                let is_at_drifted_pos = meta.query_advice(branch.is_at_drifted_pos, Rotation(-15+ind));
                let s_mod_node_hash_rlc_cur = meta.query_advice(accs.s_mod_node_rlc, Rotation(-15+ind));
                let c_mod_node_hash_rlc_cur = meta.query_advice(accs.c_mod_node_rlc, Rotation(-15+ind));

                /*
                For a branch placeholder we do not have any constraints. However, in the parallel
                (regular) branch we have an additional constraint (besides `is_modified` row
                corresponding to `mod_nod_hash_rlc`) in this case: `is_at_drifted_pos main.bytes RLC`
                is stored in the placeholder `mod_node_hash_rlc`. For example, if there is a placeholder
                branch in `S` proof, we have:
                 * `is_modified c_main.bytes RLC = c_mod_node_hash_rlc`
                 * `is_at_drifted_pos c_main.bytes RLC = s_mod_node_hash_rlc`
                That means we simply use `mod_node_hash_rlc` column (because it is not occupied)
                in the placeholder branch for `is_at_drifted_pos main.bytes RLC` of
                the regular parallel branch.

                When `S` branch is NOT a placeholder, `s_main.bytes RLC` corresponds to the value
                stored in `accumulators.s_mod_node_rlc` in `is_modified` row.

                Note that `s_hash_rlc` is a bit misleading naming, because sometimes the branch
                child is not hashed (shorter than 32 bytes), but in this case we need to compute
                the RLC too - the same computation is used (stored in variable `s_hash_rlc`), but
                we check in `branch_parallel` that the non-hashed child is of the appropriate length
                (the length is specified by `rlp2`) and that there are 0s after the last branch child byte.
                The same applies for `c_hash_rlc`.
                */
                constraints.push((
                    "NOT is_branch_placeholder_s: s_mod_node_hash_rlc corresponds to s_main.bytes at modified pos",
                    q_not_first.clone()
                            * is_last_branch_child.clone()
                            * (one.clone() - is_branch_placeholder_s_from_last.clone())
                            * is_modified.clone()
                            * (s_hash_rlc.clone() - s_mod_node_hash_rlc_cur.clone()),
                ));

                /*
                When `S` branch is a placeholder, `c_main.bytes RLC` corresponds to the value
                stored in `accumulators.s_mod_node_rlc` in `is_at_drifted_pos` row.
                */
                constraints.push((
                    "is_branch_placeholder_s: s_mod_node_hash_rlc corresponds to c_main.bytes at drifted pos",
                    q_not_first.clone()
                            * is_last_branch_child.clone()
                            * is_branch_placeholder_s_from_last.clone()
                            * is_at_drifted_pos.clone()
                            * (c_hash_rlc.clone() - s_mod_node_hash_rlc_cur), // c_hash_rlc is correct
                ));

                /*
                When `C` branch is NOT a placeholder, `c_main.bytes RLC` corresponds to the value
                stored in `accumulators.c_mod_node_rlc` in `is_modified` row.
                */
                constraints.push((
                    "NOT is_branch_placeholder_c: c_mod_node_hash_rlc corresponds to c_main.bytes at modified pos",
                    q_not_first.clone()
                            * is_last_branch_child.clone()
                            * (one.clone() - is_branch_placeholder_c_from_last.clone())
                            * is_modified.clone()
                            * (c_hash_rlc.clone() - c_mod_node_hash_rlc_cur.clone()),
                ));

                /*
                When `C` branch is a placeholder, `s_main.bytes RLC` corresponds to the value
                stored in `accumulators.c_mod_node_rlc` in `is_at_drifted_pos` row.
                */
                constraints.push((
                    "is_branch_placeholder_c: c_mod_node_hash_rlc corresponds to s_main.bytes at drifted pos",
                    q_not_first.clone()
                            * is_last_branch_child.clone()
                            * is_branch_placeholder_c_from_last.clone()
                            * is_at_drifted_pos.clone()
                            * (s_hash_rlc.clone() - c_mod_node_hash_rlc_cur), // s_hash_rlc is correct
                ));
            }

            let is_branch_child_cur = meta.query_advice(branch.is_child, Rotation::cur());
            let is_modified = meta.query_advice(branch.is_modified, Rotation::cur());
            let is_at_drifted_pos = meta.query_advice(branch.is_at_drifted_pos, Rotation::cur());
            let drifted_pos = meta.query_advice(branch.drifted_pos, Rotation::cur());

            /*
            `is_modified` is boolean (booleanity is checked in `selectors.rs`):
              * 0 when `node_index != modified_node`
              * 1 when `node_index == modified_node`
            */
            constraints.push((
                "is_modified = 1 only for modified node",
                q_not_first.clone()
                    * is_branch_child_cur.clone()
                    * is_modified
                    * (node_index_cur.clone() - modified_node_cur),
            ));

            /* 
            `is_at_drifted_pos` is boolean (booleanity is checked in `selectors.rs`):
              * 0 when `node_index != drifted_pos`
              * 1 when `node_index == drifted_pos`
            */
            constraints.push((
                "is_at_drifted_pos = 1 only for drifted node",
                q_not_first
                    * is_branch_child_cur
                    * is_at_drifted_pos
                    * (node_index_cur - drifted_pos),
            ));

            constraints
        });

        meta.create_gate("Branch placeholder selectors", |meta| {
            /*
            Note: Not merged with gate above because this needs to be checked in the first row
            too and we need to avoid rotation -1.
            */
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
            let is_branch_non_hashed_s = meta.query_advice(
                s_main.bytes[IS_S_BRANCH_NON_HASHED_POS - RLP_NUM],
                Rotation::cur(),
            );
            let is_branch_non_hashed_c = meta.query_advice(
                s_main.bytes[IS_C_BRANCH_NON_HASHED_POS - RLP_NUM],
                Rotation::cur(),
            );

            let q_enable = meta.query_fixed(position_cols.q_enable, Rotation::cur());

            /*
            `is_branch_placeholder_s` needs to be boolean.
            */
            constraints.push((
                "Bool check is_branch_placeholder_s",
                get_bool_constraint(
                    q_enable.clone() * is_branch_init_cur.clone(),
                    is_branch_placeholder_s,
                ),
            ));

            /*
            `is_branch_placeholder_c` needs to be boolean.
            */
            constraints.push((
                "Bool check is_branch_placeholder_c",
                get_bool_constraint(
                    q_enable.clone() * is_branch_init_cur.clone(),
                    is_branch_placeholder_c,
                ),
            ));

            /*
            `is_branch_non_hashed_s` needs to be boolean.
            */
            constraints.push((
                "Bool check is_branch_non_hashed_s",
                get_bool_constraint(
                    q_enable.clone() * is_branch_init_cur.clone(),
                    is_branch_non_hashed_s,
                ),
            ));

            /*
            `is_branch_non_hashed_c` needs to be boolean.
            */
            constraints.push((
                "Bool check is_branch_non_hashed_c",
                get_bool_constraint(q_enable * is_branch_init_cur, is_branch_non_hashed_c),
            ));

            constraints
        });

        /*
        The cell `s_main.bytes[NIBBLES_COUNTER_POS - RLP_NUM]` in branch init row stores the number of
        nibbles used up to this point (up to this branch). If a regular branch, the counter increases only
        by 1 as only one nibble is used to determine the position of `modified_node` in a branch.
        On the contrary, when it is an extension node the counter increases by the number of nibbles
        in the extension key and the additional nibble for the position in a branch (this constraint
        is in `extension_node.rs` though).
        */
        meta.create_gate("Branch number of nibbles (not first level)", |meta| {
            let mut constraints = vec![];
            let q_enable = meta.query_fixed(position_cols.q_enable, Rotation::cur());
            let not_first_level = meta.query_advice(position_cols.not_first_level, Rotation::cur());
            let is_branch_init_cur = meta.query_advice(branch.is_init, Rotation::cur());
            let is_extension_node = get_is_extension_node(meta, s_main.bytes, 0);

            // Only check if there is an account above the branch.
            let is_account_leaf_in_added_branch =
                meta.query_advice(is_account_leaf_in_added_branch, Rotation(-1));

            let nibbles_count_cur =
                meta.query_advice(s_main.bytes[NIBBLES_COUNTER_POS - RLP_NUM], Rotation::cur());
            let nibbles_count_prev = meta.query_advice(
                s_main.bytes[NIBBLES_COUNTER_POS - RLP_NUM],
                Rotation(-BRANCH_ROWS_NUM),
            );

            constraints.push((
                "nibbles_count",
                q_enable
                    * is_branch_init_cur
                    * (one.clone() - is_extension_node) // extension node counterpart constraint is in extension_node.rs
                    * (one.clone() - is_account_leaf_in_added_branch)
                    * not_first_level
                    * (nibbles_count_cur - nibbles_count_prev - one.clone()),
            ));

            constraints
        });

        /*
        If we are in the first level of the trie, `nibbles_count` needs to be 1.
        */
        meta.create_gate("Branch number of nibbles (first level)", |meta| {
            let mut constraints = vec![];
            let q_enable = meta.query_fixed(position_cols.q_enable, Rotation::cur());
            let not_first_level = meta.query_advice(position_cols.not_first_level, Rotation::cur());
            let is_branch_init_cur = meta.query_advice(branch.is_init, Rotation::cur());
            let is_extension_node = get_is_extension_node(meta, s_main.bytes, 0);

            // Only check if there is an account above the branch.
            let is_account_leaf_in_added_branch =
                meta.query_advice(is_account_leaf_in_added_branch, Rotation(-1));

            let nibbles_count_cur =
                meta.query_advice(s_main.bytes[NIBBLES_COUNTER_POS - RLP_NUM], Rotation::cur());

            /*
            If branch is in the first level of the account trie, `nibbles_count` needs to be 1.
            */
            constraints.push((
                "nibbles_count first level account",
                q_enable.clone()
                    * is_branch_init_cur.clone()
                    * (one.clone() - is_extension_node.clone()) // extension node counterpart constraint is in extension_node.rs
                    * (one.clone() - not_first_level)
                    * (nibbles_count_cur.clone() - one.clone()),
            ));

            /*
            If branch is in the first level of the storage trie, `nibbles_count` needs to be 1.
            */
            constraints.push((
                "nibbles_count first level storage",
                q_enable
                    * is_branch_init_cur
                    * (one.clone() - is_extension_node) // extension node counterpart constraint is in extension_node.rs
                    * is_account_leaf_in_added_branch
                    * (nibbles_count_cur - one.clone()),
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
            let q_not_first = meta.query_fixed(position_cols.q_not_first, Rotation::cur());
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
        pv: &mut ProofValues<F>,
        offset: usize,
    ) -> Result<(), Error> {
        let row = &witness[offset];

        pv.modified_node = row.get_byte(BRANCH_0_KEY_POS);
        pv.node_index = 0;
        pv.drifted_pos = row.get_byte(DRIFTED_POS);

        // Get the child that is being changed and convert it to words to enable
        // lookups:
        let mut s_hash = witness[offset + 1 + pv.modified_node as usize]
            .s_hash_bytes()
            .to_vec();
        let mut c_hash = witness[offset + 1 + pv.modified_node as usize]
            .c_hash_bytes()
            .to_vec();
        pv.s_mod_node_hash_rlc = bytes_into_rlc(&s_hash, mpt_config.randomness);
        pv.c_mod_node_hash_rlc = bytes_into_rlc(&c_hash, mpt_config.randomness);

        if row.get_byte(IS_BRANCH_S_PLACEHOLDER_POS) == 1 {
            // We put hash of a node that moved down to the added branch.
            // This is needed to check the hash of leaf_in_added_branch.
            s_hash = witness[offset + 1 + pv.drifted_pos as usize]
                .s_hash_bytes()
                .to_vec();
            pv.s_mod_node_hash_rlc = bytes_into_rlc(&s_hash, mpt_config.randomness);
            pv.is_branch_s_placeholder = true
        } else {
            pv.is_branch_s_placeholder = false
        }
        if row.get_byte(IS_BRANCH_C_PLACEHOLDER_POS) == 1 {
            c_hash = witness[offset + 1 + pv.drifted_pos as usize]
                .c_hash_bytes()
                .to_vec();
            pv.c_mod_node_hash_rlc = bytes_into_rlc(&c_hash, mpt_config.randomness);
            pv.is_branch_c_placeholder = true
        } else {
            pv.is_branch_c_placeholder = false
        }
        /*
        If no placeholder branch, we set `drifted_pos = modified_node`. This
        is needed just to make some other constraints (`s_mod_node_hash_rlc`
        and `c_mod_node_hash_rlc` correspond to the proper node) easier to write.
        */
        if row.get_byte(IS_BRANCH_S_PLACEHOLDER_POS) == 0
            && row.get_byte(IS_BRANCH_C_PLACEHOLDER_POS) == 0
        {
            pv.drifted_pos = pv.modified_node
        }

        let account_leaf = AccountLeaf::default();
        let storage_leaf = StorageLeaf::default();
        let branch = Branch {
            is_branch_init: true,
            ..Default::default()
        };
 
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
        pv.acc_mult_s = mpt_config.randomness;

        if s_len[0] == 249 {
            pv.acc_s += F::from(s_len[1]) * pv.acc_mult_s;
            pv.acc_mult_s *= mpt_config.randomness;
            pv.acc_s += F::from(s_len[2]) * pv.acc_mult_s;
            pv.acc_mult_s *= mpt_config.randomness;

            pv.rlp_len_rem_s = s_len[1] as i32 * 256 + s_len[2] as i32;
        } else if s_len[0] == 248 {
            pv.acc_s += F::from(s_len[1]) * pv.acc_mult_s;
            pv.acc_mult_s *= mpt_config.randomness;

            pv.rlp_len_rem_s = s_len[1] as i32;
        } else {
            pv.rlp_len_rem_s = s_len[0] as i32 - 192;
        }

        let c_len = [0, 1, 2].map(|i| row.get_byte(BRANCH_0_C_START + i) as u64);
        pv.acc_c = F::from(c_len[0]);
        pv.acc_mult_c = mpt_config.randomness;

        if c_len[0] == 249 {
            pv.acc_c += F::from(c_len[1]) * pv.acc_mult_c;
            pv.acc_mult_c *= mpt_config.randomness;
            pv.acc_c += F::from(c_len[2]) * pv.acc_mult_c;
            pv.acc_mult_c *= mpt_config.randomness;

            pv.rlp_len_rem_c = c_len[1] as i32 * 256 + c_len[2] as i32;
        } else if c_len[0] == 248 {
            pv.acc_c += F::from(c_len[1]) * pv.acc_mult_c;
            pv.acc_mult_c *= mpt_config.randomness;

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

        pv.is_even =
            row.get_byte(IS_EXT_LONG_EVEN_C16_POS) + row.get_byte(IS_EXT_LONG_EVEN_C1_POS) == 1;
        pv.is_odd = row.get_byte(IS_EXT_LONG_ODD_C16_POS)
            + row.get_byte(IS_EXT_LONG_ODD_C1_POS)
            + row.get_byte(IS_EXT_SHORT_C16_POS)
            + row.get_byte(IS_EXT_SHORT_C1_POS)
            == 1;
        pv.is_short = row.get_byte(IS_EXT_SHORT_C16_POS) + row.get_byte(IS_EXT_SHORT_C1_POS) == 1;
        pv.is_long = row.get_byte(IS_EXT_LONG_EVEN_C16_POS)
            + row.get_byte(IS_EXT_LONG_EVEN_C1_POS)
            + row.get_byte(IS_EXT_LONG_ODD_C16_POS)
            + row.get_byte(IS_EXT_LONG_ODD_C1_POS)
            == 1;
        pv.is_extension_node = pv.is_even || pv.is_odd;

        // Assign how many nibbles have been used in the previous extension node +
        // branch.
        pv.nibbles_num += 1; // one nibble is used for position in branch
        if pv.is_extension_node {
            // Get into extension node S
            let row_ext = &witness[offset + BRANCH_ROWS_NUM as usize - 2];
            let ext_nibbles: usize;
            if row_ext.get_byte(1) <= 32 {
                ext_nibbles = 1
            } else if row_ext.get_byte(0) < 248 {
                if row_ext.get_byte(2) == 0 {
                    // even number of nibbles
                    ext_nibbles = ((row_ext.get_byte(1) - 128) as usize - 1) * 2;
                } else {
                    ext_nibbles = (row_ext.get_byte(1) - 128) as usize * 2 - 1;
                }
            } else if row_ext.get_byte(3) == 0 {
                // even number of nibbles
                ext_nibbles = ((row_ext.get_byte(2) - 128) as usize - 1) * 2;
            } else {
                ext_nibbles = (row_ext.get_byte(2) - 128) as usize * 2 - 1;
            }

            pv.nibbles_num += ext_nibbles;
        }
        region.assign_advice(
            || "assign number of nibbles".to_string(),
            mpt_config.s_main.bytes[NIBBLES_COUNTER_POS - RLP_NUM],
            offset,
            || Value::known(F::from(pv.nibbles_num as u64)),
        )?;

        Ok(())
    }

    pub(crate) fn assign_branch_child(
        &self,
        region: &mut Region<'_, F>,
        witness: &[MptWitnessRow<F>],
        mpt_config: &MPTConfig<F>,
        pv: &mut ProofValues<F>,
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
                node_mult_diff_s *= mpt_config.randomness;
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
                node_mult_diff_c *= mpt_config.randomness;
            }
        } else if row.get_byte(C_RLP_START + 1) == 0 {
            pv.rlp_len_rem_c -= 1;
        }

        region.assign_advice(
            || "node_mult_diff_s".to_string(),
            mpt_config.accumulators.node_mult_diff_s,
            offset,
            || Value::known(node_mult_diff_s),
        )?;
        region.assign_advice(
            || "node_mult_diff_c".to_string(),
            mpt_config.accumulators.node_mult_diff_c,
            offset,
            || Value::known(node_mult_diff_c),
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
                            pv.mult_diff *= mpt_config.randomness;
                        }
                        pv.key_rlc = pv.extension_node_rlc;
                        // branch part:
                        pv.key_rlc +=
                            F::from(pv.modified_node as u64) * F::from(16) * pv.key_rlc_mult;
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
                        for k in 0..key_len - 1 {
                            let second_nibble = ext_row_c.get_byte(S_START + k);
                            let first_nibble =
                                (ext_row.get_byte(key_len_pos + 2 + k) - second_nibble) / 16;
                            assert_eq!(
                                first_nibble * 16 + second_nibble,
                                ext_row.get_byte(key_len_pos + 2 + k),
                            );
                            pv.extension_node_rlc += F::from(first_nibble as u64) * pv.key_rlc_mult;

                            pv.key_rlc_mult *= mpt_config.randomness;
                            pv.mult_diff *= mpt_config.randomness;

                            pv.extension_node_rlc +=
                                F::from(second_nibble as u64) * F::from(16) * pv.key_rlc_mult;
                        }

                        pv.key_rlc = pv.extension_node_rlc;
                        // branch part:
                        pv.key_rlc += F::from(pv.modified_node as u64) * pv.key_rlc_mult;
                        pv.key_rlc_mult *= mpt_config.randomness;
                    } else if pv.is_short {
                        pv.extension_node_rlc += F::from((ext_row.get_byte(1) - 16) as u64)
                            * F::from(16)
                            * pv.key_rlc_mult;
                        pv.key_rlc = pv.extension_node_rlc;
                        // branch part:
                        pv.key_rlc += F::from(pv.modified_node as u64) * pv.key_rlc_mult;
                        pv.key_rlc_mult *= mpt_config.randomness;
                        pv.mult_diff = mpt_config.randomness;
                    }
                } else if pv.is_even && pv.is_long {
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
                        pv.extension_node_rlc += F::from(first_nibble as u64) * pv.key_rlc_mult;

                        pv.key_rlc_mult *= mpt_config.randomness;
                        pv.mult_diff *= mpt_config.randomness;

                        pv.extension_node_rlc +=
                            F::from(16) * F::from(second_nibble as u64) * pv.key_rlc_mult;
                    }

                    pv.key_rlc = pv.extension_node_rlc;
                    // branch part:
                    pv.key_rlc += F::from(pv.modified_node as u64) * pv.key_rlc_mult;
                    pv.key_rlc_mult *= mpt_config.randomness;
                    pv.key_rlc_sel = !pv.key_rlc_sel;
                } else if pv.is_odd && pv.is_long {
                    pv.extension_node_rlc +=
                        F::from((ext_row.get_byte(key_len_pos + 1) - 16) as u64) * pv.key_rlc_mult;

                    pv.key_rlc_mult *= mpt_config.randomness;

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
                        pv.mult_diff *= mpt_config.randomness;
                    }
                    pv.key_rlc = pv.extension_node_rlc;
                    // branch part:
                    pv.key_rlc += F::from(pv.modified_node as u64) * F::from(16) * pv.key_rlc_mult;
                    // key_rlc_mult stays the same
                } else if pv.is_short {
                    pv.extension_node_rlc +=
                        F::from((ext_row.get_byte(1) - 16) as u64) * pv.key_rlc_mult;

                    pv.key_rlc = pv.extension_node_rlc;

                    pv.key_rlc_mult *= mpt_config.randomness;
                    // branch part:
                    pv.key_rlc += F::from(pv.modified_node as u64) * F::from(16) * pv.key_rlc_mult;
                    pv.mult_diff = mpt_config.randomness;
                }
            } else {
                if pv.key_rlc_sel {
                    pv.key_rlc += F::from(pv.modified_node as u64) * F::from(16) * pv.key_rlc_mult;
                    // key_rlc_mult stays the same
                } else {
                    pv.key_rlc += F::from(pv.modified_node as u64) * pv.key_rlc_mult;
                    pv.key_rlc_mult *= mpt_config.randomness;
                }
                pv.key_rlc_sel = !pv.key_rlc_sel;
            }
            row.assign_branch_row(region, mpt_config, pv, offset)?;
        } else {
            row.assign_branch_row(region, mpt_config, pv, offset)?;
        }

        /*
        `sel1` is to distinguish whether the S node at `modified_node` position is empty.
        `sel2` is to distinguish whether the C node at `modified_node` position is empty.
        Note that 128 comes from the RLP byte denoting empty leaf.
        Having 128 for `*_mod_node_hash_rlc` means there is no node at
        this position in branch - for example,
        `s_mode_node_hash_rlc = 128` and `c_words` is some other value
        when new value is added to the trie
        (as opposed to just updating the value).
        Note that there is a potential attack if a leaf node
        is found with hash `[128, 0, ..., 0]`,
        but the probability is negligible.
        */
        let mut sel1 = F::zero();
        let mut sel2 = F::zero();
        if pv.s_mod_node_hash_rlc == F::from(128_u64) {
            sel1 = F::one();
        }
        if pv.c_mod_node_hash_rlc == F::from(128_u64) {
            sel2 = F::one();
        }

        region.assign_advice(
            || "assign sel1".to_string(),
            mpt_config.denoter.sel1,
            offset,
            || Value::known(sel1),
        )?;
        region.assign_advice(
            || "assign sel2".to_string(),
            mpt_config.denoter.sel2,
            offset,
            || Value::known(sel2),
        )?;

        // reassign (it was assigned to 0 in assign_row) branch_acc and
        // branch_mult to proper values

        // We need to distinguish between empty and non-empty node:
        // empty node at position 1: 0
        // non-empty node at position 1: 160

        let c128 = F::from(128_u64);
        let c160 = F::from(160_u64);

        let compute_branch_acc_and_mult =
            |branch_acc: &mut F, branch_mult: &mut F, rlp_start: usize, start: usize| {
                if row.get_byte(rlp_start + 1) == 0 && row.get_byte(start) == 128 {
                    *branch_acc += c128 * *branch_mult;
                    *branch_mult *= mpt_config.randomness;
                } else if row.get_byte(rlp_start + 1) == 160 {
                    *branch_acc += c160 * *branch_mult;
                    *branch_mult *= mpt_config.randomness;
                    for i in 0..HASH_WIDTH {
                        *branch_acc += F::from(row.get_byte(start + i) as u64) * *branch_mult;
                        *branch_mult *= mpt_config.randomness;
                    }
                } else {
                    *branch_acc += F::from(row.get_byte(start) as u64) * *branch_mult;
                    *branch_mult *= mpt_config.randomness;
                    let len = row.get_byte(start) as usize - 192;
                    for i in 0..len {
                        *branch_acc += F::from(row.get_byte(start + 1 + i) as u64) * *branch_mult;
                        *branch_mult *= mpt_config.randomness;
                    }
                }
            };

        // TODO: add branch ValueNode info

        compute_branch_acc_and_mult(&mut pv.acc_s, &mut pv.acc_mult_s, S_RLP_START, S_START);
        compute_branch_acc_and_mult(&mut pv.acc_c, &mut pv.acc_mult_c, C_RLP_START, C_START);
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
            || Value::known(pv.key_rlc),
        )?;
        region.assign_advice(
            || "assign key_rlc_mult".to_string(),
            mpt_config.accumulators.key.mult,
            offset,
            || Value::known(pv.key_rlc_mult),
        )?;

        pv.node_index += 1;

        Ok(())
    }
}
