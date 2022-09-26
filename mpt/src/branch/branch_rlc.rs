use halo2_proofs::{
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, VirtualCells},
    poly::Rotation,
};
use pairing::arithmetic::FieldExt;
use std::marker::PhantomData;

use crate::{
    columns::{AccumulatorPair, MainCols},
    helpers::mult_diff_lookup,
    param::{HASH_WIDTH, R_TABLE_LEN},
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

The constraints in `branch_rlc.rs` check whether the branch RLC is being properly computed row by row.
There are three type of branch children rows: empty children, non-empty hashed children,
non-empty non-hashed children. We need to take into account these three types when computing
the intermediate RLC of the current row.

Note that the RLC for branch init row is checked in `branch_init.rs`.
*/

#[derive(Clone, Debug)]
pub(crate) struct BranchRLCConfig<F> {
    _marker: PhantomData<F>,
}

impl<F: FieldExt> BranchRLCConfig<F> {
    #[allow(clippy::too_many_arguments)]
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: impl Fn(&mut VirtualCells<'_, F>) -> Expression<F>,
        main: MainCols<F>,
        branch_acc: AccumulatorPair<F>,
        is_node_hashed: Column<Advice>,
        node_mult_diff: Column<Advice>,
        r_table: Vec<Expression<F>>,
        fixed_table: [Column<Fixed>; 3],
    ) -> Self {
        let config = BranchRLCConfig {
            _marker: PhantomData,
        };
        let c128 = Expression::Constant(F::from(128_u64));

        meta.create_gate("Branch RLC", |meta| {
            let q_enable = q_enable(meta);

            let mut constraints = vec![];
            let rlp2 = meta.query_advice(main.rlp2, Rotation::cur());
            let branch_acc_prev = meta.query_advice(branch_acc.rlc, Rotation::prev());
            let branch_acc_cur = meta.query_advice(branch_acc.rlc, Rotation::cur());
            let branch_mult_prev = meta.query_advice(branch_acc.mult, Rotation::prev());
            let branch_mult_cur = meta.query_advice(branch_acc.mult, Rotation::cur());

            let is_node_hashed = meta.query_advice(is_node_hashed, Rotation::cur());

            let one = Expression::Constant(F::one());
            let c160 = Expression::Constant(F::from(160_u64));

            /*
            When a branch child is empty, we only have one byte (128 at `bytes[0]`)
            that needs to be added to the RLC:
            `branch_acc_curr = branch_acc_prev + 128 * branch_mult_prev`

            `branch_mult_prev` is the value that is to be used when multiplying the byte to be added
            to the RLC. Note that `branch_mult_prev` is stored in the previous row.
            */
            constraints.push((
                "Branch RLC empty",
                q_enable.clone()
                    * (one.clone() - is_node_hashed.clone())
                    * (c160.clone() - rlp2.clone())
                    * (branch_acc_cur.clone()
                        - branch_acc_prev.clone()
                        - c128 * branch_mult_prev.clone()),
            ));

            /*
            When a branch child is empty, we only have one byte in a row and the multiplier only
            changes by factor `r`.
            */
            constraints.push((
                "Branch RLC mult empty",
                q_enable.clone()
                    * (one.clone() - is_node_hashed.clone())
                    * (c160.clone() - rlp2.clone())
                    * (branch_mult_cur.clone() - branch_mult_prev.clone() * r_table[0].clone()),
            ));

            let mut expr = c160 * branch_mult_prev.clone();
            for (ind, col) in main.bytes.iter().enumerate() {
                let s = meta.query_advice(*col, Rotation::cur());
                expr = expr + s * branch_mult_prev.clone() * r_table[ind].clone();
            }

            /*
            When a branch child is non-empty and hashed, we have 33 bytes in a row.
            We need to add these 33 bytes to the RLC.
            */
            constraints.push((
                "Branch RLC non-empty hashed",
                q_enable.clone()
                    * (one.clone() - is_node_hashed.clone())
                    * rlp2.clone()
                    * (branch_acc_cur.clone() - branch_acc_prev.clone() - expr),
            ));

            /*
            When a branch child is non-empty and hashed, we have 33 bytes in a row.
            The multiplier changes by factor `r^33`.
            */
            constraints.push((
                "Branch RLC mult non-empty hashed",
                q_enable.clone()
                    * (one - is_node_hashed.clone())
                    * rlp2
                    * (branch_mult_cur.clone()
                        - branch_mult_prev.clone()
                            * r_table[R_TABLE_LEN - 1].clone()
                            * r_table[0].clone()),
            ));

            let advices0 = meta.query_advice(main.bytes[0], Rotation::cur());
            let mut acc = branch_acc_prev + advices0 * branch_mult_prev.clone();
            for ind in 1..HASH_WIDTH {
                let a = meta.query_advice(main.bytes[ind], Rotation::cur());
                acc = acc + a * branch_mult_prev.clone() * r_table[ind - 1].clone();
            }

            /*
            When a branch child is non-hashed, we have `bytes[0] - 192` bytes in a row.
            We need to add these bytes to the RLC. Note that we add all `bytes` to the RLC, but
            we rely that there are 0s after the last non-hashed byte (see constraints in `branch.rs`).

            For example we have 6 bytes in the following child: `[0,0,198,132,48,0,0,0,1,...]`.
            */
            constraints.push((
                "Branch RLC non-hashed",
                q_enable.clone() * is_node_hashed.clone() * (branch_acc_cur - acc),
            ));

            let node_mult_diff = meta.query_advice(node_mult_diff, Rotation::cur());

            /*
            When a branch child is non-hashed, we have `f = bytes[0] - 192` bytes in a row.
            The multiplier changes by factor `r^{f+1}`. `+1` is for the byte that specifies the length.

            We do not know in advance the factor `f`, so we use the lookup table that it corresponds
            to the length specified at `rlp2` position. See `mult_diff_lookup` constraint below.
            */
            constraints.push((
                "Branch RLC mult non-hashed",
                q_enable
                    * is_node_hashed
                    * (branch_mult_cur - branch_mult_prev * node_mult_diff * r_table[0].clone()), // * r_table[0] because of the first (length) byte
            ));

            constraints
        });

        let sel = |meta: &mut VirtualCells<F>| {
            let q_enable = q_enable(meta);
            let is_node_hashed = meta.query_advice(is_node_hashed, Rotation::cur());

            q_enable * is_node_hashed
        };

        /*
        We need to check that the multiplier in non-hashed nodes changes according to the non-hashed
        node length.
        */
        mult_diff_lookup(
            meta,
            sel,
            0,
            main.bytes[0],
            node_mult_diff,
            192,
            fixed_table,
        );

        /*
        Note: the constraints for there being 0s after the non-hashed child last byte are in
        branch_parallel.rs.
        */

        config
    }
}
