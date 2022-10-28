use halo2_proofs::{
    arithmetic::FieldExt,
    plonk::{Column, ConstraintSystem, Expression, Fixed, VirtualCells},
    poly::Rotation,
};
use std::marker::PhantomData;

use crate::{
    mpt_circuit::columns::{AccumulatorCols, MainCols},
    mpt_circuit::helpers::{get_bool_constraint, range_lookups},
    mpt_circuit::FixedTableTag,
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

The constraints in this file check whether the RLC of the branch init row (first branch row)
is computed correctly.

There are three possible cases:
1. Branch (length 21 = 213 - 192) with one byte of RLP meta data
    [213,128,194,32,1,128,194,32,1,128,128,128,128,128,128,128,128,128,128,128,128,128]
    In this case the init row looks like (specifying only for `S`, we put `x` for `C`):
    [1,1,x,x,213,0,0,...]
    The RLC is simply `213`.

2. Branch (length 83) with two bytes of RLP meta data
    [248,81,128,128,...
    In this case the init row looks like (specifying only for `S`, we put `x` for `C`):
    [1,0,x,x,248,81,0,...]
    The RLC is `248 + 81*r`.


3. Branch (length 340) with three bytes of RLP meta data
    [249,1,81,128,16,...
    In this case the init row looks like (specifying only for `S`, we put `x` for `C`):
    [1,0,x,x,249,1,81,...]
    The RLC is `249 + 1*r + 81*r^2`.

We specify the case as (note that `S` branch and
`C` branch can be of different length. `s_rlp1, s_rlp2` is used for `S` and
`s_main.bytes[0], s_main.bytes[1]` is used for `C`):
    rlp1, rlp2: 1, 1 means 1 RLP byte
    rlp1, rlp2: 1, 0 means 2 RLP bytes
    rlp1, rlp2: 0, 1 means 3 RLP bytes

The example branch init above is the second case (two RLP meta bytes).

Note: the constraints for the selectors in branch init row to be boolean are in `branch.rs`
and `extension_node.rs`.
*/

#[derive(Clone, Debug)]
pub(crate) struct BranchInitConfig<F> {
    _marker: PhantomData<F>,
}

impl<F: FieldExt> BranchInitConfig<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: impl Fn(&mut VirtualCells<'_, F>) -> Expression<F> + Copy,
        s_main: MainCols<F>,
        accs: AccumulatorCols<F>,
        randomness: Expression<F>,
        fixed_table: [Column<Fixed>; 3],
    ) -> Self {
        let config = BranchInitConfig {
            _marker: PhantomData,
        };
        let one = Expression::Constant(F::one());

        // Short RLP, meta data contains two bytes: 248, 81
        // [1,0,1,0,248,81,0,248,81,0,3,0,0,0,...
        // The length of RLP stream is: 81.

        // Long RLP, meta data contains three bytes: 249, 2, 17
        // [0,1,0,1,249,2,17,249,2,17,7,0,0,0,...
        // The length of RLP stream is: 2 * 256 + 17.

        /*
        The RLC of the init branch comprises 1, 2, or 3 bytes. This gate ensures the RLC
        is computed properly in each of the three cases. It also ensures that the values
        that specify the case are boolean.
        */
        meta.create_gate("Branch init RLC", |meta| {
            let q_enable = q_enable(meta);

            let mut constraints = vec![];

            // check branch accumulator S in row 0
            let branch_acc_s_cur = meta.query_advice(accs.acc_s.rlc, Rotation::cur());
            let branch_acc_c_cur = meta.query_advice(accs.acc_c.rlc, Rotation::cur());
            let branch_mult_s_cur = meta.query_advice(accs.acc_s.mult, Rotation::cur());
            let branch_mult_c_cur = meta.query_advice(accs.acc_c.mult, Rotation::cur());

            let s1 = meta.query_advice(s_main.rlp1, Rotation::cur());
            let s2 = meta.query_advice(s_main.rlp2, Rotation::cur());
            let c1 = meta.query_advice(s_main.bytes[0], Rotation::cur());
            let c2 = meta.query_advice(s_main.bytes[1], Rotation::cur());

            let one_rlp_byte_s = s1.clone() * s2.clone();
            let two_rlp_bytes_s = s1.clone() * (one.clone() - s2.clone());
            let three_rlp_bytes_s = (one.clone() - s1.clone()) * s2.clone();

            let one_rlp_byte_c = c1.clone() * c2.clone();
            let two_rlp_bytes_c = c1.clone() * (one.clone() - c2.clone());
            let three_rlp_bytes_c = (one.clone() - c1.clone()) * c2.clone();

            constraints.push((
                "Branch init s1 boolean",
                get_bool_constraint(q_enable.clone(), s1),
            ));
            constraints.push((
                "Branch init c1 boolean",
                get_bool_constraint(q_enable.clone(), c1),
            ));
            constraints.push((
                "Branch init s2 boolean",
                get_bool_constraint(q_enable.clone(), s2),
            ));
            constraints.push((
                "Branch init c2 boolean",
                get_bool_constraint(q_enable.clone(), c2),
            ));

            let s_rlp1 = meta.query_advice(s_main.bytes[2], Rotation::cur());
            let s_rlp2 = meta.query_advice(s_main.bytes[3], Rotation::cur());
            let s_rlp3 = meta.query_advice(s_main.bytes[4], Rotation::cur());

            let c_rlp1 = meta.query_advice(s_main.bytes[5], Rotation::cur());
            let c_rlp2 = meta.query_advice(s_main.bytes[6], Rotation::cur());
            let c_rlp3 = meta.query_advice(s_main.bytes[7], Rotation::cur());

            constraints.push((
                "Branch accumulator S row 0 (1)",
                q_enable.clone()
                    * one_rlp_byte_s.clone()
                    * (s_rlp1.clone() - branch_acc_s_cur.clone()),
            ));
            constraints.push((
                "Branch mult S row 0 (1)",
                q_enable.clone()
                    * one_rlp_byte_s
                    * (randomness.clone() - branch_mult_s_cur.clone()),
            ));
            constraints.push((
                "Branch accumulator C row 0 (1)",
                q_enable.clone()
                    * one_rlp_byte_c.clone()
                    * (c_rlp1.clone() - branch_acc_c_cur.clone()),
            ));
            constraints.push((
                "Branch mult C row 0 (1)",
                q_enable.clone()
                    * one_rlp_byte_c
                    * (randomness.clone() - branch_mult_s_cur.clone()),
            ));

            let acc_s_two = s_rlp1.clone() + s_rlp2.clone() * randomness.clone();
            constraints.push((
                "Branch accumulator S row 0 (2)",
                q_enable.clone() * two_rlp_bytes_s.clone() * (acc_s_two - branch_acc_s_cur.clone()),
            ));

            let mult_two = randomness.clone() * randomness.clone();
            constraints.push((
                "Branch mult S row 0 (2)",
                q_enable.clone() * two_rlp_bytes_s * (mult_two.clone() - branch_mult_s_cur.clone()),
            ));

            let acc_c_two = c_rlp1.clone() + c_rlp2.clone() * randomness.clone();
            constraints.push((
                "Branch accumulator C row 0 (2)",
                q_enable.clone() * two_rlp_bytes_c.clone() * (acc_c_two - branch_acc_c_cur.clone()),
            ));

            constraints.push((
                "Branch mult C row 0 (2)",
                q_enable.clone() * two_rlp_bytes_c * (mult_two - branch_mult_c_cur.clone()),
            ));

            let acc_s_three = s_rlp1
                + s_rlp2 * randomness.clone()
                + s_rlp3 * randomness.clone() * randomness.clone();
            constraints.push((
                "Branch accumulator S row 0 (3)",
                q_enable.clone() * three_rlp_bytes_s.clone() * (acc_s_three - branch_acc_s_cur),
            ));

            let mult_three = randomness.clone() * randomness.clone() * randomness.clone();
            constraints.push((
                "Branch mult S row 0 (3)",
                q_enable.clone() * three_rlp_bytes_s * (mult_three.clone() - branch_mult_s_cur),
            ));

            let acc_c_three = c_rlp1
                + c_rlp2 * randomness.clone()
                + c_rlp3 * randomness.clone() * randomness.clone();
            constraints.push((
                "Branch accumulator C row 0 (3)",
                q_enable.clone() * three_rlp_bytes_c.clone() * (acc_c_three - branch_acc_c_cur),
            ));

            constraints.push((
                "Branch mult C row 0 (3)",
                q_enable * three_rlp_bytes_c * (mult_three - branch_mult_c_cur),
            ));

            constraints
        });

        /*
        Range lookups ensure that the values in the used columns are all bytes (between 0 - 255).
        Note: range lookups for extension node rows are in `extension_node_key.rs`.
        */
        range_lookups(
            meta,
            q_enable,
            s_main.bytes.to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );
        range_lookups(
            meta,
            q_enable,
            [s_main.rlp1, s_main.rlp2].to_vec(),
            FixedTableTag::Range256,
            fixed_table,
        );

        config
    }
}
