use halo2_proofs::{
    arithmetic::FieldExt,
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, VirtualCells},
    poly::Rotation,
};

use crate::{
    mpt_circuit::param::{
        HASH_WIDTH, IS_EXT_LONG_EVEN_C16_POS, IS_EXT_LONG_EVEN_C1_POS, IS_EXT_LONG_ODD_C16_POS,
        IS_EXT_LONG_ODD_C1_POS, IS_EXT_SHORT_C16_POS, IS_EXT_SHORT_C1_POS, POWER_OF_RANDOMNESS_LEN,
        RLP_NUM,
    },
    mpt_circuit::FixedTableTag,
};

use super::{
    columns::{AccumulatorCols, MainCols},
    param::{BRANCH_0_C_START, BRANCH_0_S_START},
};

// Turn 32 hash cells into 4 cells containing keccak words.
pub(crate) fn into_words_expr<F: FieldExt>(hash: Vec<Expression<F>>) -> Vec<Expression<F>> {
    let mut words = vec![];
    for i in 0..4 {
        let mut word = Expression::Constant(F::zero());
        let mut exp = Expression::Constant(F::one());
        for j in 0..8 {
            word = word + hash[i * 8 + j].clone() * exp.clone();
            exp = exp * Expression::Constant(F::from(256));
        }
        words.push(word)
    }

    words
}

pub(crate) fn compute_rlc<F: FieldExt>(
    meta: &mut VirtualCells<F>,
    advices: Vec<Column<Advice>>,
    mut rind: usize,
    mult: Expression<F>,
    rotation: i32,
    power_of_randomness: [Expression<F>; HASH_WIDTH],
) -> Expression<F> {
    let mut r_wrapped = false;
    let mut rlc = Expression::Constant(F::zero());
    for col in advices.iter() {
        let s = meta.query_advice(*col, Rotation(rotation));
        if !r_wrapped {
            rlc = rlc + s * power_of_randomness[rind].clone() * mult.clone();
        } else {
            rlc = rlc
                + s * power_of_randomness[rind].clone()
                    * power_of_randomness[POWER_OF_RANDOMNESS_LEN - 1].clone()
                    * mult.clone();
        }
        if rind == POWER_OF_RANDOMNESS_LEN - 1 {
            rind = 0;
            r_wrapped = true;
        } else {
            rind += 1;
        }
    }

    rlc
}

/*
`range_lookups` is not called in some central place, but instead in each config separately
because: (i) some columns not need to be checked in some rows because they are checked to be
RLP compliant, (ii) branch init row specifies the length of the branch which can be bigger than 255. 
*/
pub(crate) fn range_lookups<F: FieldExt>(
    meta: &mut ConstraintSystem<F>,
    q_enable: impl Fn(&mut VirtualCells<'_, F>) -> Expression<F>,
    columns: Vec<Column<Advice>>,
    tag: FixedTableTag,
    fixed_table: [Column<Fixed>; 3],
) {
    for col in columns {
        meta.lookup_any("range_lookup", |meta| {
            let q_enable = q_enable(meta);
            let mut constraints = vec![];

            let s = meta.query_advice(col, Rotation::cur());
            constraints.push((
                Expression::Constant(F::from(tag as u64)),
                meta.query_fixed(fixed_table[0], Rotation::cur()),
            ));
            constraints.push((
                q_enable * s,
                meta.query_fixed(fixed_table[1], Rotation::cur()),
            ));

            constraints
        });
    }
}

pub(crate) fn range256_check<F: FieldExt>(
    meta: &mut ConstraintSystem<F>,
    q_enable: impl Fn(&mut VirtualCells<'_, F>) -> Expression<F> + Clone,
    s_main: MainCols<F>,
    c_main: MainCols<F>,
    fixed_table: [Column<Fixed>; 3],
) {
    range_lookups(
        meta,
        q_enable.clone(),
        s_main.bytes.to_vec(),
        FixedTableTag::Range256,
        fixed_table,
    );
    range_lookups(
        meta,
        q_enable.clone(),
        c_main.bytes.to_vec(),
        FixedTableTag::Range256,
        fixed_table,
    );
    range_lookups(
        meta,
        q_enable,
        [s_main.rlp1, s_main.rlp2, c_main.rlp1, c_main.rlp2].to_vec(),
        FixedTableTag::Range256,
        fixed_table,
    );
}

// The columns after the key stops have to be 0 to prevent attacks on RLC using
// bytes that should be 0.
// Let's say we have a key of length 3, then: [248,112,131,59,158,123,0,0,0,...
// 131 - 128 = 3 presents key length. We need to prove all bytes after key ends
// are 0 (after 59, 158, 123).
// We prove the following (33 is max key length):
// (key_len - 1) * 59 < 33 * 255
// (key_len - 2) * 158 < 33 * 255
// (key_len - 3) * 123 < 33 * 255
// From now on, key_len < 0:
// (key_len - 4) * byte < 33 * 255 (Note that this will be true only if byte =
// 0) (key_len - 5) * byte < 33 * 255 (Note that this will be true only if byte
// = 0) (key_len - 6) * byte < 33 * 255 (Note that this will be true only if
// byte = 0) ...
pub(crate) fn key_len_lookup<F: FieldExt>(
    meta: &mut ConstraintSystem<F>,
    q_enable: impl Fn(&mut VirtualCells<'_, F>) -> Expression<F>,
    ind: usize,
    key_len_col: Column<Advice>,
    column: Column<Advice>,
    len_offset: usize,
    fixed_table: [Column<Fixed>; 3],
) {
    meta.lookup_any("key_len_lookup", |meta| {
        let mut constraints = vec![];
        let q_enable = q_enable(meta);

        let s = meta.query_advice(column, Rotation::cur());
        let offset = Expression::Constant(F::from(len_offset as u64));
        let key_len = meta.query_advice(key_len_col, Rotation::cur()) - offset;
        let key_len_rem = key_len - Expression::Constant(F::from(ind as u64));
        constraints.push((
            Expression::Constant(F::from(FixedTableTag::RangeKeyLen256 as u64)),
            meta.query_fixed(fixed_table[0], Rotation::cur()),
        ));
        constraints.push((
            q_enable * s * key_len_rem,
            meta.query_fixed(fixed_table[1], Rotation::cur()),
        ));

        constraints
    });
}

pub(crate) fn mult_diff_lookup<F: FieldExt>(
    meta: &mut ConstraintSystem<F>,
    q_enable: impl Fn(&mut VirtualCells<'_, F>) -> Expression<F>,
    addition: i8,
    key_len_col: Column<Advice>,
    mult_diff_col: Column<Advice>,
    key_len_offset: usize,
    fixed_table: [Column<Fixed>; 3],
) {
    meta.lookup_any("mult_diff_lookup", |meta| {
        let q_enable = q_enable(meta);
        let mut constraints = vec![];

        let offset = Expression::Constant(F::from(key_len_offset as u64));
        let mut key_len = meta.query_advice(key_len_col, Rotation::cur()) - offset;
        if addition < 0 {
            key_len = key_len - Expression::Constant(F::from(-addition as u64));
        }
        let mult_diff = meta.query_advice(mult_diff_col, Rotation::cur());
        let mut add_expr = Expression::Constant(F::from(addition as u64));
        if addition < 0 {
            add_expr = Expression::Constant(F::zero());
        }

        constraints.push((
            Expression::Constant(F::from(FixedTableTag::RMult as u64)),
            meta.query_fixed(fixed_table[0], Rotation::cur()),
        ));
        constraints.push((
            q_enable.clone() * (key_len + add_expr),
            meta.query_fixed(fixed_table[1], Rotation::cur()),
        ));
        constraints.push((
            q_enable * mult_diff,
            meta.query_fixed(fixed_table[2], Rotation::cur()),
        ));

        constraints
    });
}

pub(crate) fn get_bool_constraint<F: FieldExt>(
    q_enable: Expression<F>,
    expr: Expression<F>,
) -> Expression<F> {
    let one = Expression::Constant(F::from(1_u64));
    q_enable * expr.clone() * (one - expr)
}

pub(crate) fn get_is_extension_node<F: FieldExt>(
    meta: &mut VirtualCells<F>,
    s_advices: [Column<Advice>; HASH_WIDTH],
    rot: i32,
) -> Expression<F> {
    /*
    To reduce the expression degree, we pack together multiple information.
    Constraints for the selectors are in `extension_node.rs`.

    Note: even and odd refers to number of nibbles that are compactly encoded.
    */
    let is_ext_short = get_is_extension_node_one_nibble(meta, s_advices, rot);
    let is_ext_node_even_nibbles = get_is_extension_node_even_nibbles(meta, s_advices, rot);
    let is_ext_node_long_odd_nibbles = get_is_extension_node_long_odd_nibbles(meta, s_advices, rot);

    is_ext_short + is_ext_node_even_nibbles + is_ext_node_long_odd_nibbles
}

pub(crate) fn get_is_extension_node_one_nibble<F: FieldExt>(
    meta: &mut VirtualCells<F>,
    s_advices: [Column<Advice>; HASH_WIDTH],
    rot: i32,
) -> Expression<F> {
    let is_ext_short_c16 =
        meta.query_advice(s_advices[IS_EXT_SHORT_C16_POS - RLP_NUM], Rotation(rot));
    let is_ext_short_c1 =
        meta.query_advice(s_advices[IS_EXT_SHORT_C1_POS - RLP_NUM], Rotation(rot));

    is_ext_short_c16 + is_ext_short_c1
}

pub(crate) fn get_is_extension_node_even_nibbles<F: FieldExt>(
    meta: &mut VirtualCells<F>,
    s_advices: [Column<Advice>; HASH_WIDTH],
    rot: i32,
) -> Expression<F> {
    let is_ext_long_even_c16 =
        meta.query_advice(s_advices[IS_EXT_LONG_EVEN_C16_POS - RLP_NUM], Rotation(rot));
    let is_ext_long_even_c1 =
        meta.query_advice(s_advices[IS_EXT_LONG_EVEN_C1_POS - RLP_NUM], Rotation(rot));

    is_ext_long_even_c16 + is_ext_long_even_c1
}

pub(crate) fn get_is_extension_node_long_odd_nibbles<F: FieldExt>(
    meta: &mut VirtualCells<F>,
    s_advices: [Column<Advice>; HASH_WIDTH],
    rot: i32,
) -> Expression<F> {
    let is_ext_long_odd_c16 =
        meta.query_advice(s_advices[IS_EXT_LONG_ODD_C16_POS - RLP_NUM], Rotation(rot));
    let is_ext_long_odd_c1 =
        meta.query_advice(s_advices[IS_EXT_LONG_ODD_C1_POS - RLP_NUM], Rotation(rot));

    is_ext_long_odd_c16 + is_ext_long_odd_c1
}

pub(crate) fn get_is_inserted_extension_node<F: FieldExt>(
    meta: &mut VirtualCells<F>,
    c_rlp1: Column<Advice>,
    c_rlp2: Column<Advice>,
    rot_into_branch_init: i32,
    is_s: bool,
) -> Expression<F> {
    let mut is_inserted_ext_node = meta.query_advice(
        /* rlp2 (corresponds to IS_INSERTED_EXT_NODE_C_POS) is correct here,
        that means in S proof we have a copy (as a placeholder) of C extension node,
        while the actual S extension node is stored in the rows below the leaf.
        */
        c_rlp2,
        Rotation(rot_into_branch_init),
    );
    if !is_s {
        is_inserted_ext_node = meta.query_advice(
            /* rlp1 (corresponds to IS_INSERTED_EXT_NODE_S_POS) is correct here,
            that means in C proof we have a copy (as a placeholder) of S extension node,
            while the actual C extension node is stored in the rows below the leaf.
            */
            c_rlp1,
            Rotation(rot_into_branch_init),
        );
    }

    is_inserted_ext_node
}

pub(crate) fn bytes_into_rlc<F: FieldExt>(expressions: &[u8], r: F) -> F {
    let mut rlc = F::zero();
    let mut mult = F::one();
    for expr in expressions.iter() {
        rlc += F::from(*expr as u64) * mult;
        mult *= r;
    }

    rlc
}

pub(crate) fn bytes_expr_into_rlc<F: FieldExt>(
    expressions: &[Expression<F>],
    r: Expression<F>,
) -> Expression<F> {
    let mut rlc = Expression::Constant(F::zero());
    let mut mult = Expression::Constant(F::one());
    for expr in expressions.iter() {
        rlc = rlc + expr.clone() * mult.clone();
        mult = mult * r.clone();
    }

    rlc
}

pub(crate) fn get_branch_len<F: FieldExt>(
    meta: &mut VirtualCells<F>,
    s_main: MainCols<F>,
    rot_into_branch_init: i32,
    is_s: bool,
) -> Expression<F> {
    let one = Expression::Constant(F::from(1_u64));
    let c192 = Expression::Constant(F::from(192_u64));

    let mut s1 = meta.query_advice(s_main.rlp1, Rotation(rot_into_branch_init));
    let mut s2 = meta.query_advice(s_main.rlp2, Rotation(rot_into_branch_init));
    if !is_s {
        s1 = meta.query_advice(s_main.bytes[0], Rotation(rot_into_branch_init));
        s2 = meta.query_advice(s_main.bytes[1], Rotation(rot_into_branch_init));
    }

    let one_rlp_byte = s1.clone() * s2.clone();
    let two_rlp_bytes = s1.clone() * (one.clone() - s2.clone());
    let three_rlp_bytes = (one.clone() - s1) * s2;

    let mut rlp_byte0 = meta.query_advice(
        s_main.bytes[BRANCH_0_S_START - RLP_NUM],
        Rotation(rot_into_branch_init),
    );
    let mut rlp_byte1 = meta.query_advice(
        s_main.bytes[BRANCH_0_S_START - RLP_NUM + 1],
        Rotation(rot_into_branch_init),
    );
    let mut rlp_byte2 = meta.query_advice(
        s_main.bytes[BRANCH_0_S_START - RLP_NUM + 2],
        Rotation(rot_into_branch_init),
    );

    if !is_s {
        rlp_byte0 = meta.query_advice(
            s_main.bytes[BRANCH_0_C_START - RLP_NUM],
            Rotation(rot_into_branch_init),
        );
        rlp_byte1 = meta.query_advice(
            s_main.bytes[BRANCH_0_C_START - RLP_NUM + 1],
            Rotation(rot_into_branch_init),
        );
        rlp_byte2 = meta.query_advice(
            s_main.bytes[BRANCH_0_C_START - RLP_NUM + 2],
            Rotation(rot_into_branch_init),
        );
    }

    let c256 = Expression::Constant(F::from(256_u64));
    one_rlp_byte * (rlp_byte0 - c192 + one.clone())
        + two_rlp_bytes * (rlp_byte1.clone() + one.clone() + one.clone())
        + three_rlp_bytes * (rlp_byte1 * c256 + rlp_byte2 + one.clone() + one.clone() + one)
}

pub(crate) fn get_leaf_len<F: FieldExt>(
    meta: &mut VirtualCells<F>,
    s_main: MainCols<F>,
    accs: AccumulatorCols<F>,
    rot_into_leaf_key: i32,
) -> Expression<F> {
    let one = Expression::Constant(F::from(1_u64));
    let c192 = Expression::Constant(F::from(192_u64));
    let flag1 = meta.query_advice(accs.s_mod_node_rlc, Rotation(rot_into_leaf_key));
    let flag2 = meta.query_advice(accs.c_mod_node_rlc, Rotation(rot_into_leaf_key));
    let is_leaf_long = flag1 * (one.clone() - flag2);

    let rlp1 = meta.query_advice(s_main.rlp1, Rotation(rot_into_leaf_key));
    let rlp2 = meta.query_advice(s_main.rlp2, Rotation(rot_into_leaf_key));

    is_leaf_long.clone() * (rlp2 + one.clone() + one.clone())
        + (one.clone() - is_leaf_long) * (rlp1 - c192 + one)
}
