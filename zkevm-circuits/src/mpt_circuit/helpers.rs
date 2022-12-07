use crate::util::Expr;
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
    addition: usize,
    key_len_col: Column<Advice>,
    mult_diff_col: Column<Advice>,
    key_len_offset: usize,
    fixed_table: [Column<Fixed>; 3],
) {
    meta.lookup_any("mult_diff_lookup", |meta| {
        let q_enable = q_enable(meta);
        let mut constraints = vec![];

        let offset = Expression::Constant(F::from(key_len_offset as u64));
        let key_len = meta.query_advice(key_len_col, Rotation::cur()) - offset;
        let mult_diff = meta.query_advice(mult_diff_col, Rotation::cur());
        let add_expr = Expression::Constant(F::from(addition as u64));

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

#[derive(Clone)]
pub(crate) struct ColumnTransition<F> {
    cur: Expression<F>,
    prev: Expression<F>,
}

impl<F: FieldExt> ColumnTransition<F> {
    pub(crate) fn new(meta: &mut VirtualCells<F>, column: Column<Advice>) -> ColumnTransition<F> {
        ColumnTransition {
            cur: meta.query_advice(column, Rotation::cur()),
            prev: meta.query_advice(column, Rotation::prev()),
        }
    }

    pub(crate) fn cur(&self) -> Expression<F> {
        self.cur.clone()
    }

    pub(crate) fn prev(&self) -> Expression<F> {
        self.prev.clone()
    }
}

impl<F: FieldExt> Expr<F> for ColumnTransition<F> {
    fn expr(&self) -> Expression<F> {
        self.cur.clone()
    }
}

#[derive(Default)]
pub struct BaseConstraintBuilder<F> {
    pub constraints: Vec<(&'static str, Expression<F>)>,
    pub max_degree: usize,
    pub conditions: Vec<Expression<F>>,
}

impl<F: FieldExt> BaseConstraintBuilder<F> {
    pub(crate) fn new(max_degree: usize) -> Self {
        BaseConstraintBuilder {
            constraints: Vec::new(),
            max_degree,
            conditions: Vec::new(),
        }
    }

    pub(crate) fn require_zero(&mut self, name: &'static str, constraint: Expression<F>) {
        self.add_constraint(name, constraint);
    }

    pub(crate) fn require_equal(
        &mut self,
        name: &'static str,
        lhs: Expression<F>,
        rhs: Expression<F>,
    ) {
        self.add_constraint(name, lhs - rhs);
    }

    pub(crate) fn require_boolean(&mut self, name: &'static str, value: Expression<F>) {
        self.add_constraint(name, value.clone() * (1u64.expr() - value));
    }

    pub(crate) fn require_in_set(
        &mut self,
        name: &'static str,
        value: Expression<F>,
        set: Vec<Expression<F>>,
    ) {
        self.add_constraint(
            name,
            set.iter()
                .fold(1.expr(), |acc, item| acc * (value.clone() - item.clone())),
        );
    }

    pub(crate) fn condition<R>(
        &mut self,
        condition: Expression<F>,
        constraint: impl FnOnce(&mut Self) -> R,
    ) -> R {
        self.conditions.push(condition);
        let ret = constraint(self);
        self.conditions.pop();
        ret
    }

    pub(crate) fn add_constraints(&mut self, constraints: Vec<(&'static str, Expression<F>)>) {
        for (name, constraint) in constraints {
            self.add_constraint(name, constraint);
        }
    }

    pub(crate) fn add_constraint(&mut self, name: &'static str, constraint: Expression<F>) {
        let constraint = if self.conditions.is_empty() {
            constraint
        } else {
            constraint
                * self
                    .conditions
                    .iter()
                    .fold(1.expr(), |acc, x| acc * x.clone())
        };
        self.validate_degree(constraint.degree(), name);
        self.constraints.push((name, constraint));
    }

    pub(crate) fn validate_degree(&self, degree: usize, name: &'static str) {
        if self.max_degree > 0 {
            debug_assert!(
                degree <= self.max_degree,
                "Expression {} degree too high: {} > {}",
                name,
                degree,
                self.max_degree,
            );
        }
    }

    pub(crate) fn gate(&self, selector: Expression<F>) -> Vec<(&'static str, Expression<F>)> {
        self.constraints
            .clone()
            .into_iter()
            .map(|(name, constraint)| (name, selector.clone() * constraint))
            .filter(|(name, constraint)| {
                self.validate_degree(constraint.degree(), name);
                true
            })
            .collect()
    }
}
