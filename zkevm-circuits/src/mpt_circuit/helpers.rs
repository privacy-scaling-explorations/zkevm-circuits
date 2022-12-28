use crate::util::Expr;
use gadgets::util::{and, not, select};
use halo2_proofs::{
    arithmetic::FieldExt,
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, VirtualCells},
    poly::Rotation,
};

use crate::{
    mpt_circuit::param::{
        HASH_WIDTH, IS_EXT_LONG_EVEN_C16_POS, IS_EXT_LONG_EVEN_C1_POS, IS_EXT_LONG_ODD_C16_POS,
        IS_EXT_LONG_ODD_C1_POS, IS_EXT_SHORT_C16_POS, IS_EXT_SHORT_C1_POS, RLP_NUM,
    },
    mpt_circuit::FixedTableTag,
};

use super::{
    columns::{AccumulatorCols, MainCols},
    param::{BRANCH_0_C_START, BRANCH_0_S_START},
};

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

    one_rlp_byte * (rlp_byte0 - c192 + one.clone())
        + two_rlp_bytes * (rlp_byte1.clone() + one.clone() + one.clone())
        + three_rlp_bytes * (rlp_byte1 * 256.expr() + rlp_byte2 + one.clone() + one.clone() + one)
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

pub(crate) fn get_rlp_meta_bytes<F: FieldExt>(
    meta: &mut VirtualCells<F>,
    s_main: MainCols<F>,
    is_s: bool,
    rot: Rotation,
) -> [Expression<F>; 2] {
    let (rlp_column_1, rlp_column_2) = if is_s {
        (s_main.rlp1, s_main.rlp2)
    } else {
        (s_main.bytes[0], s_main.bytes[1])
    };
    [
        meta.query_advice(rlp_column_1, rot),
        meta.query_advice(rlp_column_2, rot),
    ]
}

pub(crate) fn get_num_rlp_bytes<F: FieldExt>(
    meta: &mut VirtualCells<F>,
    s_main: MainCols<F>,
    is_s: bool,
    rot: Rotation,
) -> (Expression<F>, Expression<F>, Expression<F>) {
    let (rlp1, rlp2) = if is_s {
        (
            meta.query_advice(s_main.rlp1, rot),
            meta.query_advice(s_main.rlp2, rot),
        )
    } else {
        (
            meta.query_advice(s_main.bytes[0], rot),
            meta.query_advice(s_main.bytes[1], rot),
        )
    };
    let one_rlp_byte = and::expr([rlp1.expr(), rlp2.expr()]);
    let two_rlp_bytes = and::expr([rlp1.expr(), not::expr(rlp2.expr())]);
    let three_rlp_bytes = and::expr([not::expr(rlp1.expr()), rlp2.expr()]);
    (one_rlp_byte, two_rlp_bytes, three_rlp_bytes)
}

pub(crate) fn get_rlp_value_bytes<F: FieldExt>(
    meta: &mut VirtualCells<F>,
    s_main: MainCols<F>,
    is_s: bool,
    rot: Rotation,
) -> [Expression<F>; 3] {
    let rlp_offset = if is_s { 2 } else { 5 };
    let rlp1 = meta.query_advice(s_main.bytes[rlp_offset + 0], rot);
    let rlp2 = meta.query_advice(s_main.bytes[rlp_offset + 1], rot);
    let rlp3 = meta.query_advice(s_main.bytes[rlp_offset + 2], rot);
    [rlp1, rlp2, rlp3]
}

pub(crate) fn extend_rand<F: FieldExt>(r: &[Expression<F>]) -> Vec<Expression<F>> {
    [
        r.to_vec(),
        r.iter()
            .map(|v| r.last().unwrap().expr() * v.clone())
            .collect::<Vec<_>>(),
    ]
    .concat()
}

pub(crate) fn accumulate_rand<F: FieldExt>(rs: &[Expression<F>]) -> Vec<Expression<F>> {
    let mut r = Vec::new();
    let mut acc = 1.expr();
    for rs in rs.iter() {
        acc = acc.expr() * rs.expr();
        r.push(acc.expr());
    }
    r
}

#[derive(Clone)]
pub(crate) struct ColumnTransition<F> {
    prev: Expression<F>,
    cur: Expression<F>,
}

impl<F: FieldExt> ColumnTransition<F> {
    pub(crate) fn new(meta: &mut VirtualCells<F>, column: Column<Advice>) -> ColumnTransition<F> {
        ColumnTransition {
            prev: meta.query_advice(column, Rotation::prev()),
            cur: meta.query_advice(column, Rotation::cur()),
        }
    }

    pub(crate) fn new_with_rot(
        meta: &mut VirtualCells<F>,
        column: Column<Advice>,
        rot_prev: Rotation,
        rot_cur: Rotation,
    ) -> ColumnTransition<F> {
        ColumnTransition {
            prev: meta.query_advice(column, rot_prev),
            cur: meta.query_advice(column, rot_cur),
        }
    }

    pub(crate) fn from(prev: Expression<F>, cur: Expression<F>) -> ColumnTransition<F> {
        ColumnTransition { prev, cur }
    }

    pub(crate) fn cur(&self) -> Expression<F> {
        self.cur.clone()
    }

    pub(crate) fn prev(&self) -> Expression<F> {
        self.prev.clone()
    }

    pub(crate) fn delta(&self) -> Expression<F> {
        self.prev() - self.cur()
    }
}

impl<F: FieldExt> Expr<F> for ColumnTransition<F> {
    fn expr(&self) -> Expression<F> {
        self.cur.clone()
    }
}

pub struct KeccakLookup<F> {
    pub selector: Expression<F>,
    pub input_rlc: Expression<F>,
    pub input_len: Expression<F>,
    pub output_rlc: Expression<F>,
}

pub struct FixedLookup<F> {
    pub selector: Expression<F>,
    pub tag: Expression<F>,
    pub lhs: Expression<F>,
    pub rhs: Expression<F>,
}

#[derive(Default)]
pub struct BaseConstraintBuilder<F> {
    pub constraints: Vec<(&'static str, Expression<F>)>,
    pub max_degree: usize,
    pub conditions: Vec<Expression<F>>,
    pub keccak_lookups: Vec<(&'static str, KeccakLookup<F>)>,
    pub fixed_lookups: Vec<(&'static str, FixedLookup<F>)>,
}

impl<F: FieldExt> BaseConstraintBuilder<F> {
    pub(crate) fn new(max_degree: usize) -> Self {
        BaseConstraintBuilder {
            constraints: Vec::new(),
            max_degree,
            conditions: Vec::new(),
            keccak_lookups: Vec::new(),
            fixed_lookups: Vec::new(),
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

    pub(crate) fn require_true(&mut self, name: &'static str, expr: Expression<F>) {
        self.require_equal(name, expr, 1.expr());
    }

    pub(crate) fn require_false(&mut self, name: &'static str, expr: Expression<F>) {
        self.require_equal(name, expr, 0.expr());
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
        self.push_condition(condition);
        let ret = constraint(self);
        self.pop_condition();
        ret
    }

    pub(crate) fn if_else<R>(
        &mut self,
        condition: Expression<F>,
        when_true: impl FnOnce(&mut Self) -> R,
        when_false: impl FnOnce(&mut Self) -> R,
    ) -> R {
        self.push_condition(condition.clone());
        let ret_true = when_true(self);
        self.pop_condition();

        self.push_condition(not::expr(condition));
        let ret_false = when_false(self);
        self.pop_condition();

        ret_true
        //select::expr(condition, ret_true, ret_false)
    }

    pub(crate) fn push_condition(&mut self, condition: Expression<F>) {
        self.conditions.push(condition);
    }

    pub(crate) fn pop_condition(&mut self) {
        self.conditions.pop();
    }

    pub(crate) fn add_constraints(&mut self, constraints: Vec<(&'static str, Expression<F>)>) {
        for (name, constraint) in constraints {
            self.add_constraint(name, constraint);
        }
    }

    pub(crate) fn add_constraint(&mut self, name: &'static str, constraint: Expression<F>) {
        let constraint = match self.get_condition() {
            Some(condition) => condition * constraint,
            None => constraint,
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

    pub(crate) fn get_condition(&self) -> Option<Expression<F>> {
        if self.conditions.is_empty() {
            None
        } else {
            Some(and::expr(self.conditions.iter()))
        }
    }

    pub(crate) fn keccak_table_lookup(
        &mut self,
        name: &'static str,
        input_rlc: Expression<F>,
        input_len: Expression<F>,
        output_rlc: Expression<F>,
    ) {
        self.keccak_lookups.push((
            name,
            KeccakLookup {
                selector: self.get_condition().unwrap_or_else(|| 1.expr()),
                input_rlc,
                input_len,
                output_rlc,
            },
        ));
    }

    pub(crate) fn fixed_table_lookup(
        &mut self,
        name: &'static str,
        tag: Expression<F>,
        lhs: Expression<F>,
        rhs: Expression<F>,
    ) {
        self.fixed_lookups.push((
            name,
            FixedLookup {
                selector: self.get_condition().unwrap_or_else(|| 1.expr()),
                tag,
                lhs,
                rhs,
            },
        ));
    }
}

/// Constraint builder macros
#[macro_export]
macro_rules! cs {
    ([$cb:ident], ifx ($condition:expr) $when_true:block elsex $when_false:block) => {{
        $cb.condition($condition.expr(), |$cb| $when_true);
        $cb.condition(not::expr($condition.expr()), |$cb| $when_false);
    }};
    ([$cb:ident], ifx ($condition:expr) $when_true:block) => {{
        $cb.condition($condition.expr(), |$cb| $when_true);
    }};
    ([$meta:ident, $cb:ident], $column_lhs:ident@$rot_lhs:tt == $column_rhs:ident@$rot_rhs:tt) => {{
        $cb.require_equal(
            "equal",
            $meta.query_advice($column_lhs, Rotation($rot_lhs as i32)),
            $meta.query_advice($column_rhs, Rotation($rot_rhs as i32)),
        );
    }};
    ([$cb:ident], $lhs:block == $rhs:block) => {{
        $cb.require_equal(
            concat!(
                file!(),
                ":",
                line!(),
                ": ",
                stringify!($lhs),
                " == ",
                stringify!($rhs)
            ),
            $lhs.expr(),
            $rhs.expr(),
        );
    }};
}

/// Constraint builder macros
#[macro_export]
macro_rules! constraints {
    ([$meta:ident, $cb:ident], $content:block) => {{
        // Nested macro's can't do repitition... (https://github.com/rust-lang/rust/issues/35853)
        macro_rules! ifx {
            ($condition:expr => $when_true:block elsex $when_false:block) => {{
                $cb.push_condition($condition.expr());
                $when_true
                $cb.pop_condition();

                $cb.push_condition(not::expr($condition.expr()));
                $when_false
                $cb.pop_condition();
            }};
            ($condition_a:expr, $condition_b:expr => $when_true:block elsex $when_false:block) => {{
                let condition = and::expr([$condition_a.expr(), $condition_b.expr()]);

                $cb.push_condition(condition.expr());
                $when_true
                $cb.pop_condition();

                $cb.push_condition(not::expr(condition.expr()));
                $when_false
                $cb.pop_condition();
            }};
            ($condition_a:expr, $condition_b:expr, $condition_c:expr => $when_true:block elsex $when_false:block) => {{
                let condition = and::expr([$condition_a.expr(), $condition_b.expr(), $condition_c.expr()]);

                $cb.push_condition(condition.expr());
                $when_true
                $cb.pop_condition();

                $cb.push_condition(not::expr(condition.expr()));
                $when_false
                $cb.pop_condition();
            }};
            ($condition_a:expr, $condition_b:expr, $condition_c:expr, $condition_d:expr => $when_true:block elsex $when_false:block) => {{
                let condition = and::expr([$condition_a.expr(), $condition_b.expr(), $condition_c.expr(), $condition_d.expr()]);

                $cb.push_condition(condition.expr());
                $when_true
                $cb.pop_condition();

                $cb.push_condition(not::expr(condition.expr()));
                $when_false
                $cb.pop_condition();
            }};


            ($condition:expr => $when_true:block) => {{
                $cb.push_condition($condition.expr());
                $when_true
                $cb.pop_condition();
            }};
            ($condition_a:expr, $condition_b:expr => $when_true:block) => {{
                let condition = and::expr([$condition_a.expr(), $condition_b.expr()]);
                $cb.push_condition(condition.expr());
                $when_true
                $cb.pop_condition();
            }};
            ($condition_a:expr, $condition_b:expr, $condition_c:expr => $when_true:block) => {{
                let condition = and::expr([$condition_a.expr(), $condition_b.expr(), $condition_c.expr()]);
                $cb.push_condition(condition.expr());
                $when_true
                $cb.pop_condition();
            }};
            ($condition_a:expr, $condition_b:expr, $condition_c:expr, $condition_d:expr => $when_true:block) => {{
                let condition = and::expr([$condition_a.expr(), $condition_b.expr(), $condition_c.expr(), $condition_d.expr()]);
                $cb.push_condition(condition.expr());
                $when_true
                $cb.pop_condition();
            }};
            ($condition_a:expr, $condition_b:expr, $condition_c:expr, $condition_d:expr, $condition_e:expr => $when_true:block) => {{
                let condition = and::expr([$condition_a.expr(), $condition_b.expr(), $condition_c.expr(), $condition_d.expr(), $condition_e.expr()]);
                $cb.push_condition(condition.expr());
                $when_true
                $cb.pop_condition();
            }};
        }

        macro_rules! selectx {
            ($condition:expr => $when_true:block elsex $when_false:block) => {{
                $cb.push_condition($condition.expr());
                let ret_true = $when_true.expr();
                $cb.pop_condition();

                $cb.push_condition(not::expr($condition.expr()));
                let ret_false = $when_false.expr();
                $cb.pop_condition();

                select::expr($condition.expr(), ret_true, ret_false)
            }};
            ($condition:expr => $when_true:block) => {{
                $cb.push_condition($condition.expr());
                let ret_true = $when_true.expr();
                $cb.pop_condition();

                $condition.expr() * ret_true
            }};
        }

        macro_rules! f {
            ($column:expr, $rot:expr) => {{
                $meta.query_fixed($column.clone(), Rotation($rot as i32))
            }};
            ($column:expr) => {{
                $meta.query_fixed($column.clone(), Rotation::cur())
            }};
        }

        macro_rules! a {
            ($column:expr, $rot:expr) => {{
                $meta.query_advice($column.clone(), Rotation($rot as i32))
            }};
            ($column:expr) => {{
                $meta.query_advice($column.clone(), Rotation::cur())
            }};
        }

        macro_rules! require {
            ($lhs:expr => $rhs:block) => {{
                $cb.require_in_set(
                    concat!(
                        file!(),
                        ":",
                        line!(),
                        ": ",
                        stringify!($lhs),
                        " in ",
                        stringify!($rhs),
                    ),
                    $lhs.expr(),
                    $rhs.to_vec(),
                );
            }};
            ($name:ident, $lhs:expr => $rhs:block) => {{
                let descr = format!("{}:{}[{}]: {} => {{{}}}",  file!(), line!(), $name, stringify!($lhs), stringify!($rhs));
                $cb.require_in_set(
                    Box::leak(descr.into_boxed_str()),
                    $lhs.expr(),
                    $rhs.to_vec(),
                );
            }};

            ($lhs:expr => bool) => {{
                $cb.require_boolean(
                    concat!(
                        file!(),
                        ":",
                        line!(),
                        ": ",
                        stringify!($lhs),
                        " in ",
                        stringify!($rhs),
                    ),
                    $lhs.expr(),
                );
            }};

            (($input_rlc:expr, $input_len:expr, $output_rlc:expr) => @keccak) => {{
                $cb.keccak_table_lookup(
                    concat!(
                        file!(),
                        ":",
                        line!(),
                        ": (",
                        stringify!($input_rlc),
                        ", ",
                        stringify!($input_len),
                        ", ",
                        stringify!($output_rlc),
                        ") => @keccak",
                    ),
                    $input_rlc.expr(),
                    $input_len.expr(),
                    $output_rlc.expr(),
                );
            }};

            (($tag:expr, $lhs:expr, $rhs:expr) => @fixed) => {{
                $cb.fixed_table_lookup(
                    concat!(
                        file!(),
                        ":",
                        line!(),
                        ": (",
                        stringify!($tag),
                        ", ",
                        stringify!($lhs),
                        ", ",
                        stringify!($rhs),
                        ") => @fixed",
                    ),
                    ($tag as u64).expr(),
                    $lhs.expr(),
                    $rhs.expr(),
                );
            }};
            (($tag:expr, $lhs:expr) => @fixed) => {{
                $cb.fixed_table_lookup(
                    concat!(
                        file!(),
                        ":",
                        line!(),
                        ": (",
                        stringify!($tag),
                        ", ",
                        stringify!($lhs),
                        ") => @fixed",
                    ),
                    ($tag as u64).expr(),
                    $lhs.expr(),
                    0.expr(),
                );
            }};

            ($lhs:expr => $rhs:expr) => {{
                $cb.require_equal(
                    concat!(
                        file!(),
                        ":",
                        line!(),
                        ": ",
                        stringify!($lhs),
                        " == ",
                        stringify!($rhs)
                    ),
                    $lhs.expr(),
                    $rhs.expr(),
                );
            }};
            ($name:expr, $lhs:expr => $rhs:expr) => {{
                let descr = format!("{}:{}[{}]: {} == {}",  file!(), line!(), $name, stringify!($lhs), stringify!($rhs));
                $cb.require_equal(
                    Box::leak(descr.into_boxed_str()),
                    $lhs.expr(),
                    $rhs.expr(),
                );
            }};
        }

        $content
    }};
}
