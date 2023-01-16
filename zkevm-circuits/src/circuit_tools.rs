//! Circuit utilities

use crate::{
    evm_circuit::util::{rlc, scalar_mult},
    util::Expr,
};
use gadgets::util::{and, select, sum};
use halo2_proofs::{
    arithmetic::FieldExt,
    plonk::{Advice, Column, ConstraintSystem, Expression, VirtualCells},
    poly::Rotation,
};
use itertools::Itertools;

#[derive(Clone)]
pub(crate) struct DataTransition<F> {
    prev: Expression<F>,
    cur: Expression<F>,
}

impl<F: FieldExt> DataTransition<F> {
    pub(crate) fn new(meta: &mut VirtualCells<F>, column: Column<Advice>) -> DataTransition<F> {
        DataTransition {
            prev: meta.query_advice(column, Rotation::prev()),
            cur: meta.query_advice(column, Rotation::cur()),
        }
    }

    pub(crate) fn new_with_rot(
        meta: &mut VirtualCells<F>,
        column: Column<Advice>,
        rot_prev: i32,
        rot_cur: i32,
    ) -> DataTransition<F> {
        DataTransition {
            prev: meta.query_advice(column, Rotation(rot_prev)),
            cur: meta.query_advice(column, Rotation(rot_cur)),
        }
    }

    pub(crate) fn from(prev: Expression<F>, cur: Expression<F>) -> DataTransition<F> {
        DataTransition { prev, cur }
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

impl<F: FieldExt> Expr<F> for DataTransition<F> {
    fn expr(&self) -> Expression<F> {
        self.cur.clone()
    }
}

/// Lookup data
#[derive(Clone)]
pub struct LookupData<F> {
    /// Desciption
    pub description: &'static str,
    /// Lookup tag
    pub tag: String,
    /// Condition under which the lookup needs to be done
    pub condition: Expression<F>,
    /// The values to lookup
    pub values: Vec<Expression<F>>,
}

/// Constraint builder
pub struct ConstraintBuilder<F> {
    constraints: Vec<(&'static str, Expression<F>)>,
    max_degree: usize,
    conditions: Vec<Expression<F>>,
    /// The lookups
    pub lookups: Vec<LookupData<F>>,
    /// The lookup tables
    pub lookup_tables: Vec<LookupData<F>>,
}

impl<F: FieldExt> ConstraintBuilder<F> {
    pub(crate) fn new(max_degree: usize) -> Self {
        ConstraintBuilder {
            constraints: Vec::new(),
            max_degree,
            conditions: Vec::new(),
            lookups: Vec::new(),
            lookup_tables: Vec::new(),
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
        self.add_constraint(name, value.clone() * (1.expr() - value));
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

    pub(crate) fn generate_constraints(&self) -> Vec<(&'static str, Expression<F>)> {
        self.constraints.clone()
    }

    pub(crate) fn generate_lookups<S: AsRef<str>>(
        &self,
        meta: &mut ConstraintSystem<F>,
        lookup_names: &[S],
    ) {
        for lookup_name in lookup_names.iter() {
            let lookups = self
                .lookups
                .iter()
                .cloned()
                .filter(|lookup| lookup.tag == lookup_name.as_ref())
                .collect::<Vec<_>>();
            for lookup in lookups.iter() {
                meta.lookup_any(lookup.description, |_meta| {
                    let table = self.get_lookup_table(lookup_name);
                    let mut values: Vec<_> = lookup
                        .values
                        .iter()
                        .map(|value| lookup.condition.expr() * value.expr())
                        .collect();
                    assert!(table.len() >= values.len());
                    while values.len() < table.len() {
                        values.push(0.expr());
                    }
                    table
                        .iter()
                        .zip(values.iter())
                        .map(|(table, value)| (value.expr(), table.expr()))
                        .collect()
                });
            }
        }
    }

    pub(crate) fn get_condition(&self) -> Option<Expression<F>> {
        if self.conditions.is_empty() {
            None
        } else {
            Some(and::expr(self.conditions.iter()))
        }
    }

    pub(crate) fn get_condition_expr(&self) -> Expression<F> {
        self.get_condition().unwrap_or_else(|| 1.expr())
    }

    pub(crate) fn lookup_table(
        &mut self,
        description: &'static str,
        tag: String,
        values: Vec<Expression<F>>,
    ) {
        let condition = self.get_condition_expr();
        self.lookup_tables.push(LookupData {
            description,
            tag,
            condition,
            values,
        });
    }

    pub(crate) fn lookup(
        &mut self,
        description: &'static str,
        tag: String,
        values: Vec<Expression<F>>,
    ) {
        let condition = self.get_condition_expr();
        self.lookups.push(LookupData {
            description,
            tag,
            condition,
            values,
        });
    }

    pub(crate) fn get_lookup_table<S: AsRef<str>>(&self, tag: S) -> Vec<Expression<F>> {
        let lookups = self
            .lookup_tables
            .iter()
            .filter(|lookup| lookup.tag == tag.as_ref())
            .collect::<Vec<_>>();
        let selector = sum::expr(lookups.iter().map(|lookup| lookup.condition.expr()));

        let mut table = vec![0.expr(); lookups[0].values.len()];
        for (idx, value) in table.iter_mut().enumerate() {
            *value = sum::expr(
                lookups
                    .iter()
                    .map(|lookup| selector.expr() * lookup.values[idx].expr()),
            );
        }
        table
    }
}

pub(crate) fn select<F: FieldExt>(
    condition: Expression<F>,
    when_true: &[Expression<F>],
    when_false: &[Expression<F>],
) -> Vec<Expression<F>> {
    when_true
        .into_iter()
        .zip(when_false.into_iter())
        .map(|(when_true, when_false)| {
            select::expr(condition.expr(), when_true.expr(), when_false.expr())
        })
        .collect()
}

/// Trait that generates a vector of expressions
pub trait Expressable<F> {
    /// Returns a vector of the expressions from itself
    fn to_expr_vec(&self) -> Vec<Expression<F>>;
}

impl<F: FieldExt, E: Expressable<F>> Expressable<F> for Vec<E> {
    fn to_expr_vec(&self) -> Vec<Expression<F>> {
        self.iter()
            .map(|e| e.to_expr_vec()[0].expr())
            .collect::<Vec<_>>()
    }
}

impl<F: FieldExt, E: Expressable<F>> Expressable<F> for [E] {
    fn to_expr_vec(&self) -> Vec<Expression<F>> {
        self.iter()
            .map(|e| e.to_expr_vec()[0].expr())
            .collect::<Vec<_>>()
    }
}

impl<F: FieldExt, E: Expressable<F>> Expressable<F> for &[E] {
    fn to_expr_vec(&self) -> Vec<Expression<F>> {
        self.iter()
            .map(|e| e.to_expr_vec()[0].expr())
            .collect::<Vec<_>>()
    }
}

impl<F: FieldExt, E: Expressable<F>> Expressable<F> for (E, E) {
    fn to_expr_vec(&self) -> Vec<Expression<F>> {
        let mut res = self.0.to_expr_vec();
        res.append(&mut self.1.to_expr_vec());
        res
    }
}

impl<F: FieldExt, E: Expressable<F>> Expressable<F> for (E, E, E) {
    fn to_expr_vec(&self) -> Vec<Expression<F>> {
        let mut res = self.0.to_expr_vec();
        res.append(&mut self.1.to_expr_vec());
        res.append(&mut self.2.to_expr_vec());
        res
    }
}

impl<F: FieldExt, E: Expressable<F>> Expressable<F> for (E, E, E, E) {
    fn to_expr_vec(&self) -> Vec<Expression<F>> {
        let mut res = self.0.to_expr_vec();
        res.append(&mut self.1.to_expr_vec());
        res.append(&mut self.2.to_expr_vec());
        res.append(&mut self.3.to_expr_vec());
        res
    }
}

/// Implementation trait `Expressable` for type able to be casted to an
/// Expression
#[macro_export]
macro_rules! impl_expressable {
    ($type:ty) => {
        impl<F: halo2_proofs::arithmetic::FieldExt> Expressable<F> for $type {
            #[inline]
            fn to_expr_vec(&self) -> Vec<Expression<F>> {
                vec![self.expr()]
            }
        }
    };
}

impl_expressable!(bool);
impl_expressable!(u8);
impl_expressable!(i32);
impl_expressable!(u64);
impl_expressable!(usize);
impl_expressable!(Expression<F>);
impl_expressable!(DataTransition<F>);

/// Trait around select
pub trait Selectable<F> {
    /// Selects between itself and another value using the given condition
    fn select(&self, condition: Expression<F>, other: &Self) -> Self;
    /// Returns itself if the condition holds, else zero
    fn conditional(&self, condition: Expression<F>) -> Self;
    /// Adds 2 Selectable together
    fn add_expr(&self, other: &Self) -> Self;
    /// Creates a vector of Expressions representing itself
    fn to_vec(&self) -> Vec<Expression<F>>;
}

impl<F: FieldExt> Selectable<F> for () {
    fn select(&self, _condition: Expression<F>, _when_false: &Self) -> Self {
        ()
    }
    fn conditional(&self, _condition: Expression<F>) -> Self {
        ()
    }
    fn add_expr(&self, _other: &Self) -> Self {
        ()
    }
    fn to_vec(&self) -> Vec<Expression<F>> {
        vec![]
    }
}

impl<F: FieldExt> Selectable<F> for Expression<F> {
    fn select(&self, condition: Expression<F>, when_false: &Self) -> Self {
        gadgets::util::select::expr(condition, self.expr(), when_false.expr())
    }
    fn conditional(&self, condition: Expression<F>) -> Self {
        condition * self.expr()
    }
    fn add_expr(&self, other: &Self) -> Self {
        self.expr() + other.expr()
    }
    fn to_vec(&self) -> Vec<Expression<F>> {
        vec![self.expr()]
    }
}

/// Implementation trait `Expr` for type able to be casted to u64
#[macro_export]
macro_rules! impl_selectable {
    ($type:ty, $v:expr) => {
        impl<F: halo2_proofs::arithmetic::FieldExt> Selectable<F> for $type {
            fn select(&self, condition: Expression<F>, when_false: &Self) -> Self {
                select(condition, &self.to_vec(), &when_false.to_vec())
                    .into_iter()
                    .collect_tuple()
                    .unwrap()
            }
            fn conditional(&self, condition: Expression<F>) -> Self {
                self.to_vec()
                    .into_iter()
                    .map(|when_true| condition.expr() * when_true.expr())
                    .collect_tuple()
                    .unwrap()
            }
            fn add_expr(&self, other: &Self) -> Self {
                self.to_vec()
                    .iter()
                    .zip(other.to_vec().iter())
                    .map(|(a, b)| a.expr() + b.expr())
                    .collect_tuple()
                    .unwrap()
            }
            fn to_vec(&self) -> Vec<Expression<F>> {
                $v(self)
            }
        }
    };
}

impl_selectable!((Expression<F>, Expression<F>), |t: &(
    Expression<F>,
    Expression<F>
)| {
    vec![t.0.expr(), t.1.expr()]
});
impl_selectable!((Expression<F>, Expression<F>, Expression<F>), |t: &(
    Expression<F>,
    Expression<F>,
    Expression<F>
)| {
    vec![t.0.expr(), t.1.expr(), t.2.expr()]
});
impl_selectable!(
    (Expression<F>, Expression<F>, Expression<F>, Expression<F>),
    |t: &(Expression<F>, Expression<F>, Expression<F>, Expression<F>)| {
        vec![t.0.expr(), t.1.expr(), t.2.expr(), t.3.expr()]
    }
);
impl_selectable!(
    (
        Expression<F>,
        Expression<F>,
        Expression<F>,
        Expression<F>,
        Expression<F>
    ),
    |t: &(
        Expression<F>,
        Expression<F>,
        Expression<F>,
        Expression<F>,
        Expression<F>
    )| { vec![t.0.expr(), t.1.expr(), t.2.expr(), t.3.expr(), t.4.expr()] }
);

/// Trait that conditionally combines multiple types
pub trait Conditionable<F, E> {
    /// Conditionally combines multiple values
    fn apply_conditions(&self) -> E;
    /// Gets the list of all conditions
    fn get_conditions(&self) -> Vec<Expression<F>>;
    /// Gets the sum of all conditions
    fn sum_conditions(&self) -> Expression<F>;
}

impl<F: FieldExt, E: Selectable<F>> Conditionable<F, E> for Vec<(Expression<F>, E)> {
    fn apply_conditions(&self) -> E {
        let mut res = self[0].1.conditional(self[0].0.expr());
        for pair in self.iter().skip(1) {
            res = res.add_expr(&pair.1.conditional(pair.0.expr()));
        }
        res
    }

    fn get_conditions(&self) -> Vec<Expression<F>> {
        self.iter().map(|v| v.0.expr()).collect()
    }

    fn sum_conditions(&self) -> Expression<F> {
        sum::expr(&self.get_conditions())
    }
}

/// Trait around LRC
pub trait LRCable<F> {
    /// Returns the LRC of itself
    fn rlc(&self, r: &[Expression<F>]) -> Expression<F>;
    /// Returns the LRC of itself with a starting multiplier
    fn rlc_chain(&self, r: &[Expression<F>], mult: Expression<F>) -> Expression<F>;
}

impl<F: FieldExt, E: Expressable<F>> LRCable<F> for Vec<E> {
    fn rlc(&self, r: &[Expression<F>]) -> Expression<F> {
        rlc::expr(&self.to_expr_vec(), r)
    }

    fn rlc_chain(&self, r: &[Expression<F>], mult: Expression<F>) -> Expression<F> {
        rlc::expr(&scalar_mult::expr(&self.to_expr_vec(), mult.expr()), &r)
    }
}

/// Constraint builder macros
#[macro_export]
macro_rules! circuit {
    ([$meta:expr, $cb:expr], $content:block) => {{
        #[allow(unused_imports)]
        use gadgets::util::and;
        #[allow(unused_imports)]
        use crate::circuit_tools::Selectable;
        #[allow(unused_imports)]
        use crate::circuit_tools::Expressable;
        #[allow(unused_imports)]
        use crate::circuit_tools::Conditionable;
        // Nested macro's can't do repetition... (https://github.com/rust-lang/rust/issues/35853)
        #[allow(unused_macros)]
        macro_rules! ifx {
            ($condition:expr => $when_true:block elsex $when_false:block) => {{
                $cb.push_condition($condition.expr());
                let ret_true = $when_true;
                $cb.pop_condition();

                $cb.push_condition(not::expr($condition.expr()));
                let ret_false = $when_false;
                $cb.pop_condition();

                ret_true.select($condition.expr(), &ret_false)
            }};
            ($condition_a:expr, $condition_b:expr => $when_true:block elsex $when_false:block) => {{
                let condition = and::expr([$condition_a.expr(), $condition_b.expr()]);

                $cb.push_condition(condition.expr());
                let ret_true = $when_true;
                $cb.pop_condition();

                $cb.push_condition(not::expr(condition.expr()));
                let ret_false = $when_false;
                $cb.pop_condition();

                ret_true.select(condition.expr(), &ret_false)
            }};
            ($condition_a:expr, $condition_b:expr, $condition_c:expr => $when_true:block elsex $when_false:block) => {{
                let condition = and::expr([$condition_a.expr(), $condition_b.expr(), $condition_c.expr()]);

                $cb.push_condition(condition.expr());
                let ret_true = $when_true;
                $cb.pop_condition();

                $cb.push_condition(not::expr(condition.expr()));
                let ret_false = $when_false;
                $cb.pop_condition();

                ret_true.select(condition.expr(), &ret_false)
            }};
            ($condition_a:expr, $condition_b:expr, $condition_c:expr, $condition_d:expr => $when_true:block elsex $when_false:block) => {{
                let condition = and::expr([$condition_a.expr(), $condition_b.expr(), $condition_c.expr(), $condition_d.expr()]);

                $cb.push_condition(condition.expr());
                let ret_true = $when_true;
                $cb.pop_condition();

                $cb.push_condition(not::expr(condition.expr()));
                let ret_false = $when_false;
                $cb.pop_condition();

                ret_true.select(condition.expr(), &ret_false)
            }};

            ($condition:expr => $when_true:block) => {{
                $cb.push_condition($condition.expr());
                let ret_true = $when_true.clone();
                $cb.pop_condition();

                ret_true.conditional($condition.expr())
            }};
            ($condition_a:expr, $condition_b:expr => $when_true:block) => {{
                let condition = and::expr([$condition_a.expr(), $condition_b.expr()]);
                $cb.push_condition(condition.expr());
                let ret_true = $when_true.clone();
                $cb.pop_condition();

                ret_true.conditional(condition.expr())
            }};
            ($condition_a:expr, $condition_b:expr, $condition_c:expr => $when_true:block) => {{
                let condition = and::expr([$condition_a.expr(), $condition_b.expr(), $condition_c.expr()]);
                $cb.push_condition(condition.expr());
                let ret_true = $when_true.clone();
                $cb.pop_condition();

                ret_true.conditional(condition.expr())
            }};
            ($condition_a:expr, $condition_b:expr, $condition_c:expr, $condition_d:expr => $when_true:block) => {{
                let condition = and::expr([$condition_a.expr(), $condition_b.expr(), $condition_c.expr(), $condition_d.expr()]);
                $cb.push_condition(condition.expr());
                let ret_true = $when_true.clone();
                $cb.pop_condition();

                ret_true.conditional(condition.expr())
            }};
            ($condition_a:expr, $condition_b:expr, $condition_c:expr, $condition_d:expr, $condition_e:expr => $when_true:block) => {{
                let condition = and::expr([$condition_a.expr(), $condition_b.expr(), $condition_c.expr(), $condition_d.expr(), $condition_e.expr()]);
                $cb.push_condition(condition.expr());
                let ret_true = $when_true.clone();
                $cb.pop_condition();

                ret_true.conditional(condition.expr())
            }};
        }

        #[allow(unused_macros)]
        macro_rules! matchx {
            ($condition_a:expr => $when_a:expr,) => {{
                $cb.push_condition($condition_a.expr());
                let ret_a = $when_a.clone();
                $cb.pop_condition();

                require!($condition_a.expr() => 1);
                ret_a.conditional($condition_a.expr())
            }};
            ($condition_a:expr => $when_a:expr, $condition_b:expr => $when_b:expr,) => {{
                $cb.push_condition($condition_a.expr());
                let ret_a = $when_a.clone();
                $cb.pop_condition();

                $cb.push_condition($condition_b.expr());
                let ret_b = $when_b.clone();
                $cb.pop_condition();

                require!($condition_a.expr() + $condition_b.expr() => 1);
                vec![($condition_a.expr(), ret_a), ($condition_b.expr(), ret_b)].apply_conditions()
            }};
            ($condition_a:expr => $when_a:expr, $condition_b:expr => $when_b:expr, $condition_c:expr => $when_c:expr,) => {{
                $cb.push_condition($condition_a.expr());
                let ret_a = $when_a.clone();
                $cb.pop_condition();

                $cb.push_condition($condition_b.expr());
                let ret_b = $when_b.clone();
                $cb.pop_condition();

                $cb.push_condition($condition_c.expr());
                let ret_c = $when_c.clone();
                $cb.pop_condition();

                require!($condition_a.expr() + $condition_b.expr() + $condition_c.expr() => 1);
                vec![($condition_a.expr(), ret_a), ($condition_b.expr(), ret_b), ($condition_c.expr(), ret_c)].apply_conditions()
            }};
            ($condition_a:expr => $when_a:expr, $condition_b:expr => $when_b:expr, $condition_c:expr => $when_c:expr, $condition_d:expr => $when_d:expr,) => {{
                $cb.push_condition($condition_a.expr());
                let ret_a = $when_a.clone();
                $cb.pop_condition();

                $cb.push_condition($condition_b.expr());
                let ret_b = $when_b.clone();
                $cb.pop_condition();

                $cb.push_condition($condition_c.expr());
                let ret_c = $when_c.clone();
                $cb.pop_condition();

                $cb.push_condition($condition_d.expr());
                let ret_d = $when_d.clone();
                $cb.pop_condition();

                require!($condition_a.expr() + $condition_b.expr() + $condition_c.expr() + $condition_d.expr() => 1);
                vec![($condition_a.expr(), ret_a), ($condition_b.expr(), ret_b), ($condition_c.expr(), ret_c), ($condition_d.expr(), ret_d)].apply_conditions()
            }};
        }

        #[allow(unused_macros)]
        macro_rules! f {
            ($column:expr, $rot:expr) => {{
                $meta.query_fixed($column.clone(), Rotation($rot as i32))
            }};
            ($column:expr) => {{
                $meta.query_fixed($column.clone(), Rotation::cur())
            }};
        }

        #[allow(unused_macros)]
        macro_rules! a {
            ($column:expr, $rot:expr) => {{
                $meta.query_advice($column.clone(), Rotation($rot as i32))
            }};
            ($column:expr) => {{
                $meta.query_advice($column.clone(), Rotation::cur())
            }};
        }

        #[allow(unused_macros)]
        macro_rules! not {
            ($expr:expr) => {{
                gadgets::util::not::expr($expr.expr())
            }};
        }

        #[allow(unused_macros)]
        macro_rules! require {
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

            ($lhs:expr => $rhs:expr) => {{
                let rhs = $rhs.to_expr_vec();
                let description = concat!(
                    file!(),
                    ":",
                    line!(),
                    ": ",
                    stringify!($lhs),
                    " => ",
                    stringify!($rhs)
                );
                if rhs.len() == 1 {
                    $cb.require_equal(
                        description,
                        $lhs.expr(),
                        rhs[0].expr(),
                    );
                } else {
                    $cb.require_in_set(
                        description,
                        $lhs.expr(),
                        rhs.clone(),
                    );
                }
            }};
            ($name:expr, $lhs:expr => $rhs:expr) => {{
                let description = format!("{}:{}[{}]: {} => {}",  file!(), line!(), $name, stringify!($lhs), stringify!($rhs));
                let rhs = $rhs.to_expr_vec();
                if rhs.len() == 1 {
                    $cb.require_equal(
                        Box::leak(description.into_boxed_str()),
                        $lhs.expr(),
                        rhs[0].expr(),
                    );
                } else {
                    $cb.require_in_set(
                        Box::leak(description.into_boxed_str()),
                        $lhs.expr(),
                        rhs.clone(),
                    );
                }
            }};

            (($a:expr, $b:expr, $c:expr) => @$tag:expr) => {{
                $cb.lookup(
                    concat!(
                        file!(),
                        ":",
                        line!(),
                        ": (",
                        stringify!($a),
                        ", ",
                        stringify!($b),
                        ", ",
                        stringify!($c),
                        ") => @",
                        stringify!($tag),
                    ),
                    $tag.to_string(),
                    vec![$a.expr(), $b.expr(), $c.expr()],
                );
            }};

            (($a:expr, $b:expr, $c:expr, $d:expr) => @$tag:expr) => {{
                $cb.lookup(
                    concat!(
                        file!(),
                        ":",
                        line!(),
                        ": (",
                        stringify!($a),
                        ", ",
                        stringify!($b),
                        ", ",
                        stringify!($c),
                        ", ",
                        stringify!($d),
                        ") => @",
                        stringify!($tag),
                    ),
                    $tag.to_string(),
                    vec![$a.expr(), $b.expr(), $c.expr(), $d.expr()],
                );
            }};

            ($values:expr => @$tag:expr) => {{
                $cb.lookup(
                    concat!(
                        file!(),
                        ":",
                        line!(),
                        ": ",
                        stringify!($values),
                        " => @",
                        stringify!($tag),
                    ),
                    $tag.to_string(),
                    $values.clone(),
                );
            }};

            ($descr:expr, ($a:expr, $b:expr, $c:expr) => @$tag:expr) => {{
                $cb.lookup(
                    Box::leak($descr.into_boxed_str()),
                    $tag.to_string(),
                    vec![$a.expr(), $b.expr(), $c.expr()],
                );
            }};

            ($descr:expr, $values:expr => @$tag:expr) => {{
                $cb.lookup(
                    Box::leak($descr.into_boxed_str()),
                    $tag.to_string(),
                    $values.clone(),
                );
            }};

            (@$tag:expr => ($a:expr, $b:expr, $c:expr)) => {{
                $cb.lookup_table(
                    concat!(
                        file!(),
                        ":",
                        line!(),
                        ": @",
                        stringify!($tag),
                        " => (",
                        stringify!($a),
                        ", ",
                        stringify!($b),
                        ", ",
                        stringify!($c),
                        ")",
                    ),
                    $tag.to_string(),
                    vec![$a.expr(), $b.expr(), $c.expr()],
                );
            }};

            (@$tag:expr => $a:expr) => {{
                $cb.lookup_table(
                    concat!(
                        file!(),
                        ":",
                        line!(),
                        ": @",
                        stringify!($tag),
                        " => (",
                        stringify!($a),
                        ")",
                    ),
                    $tag.to_string(),
                    $a,
                );
            }};
        }

        $content
    }};
}
