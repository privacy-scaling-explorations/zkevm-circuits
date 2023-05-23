//! Circuit utilities
use std::ops::{Add, Mul};

use crate::{evm_circuit::util::rlc, util::Expr};
use eth_types::Field;
use gadgets::util::{and, sum, Scalar};
use halo2_proofs::plonk::{ConstraintSystem, Expression};
use itertools::Itertools;

use super::cell_manager::{Cell, CellManager_, CellTypeTrait, EvmCellType};

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
#[derive(Clone)]
pub struct ConstraintBuilder<F, C: CellTypeTrait> {
    constraints: Vec<(&'static str, Expression<F>)>,
    max_degree: usize,
    conditions: Vec<Expression<F>>,
    /// The lookups
    pub lookups: Vec<LookupData<F>>,
    /// The lookup tables
    pub lookup_tables: Vec<LookupData<F>>,
    /// CellManager
    pub cell_manager: Option<CellManager_<F, C>>,
}

impl<F: Field, C: CellTypeTrait> ConstraintBuilder<F, C> {
    pub(crate) fn new(max_degree: usize, cell_manager: Option<CellManager_<F, C>>) -> Self {
        ConstraintBuilder {
            constraints: Vec::new(),
            max_degree,
            conditions: Vec::new(),
            lookups: Vec::new(),
            lookup_tables: Vec::new(),
            cell_manager,
        }
    }

    pub(crate) fn set_cell_manager(&mut self, cell_manager: CellManager_<F, C>) {
        self.cell_manager = Some(cell_manager);
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

    // Query

    pub(crate) fn query_bool(&mut self) -> Cell<F> {
        let cell = self.query_default();
        self.require_boolean("Constrain cell to be a bool", cell.expr());
        cell
    }

    pub(crate) fn query_default(&mut self) -> Cell<F> {
        self.query_cells_dyn(C::default(), 1)
            .get(0)
            .expect("No cell found")
            .clone()
    }

    pub(crate) fn query_one(&mut self, cell_type: C) -> Cell<F> {
        self.query_cells_dyn(cell_type, 1).first().unwrap().clone()
    }

    pub(crate) fn query_bytes<const N: usize>(&mut self) -> [Cell<F>; N] {
        // Your own definition of CellType::Byte
        self.query_cells_dyn(
            C::byte_type().expect("No byte type for this CellManager"), 
            N
            ).try_into()
            .unwrap()
    }

    pub(crate) fn query_cells_dyn(&mut self, cell_type: C, count: usize) -> Vec<Cell<F>> {
        self.cell_manager
            .as_mut()
            .expect("Cell manager not set")
            .query_cells(cell_type, count)
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
        // 这里没有
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
                    let table = self.get_lookup_table_values(lookup_name);
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

    pub(crate) fn lookup_table<S: AsRef<str>>(
        &mut self,
        description: &'static str,
        tag: S,
        values: Vec<Expression<F>>,
    ) {
        let condition = self.get_condition_expr();
        self.lookup_tables.push(LookupData {
            description,
            tag: tag.as_ref().to_owned(),
            condition,
            values,
        });
    }

    pub(crate) fn lookup<S: AsRef<str>>(
        &mut self,
        description: &'static str,
        tag: S,
        values: Vec<Expression<F>>,
    ) {
        let condition = self.get_condition_expr();
        self.lookups.push(LookupData {
            description,
            tag: tag.as_ref().to_owned(),
            condition,
            values,
        });
    }

    pub(crate) fn get_lookups<S: AsRef<str>>(&self, tags: &[S]) -> Vec<LookupData<F>> {
        self.lookups
            .iter()
            .cloned()
            .filter(|lookup| tags.iter().any(|tag| lookup.tag == tag.as_ref()))
            .collect::<Vec<_>>()
    }

    pub(crate) fn consume_lookups<S: AsRef<str>>(&mut self, tags: &[S]) -> Vec<LookupData<F>> {
        let lookups = self.get_lookups(tags);
        self.lookups
            .retain(|lookup| tags.iter().any(|tag| lookup.tag != tag.as_ref()));
        lookups
    }

    pub(crate) fn get_lookup_table<S: AsRef<str>>(
        &self,
        tag: S,
    ) -> (Expression<F>, Vec<Expression<F>>) {
        let lookups = self
            .lookup_tables
            .iter()
            .filter(|lookup| lookup.tag == tag.as_ref())
            .collect::<Vec<_>>();

        merge_values_unsafe(
            lookups
                .iter()
                .map(|lookup| (lookup.condition.clone(), lookup.values.clone()))
                .collect::<Vec<_>>(),
        )
    }

    pub(crate) fn get_lookup_table_values<S: AsRef<str>>(&self, tag: S) -> Vec<Expression<F>> {
        let lookup_table = self.get_lookup_table(tag);
        // Combine with the merged selector as well
        lookup_table
            .1
            .iter()
            .map(|v| v.expr() * lookup_table.0.expr())
            .collect::<Vec<_>>()
    }

    pub(crate) fn generate_lookup_table_checks<S: AsRef<str>>(&mut self, tag: S) {
        let lookups = self
            .lookup_tables
            .iter()
            .filter(|lookup| lookup.tag == tag.as_ref())
            .collect::<Vec<_>>();
        let selectors = lookups
            .iter()
            .map(|lookup| lookup.condition.expr())
            .collect::<Vec<_>>();
        for selector in selectors.iter() {
            self.require_boolean(
                "lookup table condition needs to be boolean",
                selector.expr(),
            );
        }
        let selector = sum::expr(&selectors);
        self.require_boolean(
            "lookup table conditions sum needs to be boolean",
            selector.expr(),
        );
    }

    pub(crate) fn print_stats(&self) {
        let mut expressions = self.constraints.clone();
        expressions.sort_by(|a, b| a.1.degree().cmp(&b.1.degree()));
        for (name, expr) in expressions.iter() {
            println!("'{}': {}", name, expr.degree());
        }
    }
}

pub(crate) fn merge_lookups<F: Field, C: CellTypeTrait>(
    cb: &mut ConstraintBuilder<F, C>,
    lookups: Vec<LookupData<F>>,
) -> (Expression<F>, Vec<Expression<F>>) {
    merge_values(
        cb,
        lookups
            .iter()
            .map(|lookup| (lookup.condition.clone(), lookup.values.clone()))
            .collect::<Vec<_>>(),
    )
}

pub(crate) fn merge_values<F: Field, C: CellTypeTrait>(
    cb: &mut ConstraintBuilder<F, C>,
    values: Vec<(Expression<F>, Vec<Expression<F>>)>,
) -> (Expression<F>, Vec<Expression<F>>) {
    let selector = sum::expr(values.iter().map(|(condition, _)| condition.expr()));
    crate::circuit!([meta, cb], {
        require!(selector => bool);
    });
    merge_values_unsafe(values)
}

pub(crate) fn merge_values_unsafe<F: Field>(
    values: Vec<(Expression<F>, Vec<Expression<F>>)>,
) -> (Expression<F>, Vec<Expression<F>>) {
    if values.is_empty() {
        return (0.expr(), Vec::new());
    }
    let selector = sum::expr(values.iter().map(|(condition, _)| condition.expr()));
    // Merge
    let max_length = values.iter().map(|(_, values)| values.len()).max().unwrap();
    let mut merged_values = vec![0.expr(); max_length];
    let default_value = 0.expr();
    for (idx, value) in merged_values.iter_mut().enumerate() {
        *value = sum::expr(values.iter().map(|(condition, values)| {
            condition.expr() * values.get(idx).unwrap_or(&default_value).expr()
        }));
    }
    (selector, merged_values)
}

/// General trait to convert to a vec
pub trait ToVec<T: Clone> {
    /// Converts a tuple to a vector
    fn to_vec(&self) -> Vec<T>;
}

impl<T: Clone> ToVec<T> for Vec<T> {
    fn to_vec(&self) -> Vec<T> {
        self.clone()
    }
}

impl<T: Clone> ToVec<T> for [T] {
    fn to_vec(&self) -> Vec<T> {
        self.to_owned()
    }
}

impl<T: Clone> ToVec<T> for &[T] {
    fn to_vec(&self) -> Vec<T> {
        self.clone().to_owned()
    }
}

macro_rules! impl_to_vec {
    (($($t:ty),*), ($($v:ident),*)) => {
        impl<T: Clone> ToVec<T> for ($($t,)*) {
            fn to_vec(&self) -> Vec<T> {
                let ($($v,)*) = self;
                vec![$($v.clone()),*]
            }
        }
    };
}

impl_to_vec!((T, T), (a, b));
impl_to_vec!((T, T, T), (a, b, c));
impl_to_vec!((T, T, T, T), (a, b, c, d));
impl_to_vec!((T, T, T, T, T), (a, b, c, d, e));
impl_to_vec!((T, T, T, T, T, T), (a, b, c, d, e, f));
impl_to_vec!((T, T, T, T, T, T, T), (a, b, c, d, e, f, g));
impl_to_vec!((T, T, T, T, T, T, T, T), (a, b, c, d, e, f, g, h));

/// Trait that generates a vector of expressions
pub trait ExprVec<F> {
    /// Returns a vector of the expressions from itself
    fn to_expr_vec(&self) -> Vec<Expression<F>>;
}

impl<F: Field> ExprVec<F> for std::ops::Range<isize> {
    fn to_expr_vec(&self) -> Vec<Expression<F>> {
        self.clone().map(|e| e.expr()).collect::<Vec<_>>()
    }
}

impl<F: Field, E: Expr<F>> ExprVec<F> for Vec<E> {
    fn to_expr_vec(&self) -> Vec<Expression<F>> {
        self.iter().map(|e| e.expr()).collect::<Vec<_>>()
    }
}

impl<F: Field, E: Expr<F>> ExprVec<F> for [E] {
    fn to_expr_vec(&self) -> Vec<Expression<F>> {
        self.iter().map(|e| e.expr()).collect::<Vec<_>>()
    }
}

impl<F: Field, E: Expr<F>> ExprVec<F> for &[E] {
    fn to_expr_vec(&self) -> Vec<Expression<F>> {
        self.iter().map(|e| e.expr()).collect::<Vec<_>>()
    }
}

/// Implementation trait `ExprVec` for type able to be casted to an
/// Expression
#[macro_export]
macro_rules! impl_expr_vec {
    ($type:ty) => {
        impl<F: eth_types::Field> ExprVec<F> for $type {
            #[inline]
            fn to_expr_vec(&self) -> Vec<Expression<F>> {
                vec![self.expr()]
            }
        }
    };
}

impl_expr_vec!(bool);
impl_expr_vec!(u8);
impl_expr_vec!(i32);
impl_expr_vec!(u64);
impl_expr_vec!(usize);
impl_expr_vec!(isize);
impl_expr_vec!(Expression<F>);
impl_expr_vec!(Cell<F>);

/// Newtype wrapper for `Vec<Expression<F>>`
#[derive(Clone)]
pub struct ExpressionVec<F: Field>(pub Vec<Expression<F>>);

impl<F: Field> Add for ExpressionVec<F> {
    type Output = ExpressionVec<F>;

    fn add(self, rhs: ExpressionVec<F>) -> Self::Output {
        ExpressionVec(
            self.0
                .iter()
                .zip(rhs.0.iter())
                .map(|(a, b)| a.expr() + b.expr())
                .collect(),
        )
    }
}

impl<F: Field> Mul for ExpressionVec<F> {
    type Output = ExpressionVec<F>;

    fn mul(self, rhs: ExpressionVec<F>) -> Self::Output {
        ExpressionVec(
            self.0
                .iter()
                .zip(rhs.0.iter())
                .map(|(a, b)| a.expr() * b.expr())
                .collect(),
        )
    }
}

/// Trait for doing math on Expressions, no matter the type they are stored in
pub trait ExprResult<F> {
    /// Adds two values together
    fn add(&self, other: &Self) -> Self;
    /// Multiply with a scalar
    fn mul(&self, other: &Expression<F>) -> Self;
}

impl<F: Field> ExprResult<F> for () {
    fn add(&self, _other: &Self) -> Self {
        
    }
    fn mul(&self, _other: &Expression<F>) -> Self {
        
    }
}

impl<F: Field> ExprResult<F> for Vec<Expression<F>> {
    fn add(&self, other: &Self) -> Self {
        (ExpressionVec(self.clone()) + ExpressionVec(other.clone())).0
    }
    fn mul(&self, other: &Expression<F>) -> Self {
        (ExpressionVec(self.clone()) * ExpressionVec(vec![other.clone(); self.len()])).0
    }
}

impl<F: Field> ExprResult<F> for Expression<F> {
    fn add(&self, other: &Self) -> Self {
        vec![self.clone()].add(&vec![other.clone()])[0].clone()
    }
    fn mul(&self, other: &Expression<F>) -> Self {
        vec![self.clone()].mul(other)[0].clone()
    }
}

/// Implement `ExprResult` for tupples
#[macro_export]
macro_rules! impl_expr_result {
    ($($type:ty),*) => {
        impl<F: eth_types::Field> ExprResult<F> for ($($type),*) {
            fn add(&self, other: &Self) -> Self {
                self.to_vec().add(&other.to_vec()).into_iter().collect_tuple().unwrap()
            }
            fn mul(&self, other: &Expression<F>) -> Self {
                self.to_vec().mul(other).into_iter().collect_tuple().unwrap()
            }
        }
    };
}

impl_expr_result!(Expression<F>, Expression<F>);
impl_expr_result!(Expression<F>, Expression<F>, Expression<F>);
impl_expr_result!(Expression<F>, Expression<F>, Expression<F>, Expression<F>);
impl_expr_result!(
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>
);
impl_expr_result!(
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>
);
impl_expr_result!(
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>
);
impl_expr_result!(
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>,
    Expression<F>
);

/// Trait around RLC
pub trait RLCable<F: Field> {
    /// Returns the RLC of itself
    fn rlc(&self, r: &Expression<F>) -> Expression<F>;
}

impl<F: Field, E: ExprVec<F> + ?Sized> RLCable<F> for E {
    fn rlc(&self, r: &Expression<F>) -> Expression<F> {
        rlc::expr(&self.to_expr_vec(), r.expr())
    }
}

/// Trait around RLC
pub trait RLCChainable<F> {
    /// Returns the RLC of itself with a starting rlc/multiplier
    fn rlc_chain(&self, other: Expression<F>) -> Expression<F>;
}

impl<F: Field> RLCChainable<F> for (Expression<F>, Expression<F>) {
    fn rlc_chain(&self, other: Expression<F>) -> Expression<F> {
        self.0.expr() + self.1.expr() * other.expr()
    }
}

/// Trait around RLC
pub trait RLCableValue<F> {
    /// Returns the RLC of itself
    fn rlc_value(&self, r: F) -> F;
}

impl<F: Field> RLCableValue<F> for Vec<u8> {
    fn rlc_value(&self, r: F) -> F {
        rlc::value(self, r)
    }
}

impl<F: Field> RLCableValue<F> for [u8] {
    fn rlc_value(&self, r: F) -> F {
        rlc::value(self, r)
    }
}

/// Trait around RLC
pub trait RLCChainableValue<F, S, I> {
    /// Returns the RLC of itself with a starting rlc/multiplier
    fn rlc_chain_value(&self, values: I, r: F) -> (F, F);
}

impl<F: Field, S: Scalar<F>, I: IntoIterator<Item = S>> RLCChainableValue<F, S, I> for (F, F) {
    fn rlc_chain_value(&self, values: I, r: F) -> (F, F) {
        let mut rlc = self.0;
        let mut mult = self.1;
        for value in values.into_iter().map(|byte| byte.scalar()) {
            rlc += value * mult;
            mult *= r;
        }
        (rlc, mult)
    }
}

/// require_parser
#[macro_export]
macro_rules! require_parser {
    {
        $cb:expr,
        lhs = ($($lhs:tt)*)
        rest = (== $($rhs:tt)*)
    } => {
        let description = $crate::concat_with_preamble!(
            stringify!($($lhs)*),
            " == ",
            stringify!($($rhs)*)
        );
        $crate::_require!($cb, description, $($lhs)* => $($rhs)*)
    };

    {
        $cb:expr,
        lhs = ($($lhs:tt)*)
        rest = ($next:tt $($rest:tt)*)
    } => {
        $crate::require_parser! {
            $cb,
            lhs = ($($lhs)* $next)
            rest = ($($rest)*)
        }
    };
}

/// _require2
#[macro_export]
macro_rules! _require2 {
    ($cb:expr, $($rest:tt)*) => {{
        $crate::require_parser! {
            $cb,
            lhs = ()
            rest = ($($rest)*)
        }
    }};
}

/// Creates a dummy constraint builder that cannot be used to add constraints.
#[macro_export]
macro_rules! _cb {
    () => {{
        ConstraintBuilder::<F, T>::new(0, None)
    }};
}

/// Concats arguments with preamble consisting of the originating file and line.
#[macro_export]
macro_rules! concat_with_preamble {
    ($($args:expr),* $(,)?) => {{
        concat!(
            file!(),
            ":",
            line!(),
            ": ",
            $(
                $args,
            )*
        )
    }};
}

/// Can be used to mark a specific branch as unreachable
#[macro_export]
macro_rules! _unreachablex {
    ($cb:expr $(,$descr:expr)?) => {{
        let descr = concat_with_preamble!(
            "unreachable executed",
            $(
                ": ",
                $descr,
            )*
        );
        _require!($cb, descr, true => false)
    }};
}

/// _require
#[macro_export]
macro_rules! _require {
    ($cb:expr, $lhs:expr => bool) => {{
        $cb.require_boolean(
            concat_with_preamble!(
                stringify!($lhs),
                " => ",
                "bool",
            ),
            $lhs.expr(),
        );
    }};

    ($cb:expr, $lhs:expr => $rhs:expr) => {{
        let description = concat_with_preamble!(
            stringify!($lhs),
            " => ",
            stringify!($rhs)
        );
        _require!($cb, description, $lhs => $rhs)
    }};

    ($cb:expr, $descr:expr, $lhs:expr => $rhs:expr) => {{
        let rhs = $rhs.to_expr_vec();
        if rhs.len() == 1 {
            $cb.require_equal(
                Box::leak($descr.to_string().into_boxed_str()),
                $lhs.expr(),
                rhs[0].expr(),
            );
        } else {
            $cb.require_in_set(
                Box::leak($descr.to_string().into_boxed_str()),
                $lhs.expr(),
                rhs.clone(),
            );
        }
    }};

    // Lookup using a tuple
    ($cb:expr, ($($v:expr),+) => @$tag:expr) => {{
        $cb.lookup(
            concat_with_preamble!(
                "(",
                $(
                    stringify!($v),
                    ", ",
                )*
                ") => @",
                stringify!($tag),
            ),
            $tag.to_string(),
            vec![$($v.expr(),)*],
        );
    }};
    ($cb:expr, $descr:expr, ($($v:expr),+)  => @$tag:expr) => {{
        $cb.lookup(
            Box::leak($descr.into_boxed_str()),
            $tag.to_string(),
            vec![$($v.expr(),)*],
        );
    }};

    // Lookup using an array
    ($cb:expr, $values:expr => @$tag:expr) => {{
        $cb.lookup(
            concat_with_preamble!(
                stringify!($values),
                " => @",
                stringify!($tag),
            ),
            $tag.to_string(),
            $values.clone(),
        );
    }};
    ($cb:expr, $descr:expr, $values:expr => @$tag:expr) => {{
        $cb.lookup(
            Box::leak($descr.to_string().into_boxed_str()),
            $tag.to_string(),
            $values.clone(),
        );
    }};

    // Put values in a lookup table using a tuple
    ($cb:expr, @$tag:expr => ($($v:expr),+)) => {{
        $cb.lookup_table(
            concat_with_preamble!(
                "@",
                stringify!($tag),
                " => (",
                $(
                    stringify!($v),
                    ", ",
                )*
                ")",
            ),
            $tag.to_string(),
            vec![$($v.expr(),)*],
        );
    }};
    // Put values in a lookup table using an array
    ($cb:expr, @$tag:expr => $values:expr) => {{
        $cb.lookup_table(
            concat_with_preamble!(
                "@",
                stringify!($tag),
                " => (",
                stringify!($values),
                ")",
            ),
            $tag.to_string(),
            $values,
        );
    }};
}

/// matchx
/// Supports `_` which works the same as in the normal `match`: if none of the
/// other arms are active the `_` arm will be executed and so can be used to
/// return some default values or could also be marked as unreachable (using the
/// unreachablex! macro).
#[macro_export]
macro_rules! _matchx {
    ($cb:expr, $($condition:expr => $when:expr),* $(, _ => $catch_all:expr)? $(,)?)  => {{
        let mut conditions = Vec::new();
        let mut cases = Vec::new();
        $(
            $cb.push_condition($condition.expr());
            let ret = $when.clone();
            $cb.pop_condition();
            cases.push(($condition.expr(), ret));
            conditions.push($condition.expr());
        )*

        $(
            let catch_all_condition = not::expr(sum::expr(&conditions));
            $cb.push_condition(catch_all_condition.expr());
            let ret = $catch_all;
            $cb.pop_condition();
            cases.push((catch_all_condition.expr(), ret));
            conditions.push(catch_all_condition.expr());
        )*

        // All conditions need to be boolean
        for condition in conditions.iter() {
            _require!($cb, condition => bool);
        }
        // Exactly 1 case needs to be enabled
        _require!($cb, sum::expr(&conditions) => 1);

        // Apply the conditions to all corresponding values
        let mut res = cases[0].1.mul(&cases[0].0.expr());
        for pair in cases.iter().skip(1) {
            res = <_ as ExprResult<F>>::add(&res, &pair.1.mul(&pair.0.expr()));
        }
        res
    }};
}

/// ifx
#[macro_export]
macro_rules! _ifx {
    ($cb:expr, $($condition:expr),* => $when_true:block $(elsex $when_false:block)?)  => {{
        let condition = and::expr([$($condition.expr()),*]);

        $cb.push_condition(condition.expr());
        let ret_true = $when_true;
        $cb.pop_condition();

        #[allow(unused_assignments, unused_mut)]
        let mut ret = ret_true.mul(&condition.expr());
        $(
            // In if/else cases, the condition needs to be boolean
            _require!($cb, condition => bool);

            $cb.push_condition(not::expr(condition.expr()));
            let ret_false = $when_false;
            $cb.pop_condition();

            ret = <_ as ExprResult<F>>::add(&ret_true.mul(&condition), &ret_false.mul(&not::expr(condition.expr())));
        )*
        ret
    }};
}

/// matchw - Resembles matchx so that the witness generation can look like the
/// circuit code.
#[macro_export]
macro_rules! matchw {
    ($($condition:expr => $when:expr),* $(, _ => $catch_all:expr)? $(,)?)  => {{
        if false {
            unreachable!()
        }
        $(else if $condition {
            $when
        }
        )*
        else {
            $(
                $catch_all
            )*
            unreachable!()
        }
    }};
}

/// assign advice
#[macro_export]
macro_rules! assign {
    // Column
    ($region:expr, ($column:expr, $offset:expr) => $value:expr) => {{
        use halo2_proofs::circuit::Value;
        let description =
            $crate::concat_with_preamble!(stringify!($column), " => ", stringify!($value));
        let value: F = $value;
        $region.assign_advice(|| description, $column, $offset, || Value::known(value))
    }};
    // Cell
    ($region:expr, $cell:expr, $offset:expr => $value:expr) => {{
        use halo2_proofs::circuit::Value;
        let description =
            $crate::concat_with_preamble!(stringify!($cell), " => ", stringify!($value));
        let value: F = $value;
        $region.assign_advice(
            || description,
            $cell.column(),
            $offset + $cell.rotation(),
            || Value::known(value),
        )
    }};
}

/// assign fixed
#[macro_export]
macro_rules! assignf {
    ($region:expr, ($column:expr, $offset:expr) => $value:expr) => {{
        let description =
            $crate::concat_with_preamble!(stringify!($column), " => ", stringify!($value));
        let value: F = $value;
        $region.assign_fixed(|| description, $column, $offset, || Value::known(value))
    }};
}

/// Circuit builder macros
/// Nested macro's can't do repetition (https://github.com/rust-lang/rust/issues/35853)
/// so we expose a couple of permutations here manually.
#[macro_export]
macro_rules! circuit {
    ([$meta:expr, $cb:expr], $content:block) => {{
        #[allow(unused_imports)]
        use $crate::{concat_with_preamble, _require, _matchx, _ifx, _unreachablex};
        #[allow(unused_imports)]
        use gadgets::util::{and, not, or, sum, Expr};
        #[allow(unused_imports)]
        use $crate::circuit_tools::constraint_builder::{ExprVec, ExprResult};

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
        macro_rules! x {
            ($column:expr, $rot:expr) => {{
                $meta.query_any($column.clone(), Rotation($rot as i32))
            }};
            ($column:expr) => {{
                $meta.query_any($column.clone(), Rotation::cur())
            }};
        }

        #[allow(unused_macros)]
        macro_rules! not {
            ($expr:expr) => {{
                gadgets::util::not::expr($expr.expr())
            }};
        }

        #[allow(unused_macros)]
        macro_rules! invert {
            ($expr:expr) => {{
                Expression::Constant(F::from($expr as u64).invert().unwrap())
            }};
        }

        #[allow(unused_macros)]
        macro_rules! require {
            ($lhs:expr => bool) => {{
                _require!($cb, $lhs => bool);
            }};

            ($lhs:expr => $rhs:expr) => {{
                _require!($cb, $lhs => $rhs);
            }};

            ($name:expr, $lhs:expr => $rhs:expr) => {{
                _require!($cb, $name, $lhs => $rhs);
            }};

            (($a:expr) => @$tag:expr) => {{
                _require!($cb, ($a) => @$tag);
            }};

            (($a:expr, $b:expr) => @$tag:expr) => {{
                _require!($cb, ($a, $b) => @$tag);
            }};

            (($a:expr, $b:expr, $c:expr) => @$tag:expr) => {{
                _require!($cb, ($a, $b, $c) => @$tag);
            }};

            (($a:expr, $b:expr, $c:expr, $d:expr) => @$tag:expr) => {{
                _require!($cb, ($a, $b, $c, $d) => @$tag);
            }};

            ($values:expr => @$tag:expr) => {{
                _require!($cb, $values => @$tag);
            }};

            ($descr:expr, $values:expr => @$tag:expr) => {{
                _require!($cb, $descr, $values => @$tag);
            }};

            (@$tag:expr => ($a:expr, $b:expr, $c:expr)) => {{
                _require!($cb, @$tag => ($a, $b, $c));
            }};

            (@$tag:expr => $values:expr) => {{
                _require!($cb, @$tag => $values);
            }};
        }

        #[allow(unused_macros)]
        macro_rules! ifx {
            ($condition:expr => $when_true:block elsex $when_false:block) => {{
                _ifx!($cb, $condition => $when_true elsex $when_false)
            }};
            ($condition_a:expr, $condition_b:expr => $when_true:block elsex $when_false:block) => {{
                _ifx!($cb, $condition_a, $condition_b => $when_true elsex $when_false)
            }};
            ($condition_a:expr, $condition_b:expr, $condition_c:expr => $when_true:block elsex $when_false:block) => {{
                _ifx!($cb, $condition_a, $condition_b, $condition_c => $when_true elsex $when_false)
            }};
            ($condition_a:expr, $condition_b:expr, $condition_c:expr, $condition_d:expr => $when_true:block elsex $when_false:block) => {{
                _ifx!($cb, $condition_a, $condition_b, $condition_c, $condition_d => $when_true elsex $when_false)
            }};

            ($condition:expr => $when_true:block) => {{
                _ifx!($cb, $condition => $when_true)
            }};
            ($condition_a:expr, $condition_b:expr => $when_true:block) => {{
                _ifx!($cb, $condition_a, $condition_b => $when_true)
            }};
            ($condition_a:expr, $condition_b:expr, $condition_c:expr => $when_true:block) => {{
                _ifx!($cb, $condition_a, $condition_b, $condition_c => $when_true)
            }};
            ($condition_a:expr, $condition_b:expr, $condition_c:expr, $condition_d:expr => $when_true:block) => {{
                _ifx!($cb, $condition_a, $condition_b, $condition_c, $condition_d => $when_true)
            }};
            ($condition_a:expr, $condition_b:expr, $condition_c:expr, $condition_d:expr, $condition_e:expr => $when_true:block) => {{
                _ifx!($cb, $condition_a, $condition_b, $condition_c, $condition_d, $condition_e => $when_true)
            }};
        }

        #[allow(unused_macros)]
        macro_rules! matchx {
            ($condition_a:expr => $when_a:expr,) => {{
                _matchx!($cb, $condition_a => $when_a)
            }};
            ($condition_a:expr => $when_a:expr, $condition_b:expr => $when_b:expr,) => {{
                _matchx!($cb, $condition_a => $when_a, $condition_b => $when_b)
            }};
            ($condition_a:expr => $when_a:expr, $condition_b:expr => $when_b:expr, $condition_c:expr => $when_c:expr,) => {{
                _matchx!($cb, $condition_a => $when_a, $condition_b => $when_b, $condition_c => $when_c)
            }};
            ($condition_a:expr => $when_a:expr, $condition_b:expr => $when_b:expr, $condition_c:expr => $when_c:expr, $condition_d:expr => $when_d:expr,) => {{
                _matchx!($cb, $condition_a => $when_a, $condition_b => $when_b, $condition_c => $when_c, $condition_d => $when_d,)
            }};

            ($condition_a:expr => $when_a:expr, _ => $catch_all:expr,) => {{
                _matchx!($cb, $condition_a => $when_a, _ => $catch_all,)
            }};
            ($condition_a:expr => $when_a:expr, $condition_b:expr => $when_b:expr, _ => $catch_all:expr,) => {{
                _matchx!($cb, $condition_a => $when_a, $condition_b => $when_b, _ => $catch_all,)
            }};
            ($condition_a:expr => $when_a:expr, $condition_b:expr => $when_b:expr, $condition_c:expr => $when_c:expr, _ => $catch_all:expr,) => {{
                _matchx!($cb, $condition_a => $when_a, $condition_b => $when_b, $condition_c => $when_c, _ => $catch_all,)
            }};
            ($condition_a:expr => $when_a:expr, $condition_b:expr => $when_b:expr, $condition_c:expr => $when_c:expr, $condition_d:expr => $when_d:expr, _ => $catch_all:expr,) => {{
                _matchx!($cb, $condition_a => $when_a, $condition_b => $when_b, $condition_c => $when_c, $condition_d => $when_d, _ => $catch_all,)
            }};
        }

        #[allow(unused_macros)]
        macro_rules! unreachablex {
            () => {{
                _unreachablex!($cb)
            }};
            ($arg:expr) => {{
                _unreachablex!($cb, $arg)
            }};
        }

        $content
    }};
}
