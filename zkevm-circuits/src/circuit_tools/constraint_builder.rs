//! Circuit utilities
use std::{
    collections::HashMap,
    ops::{Add, Mul},
    vec,
};

use crate::{evm_circuit::util::rlc, table::LookupTable, util::Expr};
use eth_types::Field;
use gadgets::util::{and, sum, Scalar};
use halo2_proofs::{
    plonk::{ConstraintSystem, Expression},
    poly::Rotation,
};
use itertools::Itertools;

use super::{
    cached_region::StoredExpression,
    cell_manager::{Cell, CellManager, CellType},
};

fn get_condition_expr<F: Field>(conditions: &Vec<Expression<F>>) -> Expression<F> {
    if conditions.is_empty() {
        1.expr()
    } else {
        and::expr(conditions)
    }
}

/// Data for dynamic lookup
#[derive(Clone, Debug)]
pub struct DynamicData<F> {
    /// Desciption
    pub description: &'static str,
    /// Condition under which the lookup needs to be done
    pub condition: Expression<F>,
    /// The values to lookup
    pub values: Vec<Expression<F>>,
    /// region
    pub region_id: usize,
    /// If is fixed, use static table for lookup
    pub is_fixed: bool,
    /// Use rlc
    pub is_combine: bool,
    /// Lower the degree by spliting expression
    pub is_split: bool,
}

/// Constraint builder
#[derive(Clone)]
pub struct ConstraintBuilder<F, C: CellType> {
    /// Constraints to be returned to meta
    constraints: Vec<(&'static str, Expression<F>)>,
    /// Max degree of constraints
    max_degree: usize,
    /// conditions for constraints
    conditions: Vec<Expression<F>>,
    /// The lookups generated during synthesis
    /// assembles runtime access to RAM
    pub dynamic_lookups: HashMap<C, Vec<DynamicData<F>>>,
    /// The tables written during synthesis
    /// write to RAM
    pub dynamic_tables: HashMap<C, Vec<DynamicData<F>>>,
    /// All stored expressions
    pub stored_expressions: HashMap<usize, Vec<StoredExpression<F, C>>>,
    /// CellManager
    pub cell_manager: Option<CellManager<F, C>>,
    /// Disable macro-generated description for constraints & lookups
    /// for graph display
    pub disable_description: bool,
    /// region id
    pub region_id: usize,
    /// lookup input challenge
    pub lookup_challenge: Option<Expression<F>>,
    /// state contect
    pub state_context: Vec<Expression<F>>,
    /// state constraints start
    pub state_constraints_start: usize,
}

impl<F: Field, C: CellType> ConstraintBuilder<F, C> {
    pub(crate) fn new(
        max_degree: usize,
        cell_manager: Option<CellManager<F, C>>,
        lookup_challenge: Option<Expression<F>>,
    ) -> Self {
        ConstraintBuilder {
            constraints: Vec::new(),
            max_degree,
            conditions: Vec::new(),
            dynamic_lookups: HashMap::new(),
            dynamic_tables: HashMap::new(),
            cell_manager,
            disable_description: false,
            stored_expressions: HashMap::new(),
            region_id: 0,
            lookup_challenge,
            state_context: Vec::new(),
            state_constraints_start: 0,
        }
    }

    pub(crate) fn set_cell_manager(&mut self, cell_manager: CellManager<F, C>) {
        self.cell_manager = Some(cell_manager);
    }

    pub(crate) fn set_max_degree(&mut self, max_degree: usize) {
        self.max_degree = max_degree;
    }

    pub(crate) fn push_region(&mut self, region_id: usize) {
        assert!(region_id != 0);
        self.region_id = region_id;
        self.state_context = self.conditions.clone();
        self.conditions.clear();
        self.state_constraints_start = self.constraints.len();
    }

    pub(crate) fn pop_region(&mut self) {
        let condition = get_condition_expr(&self.state_context);
        for idx in self.state_constraints_start..self.constraints.len() {
            self.constraints[idx].1 = condition.expr() * self.constraints[idx].1.clone();
        }
        for (_, values) in self.dynamic_lookups.iter_mut() {
            for value in values {
                if value.region_id == self.region_id {
                    value.condition = condition.expr() * value.condition.expr();
                }
            }
        }
        for (_key, values) in self.dynamic_tables.iter_mut() {
            for value in values {
                if value.region_id == self.region_id {
                    value.condition = condition.expr() * value.condition.expr();
                }
            }
        }
        self.conditions = self.state_context.clone();
        self.region_id = 0;
    }

    pub(crate) fn set_disable_description(&mut self, disable_description: bool) {
        self.disable_description = disable_description;
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
        if self.max_degree == 0 {
            return;
        }
        let constraint = match self.get_condition() {
            Some(condition) => condition * constraint,
            None => constraint,
        };
        let constraint = self.split_expression(name, constraint);
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
        self.query_cells_dyn(
            C::byte_type().expect("No byte type for this CellManager"),
            N,
        )
        .try_into()
        .unwrap()
    }

    pub(crate) fn query_cells_dyn(&mut self, cell_type: C, count: usize) -> Vec<Cell<F>> {
        self.cell_manager
            .as_mut()
            .expect("Cell manager not set")
            .query_cells(cell_type, count)
    }

    pub(crate) fn query_cell_with_type(&mut self, cell_type: C) -> Cell<F> {
        self.query_cells_dyn(cell_type, 1).first().unwrap().clone()
    }

    pub(crate) fn validate_degree(&self, degree: usize, name: &'static str) {
        if self.max_degree > 0 && self.region_id != 0 {
            debug_assert!(
                degree <= self.max_degree,
                "Expression {} degree too high: {} > {}",
                name,
                degree,
                self.max_degree,
            );
        }
    }

    pub(crate) fn build_constraints(&self) -> Vec<(&'static str, Expression<F>)> {
        self.constraints.clone()
    }

    pub(crate) fn build_celltype_lookups(
        &self,
        meta: &mut ConstraintSystem<F>,
        cell_managers: Vec<CellManager<F, C>>,
        tables: Vec<(C, &dyn LookupTable<F>)>,
    ) {
        for cm in cell_managers {
            for (cell_type, table) in &tables {
                for col in cm.get_typed_columns(*cell_type) {
                    let name = format!("{:?}", cell_type);
                    meta.lookup_any(Box::leak(name.into_boxed_str()), |meta| {
                        vec![(
                            col.expr,
                            rlc::expr(
                                &table.table_exprs(meta),
                                self.lookup_challenge.clone().unwrap(),
                            ),
                        )]
                    });
                }
            }
        }
    }

    pub(crate) fn build_dynamic_lookups(
        &mut self,
        meta: &mut ConstraintSystem<F>,
        lookup_names: &[C],
        fixed_table: Vec<(C, &dyn LookupTable<F>)>,
    ) {
        let lookups = self.dynamic_lookups.clone();
        for lookup_name in lookup_names.iter() {
            if let Some(lookups) = lookups.get(lookup_name) {
                for lookup in lookups.iter() {
                    meta.lookup_any(lookup.description, |meta| {
                        // Fixed lookup is a direct lookup into the pre-difined fixed tables
                        // i.e. cond * (v1, v2, v3) => (t1, t2, t3)
                        // equivalent to the vanilla lookup operation of Halo2.
                        // Dynamic lookup applies condition to the advice values stored at
                        // configuration time i.e. cond * (v1, v2, v3) =>
                        // cond * (t1, t2, t3) the dynamic lookup in a ifx!
                        // branch would become trivial 0 => 0
                        // when the elsex! branch evaluates to true

                        let table = if lookup.is_fixed {
                            let table_cols = fixed_table
                                .iter()
                                .find(|(name, _)| name == lookup_name)
                                .unwrap()
                                .1
                                .columns();
                            table_cols
                                .iter()
                                .map(|col| meta.query_any(*col, Rotation(0)))
                                .collect()
                        } else {
                            let dyn_table = self.get_dynamic_table_values(*lookup_name);
                            assert_eq!(dyn_table.len(), lookup.values.len());
                            dyn_table
                        };

                        let mut values: Vec<_> = lookup
                            .values
                            .iter()
                            .map(|value| value.expr() * lookup.condition.clone())
                            .collect();
                        // allign the length of values and table
                        assert!(table.len() >= values.len());
                        while values.len() < table.len() {
                            values.push(0.expr());
                        }

                        // Perform rlc if specified
                        // i.e. (v1*r + v2*r^2 + v3*r^3) => (t1*r + t2*r^2 + t3*r^3)
                        // lastly is_split had been fulfilled at insertion time

                        let ret = if lookup.is_combine {
                            vec![(
                                rlc::expr(&values, self.lookup_challenge.clone().unwrap()),
                                rlc::expr(&table, self.lookup_challenge.clone().unwrap()),
                            )]
                        } else {
                            values
                                .iter()
                                .zip(table.iter())
                                .map(|(v, t)| (v.expr(), t.expr()))
                                .collect()
                        };
                        ret
                    });
                }
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

    pub(crate) fn store_dynamic_table(
        &mut self,
        description: &'static str,
        tag: C,
        values: Vec<Expression<F>>,
        is_combine: bool,
        is_split: bool,
    ) {
        let condition = self.get_condition_expr();
        let mut values = if is_combine {
            vec![rlc::expr(&values, self.lookup_challenge.clone().unwrap())]
        } else {
            values.clone()
        };
        if is_split {
            values.iter_mut().for_each(|v| {
                *v = self.split_expression(
                    Box::leak(format!("compression value - {:?}", tag).into_boxed_str()),
                    v.clone(),
                )
            });
        }
        let lookup = DynamicData {
            description,
            condition,
            values,
            region_id: self.region_id,
            // cannot be is_fixed
            is_fixed: false,
            is_combine: false,
            is_split: false,
        };
        if let Some(table_data) = self.dynamic_tables.get_mut(&tag) {
            table_data.push(lookup);
        } else {
            self.dynamic_tables.insert(tag, vec![lookup]);
        }
    }

    pub(crate) fn add_dynamic_lookup(
        &mut self,
        description: &'static str,
        tag: C,
        values: Vec<Expression<F>>,
        is_fixed: bool,
        is_combine: bool,
        is_split: bool,
    ) {
        let condition = self.get_condition_expr();
        let mut values = if is_combine {
            vec![rlc::expr(&values, self.lookup_challenge.clone().unwrap())]
        } else {
            values.clone()
        };
        if is_split {
            values.iter_mut().for_each(|v| {
                *v = self.split_expression(
                    Box::leak(format!("compression value - {:?}", tag).into_boxed_str()),
                    v.clone(),
                )
            });
        }
        let lookup = DynamicData {
            description,
            condition,
            values,
            region_id: self.region_id,
            is_fixed,
            is_combine,
            is_split,
        };
        if let Some(lookup_data) = self.dynamic_lookups.get_mut(&tag) {
            lookup_data.push(lookup);
        } else {
            self.dynamic_lookups.insert(tag, vec![lookup]);
        }
    }

    pub(crate) fn add_celltype_lookup(
        &mut self,
        description: &str,
        cell_type: C,
        values: Vec<Expression<F>>,
    ) {
        let condition = self.get_condition_expr();
        let values = values
            .iter()
            .map(|value| condition.expr() * value.expr())
            .collect_vec();
        let compressed_expr = self.split_expression(
            "compression",
            rlc::expr(&values, self.lookup_challenge.clone().unwrap().expr()),
        );
        self.store_expression(description, compressed_expr, cell_type);
    }

    pub(crate) fn get_stored_expressions(&self, region_id: usize) -> Vec<StoredExpression<F, C>> {
        self.stored_expressions
            .get(&region_id)
            .cloned()
            .unwrap_or_default()
    }

    pub(crate) fn get_dynamic_table(&self, tag: C) -> (Expression<F>, Vec<Expression<F>>) {
        let table_values = self
            .dynamic_tables
            .get(&tag)
            .unwrap_or_else(|| panic!("Dynamic table {:?} not found", tag));
        merge_values_unsafe(
            table_values
                .iter()
                .map(|table| {
                    (
                        table.condition.clone(),
                        table.values.clone(),
                        table.is_split,
                    )
                })
                .collect::<Vec<_>>(),
        )
    }

    pub(crate) fn get_dynamic_table_values(&self, tag: C) -> Vec<Expression<F>> {
        let condition_and_values = self.get_dynamic_table(tag);
        condition_and_values
            .1
            .iter()
            .map(|value| value.expr() * condition_and_values.0.expr())
            .collect::<Vec<_>>()
    }

    pub(crate) fn generate_lookup_table_checks(&mut self, tag: C) {
        let table_values = self
            .dynamic_tables
            .get(&tag)
            .unwrap_or_else(|| panic!("Dynamic table {:?} not found", tag))
            .clone();
        let selectors = table_values
            .into_iter()
            .map(|value| {
                let sel = value.condition.expr();
                self.require_boolean("lookup table condition needs to be boolean", sel.clone());
                sel
            })
            .collect::<Vec<_>>();
        let selector = sum::expr(&selectors);
        self.require_boolean(
            "lookup table conditions sum needs to be boolean",
            selector.expr(),
        );
    }

    pub(crate) fn store_expression(
        &mut self,
        name: &str,
        expr: Expression<F>,
        cell_type: C,
    ) -> Expression<F> {
        // Check if we already stored the expression somewhere
        let stored_expression = self.find_stored_expression(&expr, cell_type);
        match stored_expression {
            Some(stored_expression) => stored_expression.cell.expr(),
            None => {
                // println!("cell_type: {:?}", cell_type);
                // Require the stored value to equal the value of the expression
                let cell = self.query_one(cell_type);
                let name = format!("{} (stored expression)", name);
                self.constraints.push((
                    Box::leak(name.clone().into_boxed_str()),
                    cell.expr() - expr.clone(),
                ));
                self.stored_expressions
                    .entry(self.region_id)
                    .or_insert_with(Vec::new)
                    .push(StoredExpression {
                        name,
                        cell: cell.clone(),
                        cell_type,
                        expr_id: expr.identifier(),
                        expr,
                    });
                cell.expr()
            }
        }
    }

    pub(crate) fn find_stored_expression(
        &self,
        expr: &Expression<F>,
        cell_type: C,
    ) -> Option<&StoredExpression<F, C>> {
        let expr_id = expr.identifier();
        if let Some(stored_expressions) = self.stored_expressions.get(&self.region_id) {
            stored_expressions
                .iter()
                .find(|&e| e.cell_type == cell_type && e.expr_id == expr_id)
        } else {
            None
        }
    }

    fn split_expression(&mut self, name: &'static str, expr: Expression<F>) -> Expression<F> {
        if expr.degree() > self.max_degree && self.region_id != 0 {
            match expr {
                Expression::Negated(poly) => {
                    Expression::Negated(Box::new(self.split_expression(name, *poly)))
                }
                Expression::Scaled(poly, v) => {
                    Expression::Scaled(Box::new(self.split_expression(name, *poly)), v)
                }
                Expression::Sum(a, b) => {
                    let a = self.split_expression(name, *a);
                    let b = self.split_expression(name, *b);
                    a + b
                }
                Expression::Product(a, b) => {
                    let (mut a, mut b) = (*a, *b);
                    while a.degree() + b.degree() > self.max_degree {
                        let mut split = |expr: Expression<F>| {
                            if expr.degree() > self.max_degree {
                                self.split_expression(name, expr)
                            } else {
                                let cell_type = C::storage_for_expr(&expr);
                                self.store_expression(name, expr, cell_type)
                            }
                        };
                        if a.degree() >= b.degree() {
                            a = split(a);
                        } else {
                            b = split(b);
                        }
                    }
                    a * b
                }
                _ => expr.clone(),
            }
        } else {
            expr.clone()
        }
    }

    pub(crate) fn print_stats(&self) {
        let mut expressions = self.constraints.clone();
        expressions.sort_by(|a, b| a.1.degree().cmp(&b.1.degree()));
        for (name, expr) in expressions.iter() {
            println!("'{}': {}", name, expr.degree());
        }
    }
}

pub(crate) fn merge_lookups<F: Field, C: CellType>(
    cb: &mut ConstraintBuilder<F, C>,
    lookups: Vec<DynamicData<F>>,
) -> (Expression<F>, Vec<Expression<F>>) {
    let values = lookups
        .iter()
        .map(|lookup| {
            (
                lookup.condition.clone(),
                lookup.values.clone(),
                lookup.is_split,
            )
        })
        .collect::<Vec<_>>();
    let selector = sum::expr(values.iter().map(|(condition, _, _)| condition.expr()));
    crate::circuit!([meta, cb], {
        require!(selector => bool);
    });
    merge_values_unsafe(values)
}

pub(crate) fn merge_values_unsafe<F: Field>(
    values: Vec<(Expression<F>, Vec<Expression<F>>, bool)>,
) -> (Expression<F>, Vec<Expression<F>>) {
    if values.is_empty() {
        return (0.expr(), Vec::new());
    }
    let selector = sum::expr(values.iter().map(|(condition, _, _)| condition.expr()));
    // Merge
    let max_length = values
        .iter()
        .map(|(_, values, _)| values.len())
        .max()
        .unwrap();
    let mut merged_values = vec![0.expr(); max_length];
    let default_value = 0.expr();
    for (idx, value) in merged_values.iter_mut().enumerate() {
        *value = sum::expr(values.iter().map(|(condition, values, _is_split)| {
            // Condition had been included if is_split
            values.get(idx).unwrap_or(&default_value).expr() * {
                condition.expr()
                // if *is_split {1.expr() } else {condition.expr()}
            }
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
        <&[T]>::clone(self).to_owned()
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
    fn add(&self, _other: &Self) -> Self {}
    fn mul(&self, _other: &Expression<F>) -> Self {}
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
    /// Returns the RLC of the reverse of itself
    fn rlc_rev(&self, r: &Expression<F>) -> Expression<F>;
}

impl<F: Field, E: ExprVec<F> + ?Sized> RLCable<F> for E {
    fn rlc(&self, r: &Expression<F>) -> Expression<F> {
        rlc::expr(&self.to_expr_vec(), r.expr())
    }

    fn rlc_rev(&self, r: &Expression<F>) -> Expression<F> {
        rlc::expr(
            &self.to_expr_vec().iter().rev().cloned().collect_vec(),
            r.expr(),
        )
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
pub trait RLCChainable2<F> {
    /// Returns the RLC of itself with a starting rlc/multiplier
    fn rlc_chain2(&self, other: (Expression<F>, Expression<F>)) -> Expression<F>;
}

impl<F: Field> RLCChainable2<F> for Expression<F> {
    fn rlc_chain2(&self, other: (Expression<F>, Expression<F>)) -> Expression<F> {
        self.expr() * other.1.expr() + other.0.expr()
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
        use $crate::circuit_tools::cell_manager::DefaultCellType;
        ConstraintBuilder::<F, DefaultCellType>::new(0, None, None)
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
        let description = concat_with_preamble!(
            stringify!($lhs),
            " => ",
            "bool",
        );
        $cb.require_boolean(description, $lhs.expr());
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
        let description = concat_with_preamble!(
            "(",
            $(
                stringify!($v),
                ", ",
            )*
            ") => @",
            stringify!($tag),
        );
        $cb.add_celltype_lookup(
            description,
            $tag,
            vec![$($v.expr(),)*],
        );
    }};
    ($cb:expr, $descr:expr, ($($v:expr),+)  => @$tag:expr) => {{
        $cb.add_celltype_lookup(
            Box::leak($descr.into_boxed_str()),
            $tag,
            vec![$($v.expr(),)*],
        );
    }};

    // Lookup using an array
    ($cb:expr, $values:expr => @$tag:expr) => {{
        let description = concat_with_preamble!(
            stringify!($values),
            " => @",
            stringify!($tag),
        );
        $cb.add_celltype_lookup(
            description,
            $tag,
            $values.clone(),
        );
    }};
    ($cb:expr, $descr:expr, $values:expr => @$tag:expr) => {{
        $cb.add_celltype_lookup(
            Box::leak($descr.to_string().into_boxed_str()),
            $tag,
            $values.clone(),
        );
    }};

        // Lookup using a tuple
        ($cb:expr, ($($v:expr),+) => @$tag:expr, $is_fixed:expr, $is_combine:expr, $is_split:expr) => {{
            let description = concat_with_preamble!(
                "(",
                $(
                    stringify!($v),
                    ", ",
                )*
                ") => @",
                stringify!($tag),
            );
            $cb.add_dynamic_lookup(
                description,
                $tag,
                vec![$($v.expr(),)*],
                $is_fixed,
                $is_combine,
                $is_split,
            );
        }};
        ($cb:expr, $descr:expr, ($($v:expr),+)  => @$tag:expr, $is_fixed:expr, $is_combine:expr, $is_split:expr) => {{
            $cb.add_dynamic_lookup(
                Box::leak($descr.into_boxed_str()),
                $tag,
                vec![$($v.expr(),)*],
                $is_fixed,
                $is_combine,
                $is_split,
            );
        }};


        // Lookup using an array
        ($cb:expr, $values:expr => @$tag:expr, $is_fixed:expr, $is_combine:expr, $is_split:expr) => {{
            let description = concat_with_preamble!(
                stringify!($values),
                " => @",
                stringify!($tag),
            );
            $cb.add_dynamic_lookup(
                description,
                $tag,
                $values.clone(),
                $is_fixed,
                $is_combine,
                $is_split,
            );
        }};
        ($cb:expr, $descr:expr, $values:expr => @$tag:expr, $is_fixed:expr, $is_combine:expr, $is_split:expr) => {{
            $cb.add_dynamic_lookup(
                Box::leak($descr.into_boxed_str()),
                $tag,
                $values.clone(),
                $is_fixed,
                $is_combine,
                $is_split,
            );
        }};

    // Put values in a lookup table using a tuple
    ($cb:expr, @$tag:expr => ($($v:expr),+)) => {{
        let description = concat_with_preamble!(
            "@",
            stringify!($tag),
            " => (",
            $(
                stringify!($v),
                ", ",
            )*
            ")",
        );
        $cb.store_dynamic_table(
            description,
            $tag,
            vec![$($v.expr(),)*],
            false,
            false,
        );
    }};
    // Put values in a lookup table using an array
    ($cb:expr, @$tag:expr => $values:expr) => {{
        let description = concat_with_preamble!(
            "@",
            stringify!($tag),
            " => (",
            stringify!($values),
            ")",
        );
        $cb.store_dynamic_table(
            description,
            $tag,
            $values,
            false,
            false,
        );
    }};

    // Put values in a lookup table using a tuple
    ($cb:expr, @$tag:expr => ($($v:expr),+), $is_combine:expr, $is_split:expr) => {{
        let description = concat_with_preamble!(
            "@",
            stringify!($tag),
            " => (",
            $(
                stringify!($v),
                ", ",
            )*
            ")",
        );
        $cb.store_dynamic_table(
            description,
            $tag,
            vec![$($v.expr(),)*],
            $is_combine,
            $is_split,
        );
    }};
    // Put values in a lookup table using an array
    ($cb:expr, @$tag:expr => $values:expr, $is_combine:expr, $is_split:expr) => {{
        let description = concat_with_preamble!(
            "@",
            stringify!($tag),
            " => (",
            stringify!($values),
            ")",
        );
        $cb.store_dynamic_table(
            description,
            $tag,
            $values,
            $is_combine,
            $is_split,
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
    ($region:expr, ($column:expr, $offset:expr) => $annotation:expr, $value:expr) => {{
        use halo2_proofs::circuit::Value;
        let value: F = $value;
        $region.name_column(|| $annotation, $column);
        $region.assign_advice(|| "", $column, $offset, || Value::known(value))
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
    ($region:expr, $cell:expr, $offset:expr => $annotation:expr, $value:expr) => {{
        use halo2_proofs::circuit::Value;
        let value: F = $value;
        $region.assign_advice(
            || $annotation,
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
/// Nested macro's can't do repetition <https://github.com/rust-lang/rust/issues/35853>
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

            (($a:expr) => @$tag:expr, $is_fixed:expr, $is_combine:expr, $is_split:expr) => {{
                _require!($cb, ($a) => @$tag, $is_fixed, $is_combine, $is_split);
            }};

            (($a:expr, $b:expr) => @$tag:expr, $is_fixed:expr, $is_combine:expr, $is_split:expr) => {{
                _require!($cb, ($a, $b) => @$tag, $is_fixed, $is_combine, $is_split);
            }};

            (($a:expr, $b:expr, $c:expr) => @$tag:expr, $is_fixed:expr, $is_combine:expr, $is_split:expr) => {{
                _require!($cb, ($a, $b, $c) => @$tag, $is_fixed, $is_combine, $is_split);
            }};

            (($a:expr, $b:expr, $c:expr, $d:expr) => @$tag:expr, $is_fixed:expr, $is_combine:expr, $is_split:expr) => {{
                _require!($cb, ($a, $b, $c, $d) => @$tag, $is_fixed, $is_combine, $is_split);
            }};

            ($values:expr => @$tag:expr, $is_fixed:expr, $is_combine:expr, $is_split:expr) => {{
                _require!($cb, $values => @$tag, $is_fixed, $is_combine, $is_split);
            }};

            ($descr:expr, $values:expr => @$tag:expr, $is_fixed:expr, $is_combine:expr, $is_split:expr) => {{
                _require!($cb, $descr, $values => @$tag, $is_fixed, $is_combine, $is_split);
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
