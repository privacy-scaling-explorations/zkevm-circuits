//! Circuit utilities
use std::{
    collections::BTreeMap,
    marker::PhantomData,
    ops::{Index, IndexMut},
};

use crate::{
    evm_circuit::util::rlc,
    util::{query_expression, Expr},
};
use gadgets::util::{and, select, sum};
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{AssignedCell, Layouter, Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, VirtualCells},
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

#[derive(Clone, Debug)]
pub(crate) struct Cell<F> {
    // expression for constraint
    expression: Expression<F>,
    column: Column<Advice>,
    // relative position to selector for synthesis
    rotation: usize,
}

impl<F: FieldExt> Cell<F> {
    pub(crate) fn new(meta: &mut VirtualCells<F>, column: Column<Advice>, rotation: usize) -> Self {
        Self {
            expression: meta.query_advice(column, Rotation(rotation as i32)),
            column,
            rotation,
        }
    }

    pub(crate) fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        value: Value<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        region.assign_advice(
            || {
                format!(
                    "Cell column: {:?} and rotation: {}",
                    self.column, self.rotation
                )
            },
            self.column,
            offset + self.rotation,
            || value,
        )
    }
}

impl<F: FieldExt> Expr<F> for Cell<F> {
    fn expr(&self) -> Expression<F> {
        self.expression.clone()
    }
}

impl<F: FieldExt> Expr<F> for &Cell<F> {
    fn expr(&self) -> Expression<F> {
        self.expression.clone()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum CellType {
    Storage,
}

#[derive(Clone, Debug)]
pub(crate) struct CellColumn<F> {
    pub(crate) index: usize,
    pub(crate) cell_type: CellType,
    pub(crate) height: usize,
    pub(crate) expr: Expression<F>,
}

impl<F: FieldExt> Expr<F> for CellColumn<F> {
    fn expr(&self) -> Expression<F> {
        self.expr.clone()
    }
}

#[derive(Clone, Debug)]
pub(crate) struct CellManager<F> {
    width: usize,
    height: usize,
    cells: Vec<Cell<F>>,
    columns: Vec<CellColumn<F>>,
}

impl<F: FieldExt> CellManager<F> {
    pub(crate) fn new(
        meta: &mut VirtualCells<F>,
        height: usize,
        advices: &[Column<Advice>],
        height_offset: usize,
    ) -> Self {
        // Setup the columns and query the cells
        let width = advices.len();
        let mut cells = Vec::with_capacity(height * width);
        let mut columns = Vec::with_capacity(width);
        for c in 0..width {
            for r in 0..height {
                cells.push(Cell::new(meta, advices[c], height_offset + r));
            }
            columns.push(CellColumn {
                index: c,
                cell_type: CellType::Storage,
                height: 0,
                expr: cells[c * height].expr(),
            });
        }

        Self {
            width,
            height,
            cells,
            columns,
        }
    }

    pub(crate) fn query_cells(&mut self, cell_type: CellType, count: usize) -> Vec<Cell<F>> {
        let mut cells = Vec::with_capacity(count);
        while cells.len() < count {
            let column_idx = self.next_column(cell_type);
            let column = &mut self.columns[column_idx];
            cells.push(self.cells[column_idx * self.height + column.height].clone());
            column.height += 1;
        }
        cells
    }

    pub(crate) fn query_cell(&mut self, cell_type: CellType) -> Cell<F> {
        self.query_cells(cell_type, 1)[0].clone()
    }

    fn next_column(&self, cell_type: CellType) -> usize {
        let mut best_index: Option<usize> = None;
        let mut best_height = self.height;
        for column in self.columns.iter() {
            if column.cell_type == cell_type && column.height < best_height {
                best_index = Some(column.index);
                best_height = column.height;
            }
        }
        match best_index {
            Some(index) => index,
            None => unreachable!("not enough cells for query: {:?}", cell_type),
        }
    }

    pub(crate) fn get_height(&self) -> usize {
        self.columns
            .iter()
            .map(|column| column.height)
            .max()
            .unwrap()
    }

    /// Returns a map of CellType -> (width, height, num_cells)
    pub(crate) fn get_stats(&self) -> BTreeMap<CellType, (usize, usize, usize)> {
        let mut data = BTreeMap::new();
        for column in self.columns.iter() {
            let (mut count, mut height, mut num_cells) =
                data.get(&column.cell_type).unwrap_or(&(0, 0, 0));
            count += 1;
            height = height.max(column.height);
            num_cells += column.height;
            data.insert(column.cell_type, (count, height, num_cells));
        }
        data
    }

    pub(crate) fn columns(&self) -> &[CellColumn<F>] {
        &self.columns
    }
}

#[derive(Clone, Debug, Default)]
pub(crate) struct Memory<F> {
    columns: Vec<Column<Advice>>,
    banks: Vec<MemoryBank<F>>,
}

impl<F: FieldExt> Memory<F> {
    pub(crate) fn new(columns: Vec<Column<Advice>>) -> Self {
        Self {
            columns,
            banks: Vec::new(),
        }
    }

    pub(crate) fn allocate<S: AsRef<str>>(
        &mut self,
        meta: &mut ConstraintSystem<F>,
        tag: S,
    ) -> &MemoryBank<F> {
        self.banks
            .push(MemoryBank::new(meta, self.columns[self.banks.len()], tag));
        self.banks.last().unwrap()
    }

    pub(crate) fn get<S: AsRef<str>>(&self, tag: S) -> &MemoryBank<F> {
        for bank in self.banks.iter() {
            if bank.tag() == tag.as_ref() {
                return bank;
            }
        }
        unreachable!()
    }

    pub(crate) fn get_mut<S: AsRef<str>>(&mut self, tag: S) -> &mut MemoryBank<F> {
        for bank in self.banks.iter_mut() {
            if bank.tag() == tag.as_ref() {
                return bank;
            }
        }
        unreachable!()
    }

    pub(crate) fn generate_constraints(&self, cb: &mut ConstraintBuilder<F>) {
        for bank in self.banks.iter() {
            bank.generate_constraints(cb);
            cb.generate_lookup_table_checks(bank.tag());

            /*let lookups = cb.consume_lookups(&[bank.tag()]);
            if !lookups.is_empty() {
                //println!("{}: {}", tag, lookups.len());
                let (_, values) = merge_lookups(cb, lookups);
                crate::circuit!([meta, cb], {
                    require!(values => @bank.tag());
                })
            }*/
        }
    }

    pub(crate) fn clear_witness_data(&mut self) {
        for bank in self.banks.iter_mut() {
            bank.clear_witness_data();
        }
    }

    pub(crate) fn assign(
        &self,
        layouter: &mut impl Layouter<F>,
        height: usize,
    ) -> Result<(), Error> {
        for bank in self.banks.iter() {
            bank.assign(layouter, height)?;
        }
        Ok(())
    }

    pub(crate) fn tags(&self) -> Vec<String> {
        self.banks.iter().map(|bank| bank.tag()).collect()
    }
}

impl<F: FieldExt, S: AsRef<str>> Index<S> for Memory<F> {
    type Output = MemoryBank<F>;

    fn index(&self, tag: S) -> &Self::Output {
        for bank in self.banks.iter() {
            if bank.tag() == tag.as_ref() {
                return bank;
            }
        }
        unreachable!()
    }
}

impl<F: FieldExt, S: AsRef<str>> IndexMut<S> for Memory<F> {
    fn index_mut(&mut self, tag: S) -> &mut Self::Output {
        for bank in self.banks.iter_mut() {
            if bank.tag() == tag.as_ref() {
                return bank;
            }
        }
        unreachable!()
    }
}

#[derive(Clone, Debug)]
pub(crate) struct MemoryBank<F> {
    column: Column<Advice>,
    tag: String,
    cur: Expression<F>,
    next: Expression<F>,
    store_offsets: Vec<usize>,
    stored_values: Vec<Vec<F>>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> MemoryBank<F> {
    pub(crate) fn new<S: AsRef<str>>(
        meta: &mut ConstraintSystem<F>,
        column: Column<Advice>,
        tag: S,
    ) -> Self {
        let mut cur = 0.expr();
        let mut next = 0.expr();
        query_expression(meta, |meta| {
            cur = meta.query_advice(column, Rotation::cur());
            next = meta.query_advice(column, Rotation::next());
        });
        Self {
            column,
            tag: tag.as_ref().to_owned(),
            cur,
            next,
            store_offsets: Vec::new(),
            stored_values: Vec::new(),
            _marker: PhantomData,
        }
    }

    pub(crate) fn key(&self) -> Expression<F> {
        self.cur.expr()
    }

    pub(crate) fn load(
        &self,
        description: &'static str,
        cb: &mut ConstraintBuilder<F>,
        offset: Expression<F>,
        values: &[Expression<F>],
    ) {
        self.load_with_key(description, cb, self.key() - offset, values);
    }

    pub(crate) fn load_with_key(
        &self,
        description: &'static str,
        cb: &mut ConstraintBuilder<F>,
        key: Expression<F>,
        values: &[Expression<F>],
    ) {
        let mut key_values = values.to_vec();
        key_values.insert(0, key);
        cb.lookup(description, self.tag(), values.to_vec());
    }

    pub(crate) fn store(&self, cb: &mut ConstraintBuilder<F>, values: &[Expression<F>]) {
        self.store_with_key(cb, self.key() + 1.expr(), values);
    }

    pub(crate) fn store_with_key(
        &self,
        cb: &mut ConstraintBuilder<F>,
        key: Expression<F>,
        values: &[Expression<F>],
    ) {
        let mut key_values = values.to_vec();
        key_values.insert(0, key);
        cb.lookup_table("memory store", self.tag(), values.to_vec());
    }

    pub(crate) fn witness_store(&mut self, offset: usize, values: &[F]) {
        self.stored_values.push(values.to_vec());
        self.store_offsets.push(offset);
    }

    pub(crate) fn witness_store_init(&mut self, values: &[F]) {
        self.stored_values.push(values.to_vec());
    }

    pub(crate) fn witness_load(&self, offset: usize) -> Vec<F> {
        self.stored_values[self.stored_values.len() - 1 - offset].clone()
    }

    pub(crate) fn clear_witness_data(&mut self) {
        self.store_offsets.clear();
    }

    pub(crate) fn generate_constraints(&self, cb: &mut ConstraintBuilder<F>) {
        let lookup_table = cb.get_lookup_table(self.tag());
        crate::circuit!([meta, cb], {
            // TODO(Brecht): fix
            //require!(self.next => self.cur.expr() + lookup_table.0);
        });
    }

    pub(crate) fn assign(
        &self,
        layouter: &mut impl Layouter<F>,
        height: usize,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "memory bank",
            |mut region| {
                // Pad to the full circuit (necessary for reads)
                let mut store_offsets = self.store_offsets.clone();
                store_offsets.push(height);

                //println!("offsets: {:?}", self.store_offsets);

                //println!("height: {}", height);
                let mut store_index = 0;
                let mut offset = 0;
                for &stored_offset in store_offsets.iter() {
                    while offset <= stored_offset {
                        region.assign_advice(
                            || "assign memory index".to_string(),
                            self.column,
                            offset,
                            || Value::known(F::from(store_index as u64)),
                        )?;
                        //println!("[{}] {}: {}", self.tag(), offset, store_index);
                        offset += 1;
                    }
                    store_index += 1;
                }
                Ok(())
            },
        )
    }

    pub(crate) fn tag(&self) -> String {
        self.tag.clone()
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
    /// Query offset
    pub query_offset: i32,
}

impl<F: FieldExt> ConstraintBuilder<F> {
    pub(crate) fn new(max_degree: usize) -> Self {
        ConstraintBuilder {
            constraints: Vec::new(),
            max_degree,
            conditions: Vec::new(),
            lookups: Vec::new(),
            lookup_tables: Vec::new(),
            query_offset: 0,
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

    pub(crate) fn get_query_offset(&self) -> i32 {
        self.query_offset
    }

    pub(crate) fn set_query_offset(&mut self, query_offset: i32) {
        self.query_offset = query_offset;
    }
}

pub(crate) fn merge_lookups<F: FieldExt>(
    cb: &mut ConstraintBuilder<F>,
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

pub(crate) fn merge_values<F: FieldExt>(
    cb: &mut ConstraintBuilder<F>,
    values: Vec<(Expression<F>, Vec<Expression<F>>)>,
) -> (Expression<F>, Vec<Expression<F>>) {
    let selector = sum::expr(values.iter().map(|(condition, _)| condition.expr()));
    // Sanity checks (can be removed, here for safety)
    crate::circuit!([meta, cb], {
        require!(selector => bool);
    });
    merge_values_unsafe(values)
}

pub(crate) fn merge_values_unsafe<F: FieldExt>(
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
            condition.expr() * values.get(idx).unwrap_or_else(|| &default_value).expr()
        }));
    }
    (selector, merged_values)
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

impl<F: FieldExt> Expressable<F> for std::ops::Range<isize> {
    fn to_expr_vec(&self) -> Vec<Expression<F>> {
        self.clone()
            .map(|e| e.to_expr_vec()[0].expr())
            .collect::<Vec<_>>()
    }
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
impl_expressable!(isize);
impl_expressable!(Expression<F>);
impl_expressable!(DataTransition<F>);
impl_expressable!(Cell<F>);

/// Trait around select
pub trait Selectable<F> {
    /// Selects between itself and another value using the given condition
    fn select(&self, condition: Expression<F>, other: &Self) -> Self;
    /// Returns itself if the condition holds, else zero
    fn conditional(&self, condition: Expression<F>) -> Self;
    /// Adds 2 Selectables together
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

/// Implementation trait `Selectable` for type able to be casted to an
/// expression
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

/// Trait around RLC
pub trait RLCable<F> {
    /// Returns the RLC of itself
    fn rlc(&self, r: &[Expression<F>]) -> Expression<F>;
}

impl<F: FieldExt, E: Expressable<F>> RLCable<F> for Vec<E> {
    fn rlc(&self, r: &[Expression<F>]) -> Expression<F> {
        rlc::expr(&self.to_expr_vec(), r)
    }
}

impl<F: FieldExt, E: Expressable<F>> RLCable<F> for [E] {
    fn rlc(&self, r: &[Expression<F>]) -> Expression<F> {
        rlc::expr(&self.to_expr_vec(), r)
    }
}

/// Trait around RLC
pub trait RLCChainable<F> {
    /// Returns the RLC of itself with a starting rlc/multiplier
    fn rlc_chain(&self, other: Expression<F>) -> Expression<F>;
}

impl<F: FieldExt> RLCChainable<F> for (Expression<F>, Expression<F>) {
    fn rlc_chain(&self, other: Expression<F>) -> Expression<F> {
        self.0.expr() + self.1.expr() * other.expr()
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
        ConstraintBuilder::<F>::new(0)
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

        cases.apply_conditions()
    }};
}

/// ifx
#[macro_export]
macro_rules! _ifx {
    ($cb:expr, $($condition:expr),* => $when_true:block $(elsex $when_false:block)?)  => {{
        let condition = and::expr([$($condition.expr()),*]);

        $cb.push_condition(condition.expr());
        let ret_true = $when_true.clone();
        $cb.pop_condition();

        #[allow(unused_assignments, unused_mut)]
        let mut ret = ret_true.conditional(condition.expr());
        $(
            // In if/else cases, the condition needs to be boolean
            _require!($cb, condition => bool);

            $cb.push_condition(not::expr(condition.expr()));
            let ret_false = $when_false;
            $cb.pop_condition();

            ret = ret_true.select(condition.expr(), &ret_false);
        )*
        ret
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
        use crate::circuit_tools::{Conditionable, Expressable, Selectable};

        #[allow(unused_macros)]
        macro_rules! f {
            ($column:expr, $rot:expr) => {{
                $meta.query_fixed($column.clone(), Rotation($cb.get_query_offset() + ($rot as i32)))
            }};
            ($column:expr) => {{
                $meta.query_fixed($column.clone(), Rotation($cb.get_query_offset()))
            }};
        }

        #[allow(unused_macros)]
        macro_rules! a {
            ($column:expr, $rot:expr) => {{
                $meta.query_advice($column.clone(), Rotation($cb.get_query_offset() + ($rot as i32)))
            }};
            ($column:expr) => {{
                $meta.query_advice($column.clone(), Rotation($cb.get_query_offset()))
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
