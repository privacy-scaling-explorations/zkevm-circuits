//! Memory
use crate::util::{query_expression, Expr};
use eth_types::Field;
use halo2_proofs::{
    circuit::Value,
    plonk::{Advice, Column, ConstraintSystem, Error, Expression},
    poly::Rotation,
};
use std::{
    collections::HashMap,
    marker::PhantomData,
    ops::{Index, IndexMut},
};

use super::{
    cached_region::CachedRegion,
    cell_manager::{CellManager, CellType},
    constraint_builder::ConstraintBuilder,
};

#[derive(Clone, Debug, Default)]
pub(crate) struct Memory<F: Field, C: CellType, MB: MemoryBank<F, C>> {
    banks: HashMap<C, MB>,
    _phantom: PhantomData<F>,
    tag_counter: usize,
}

impl<F: Field, C: CellType, MB: MemoryBank<F, C>> Index<C> for Memory<F, C, MB> {
    type Output = MB;

    fn index(&self, tag: C) -> &Self::Output {
        if let Some(bank) = self.banks.get(&tag) {
            bank
        } else {
            unreachable!()
        }
    }
}

impl<F: Field, C: CellType, MB: MemoryBank<F, C>> IndexMut<C> for Memory<F, C, MB> {
    fn index_mut(&mut self, tag: C) -> &mut Self::Output {
        if let Some(bank) = self.banks.get_mut(&tag) {
            bank
        } else {
            unreachable!()
        }
    }
}

impl<F: Field, C: CellType, MB: MemoryBank<F, C>> Memory<F, C, MB> {
    pub(crate) fn new() -> Self {
        Self {
            banks: HashMap::new(),
            _phantom: PhantomData,
            tag_counter: 0,
        }
    }

    pub(crate) fn add_rw(
        &mut self,
        meta: &mut ConstraintSystem<F>,
        cb: &mut ConstraintBuilder<F, C>,
        cm: &mut CellManager<F, C>,
        tag: C,
        phase: u8,
    ) -> &MB {
        let table_tag = self.allocate_tag();
        let bank = MB::new(meta, cb, cm, (tag, table_tag), phase);
        self.add(bank)
    }

    pub(crate) fn add(&mut self, memory_bank: MB) -> &MB {
        let tag = memory_bank.tag();
        self.banks.insert(tag, memory_bank);
        &self.banks[&tag]
    }

    pub(crate) fn get_columns(&self) -> Vec<Column<Advice>> {
        self.banks.values().fold(Vec::new(), |mut acc, bank| {
            acc.extend(bank.columns().iter());
            acc
        })
    }

    pub(crate) fn build_constraints(
        &self,
        cb: &mut ConstraintBuilder<F, C>,
        q_start: Expression<F>,
    ) {
        for (_, bank) in self.banks.iter() {
            bank.build_constraints(cb, q_start.expr());
        }
    }

    pub(crate) fn assign(
        &mut self,
        region: &mut CachedRegion<'_, '_, F>,
        height: usize,
    ) -> Result<(), Error> {
        for (_, bank) in self.banks.iter_mut() {
            bank.assign(region, height)?;
        }
        Ok(())
    }

    pub(crate) fn allocate_tag(&mut self) -> C {
        let tag = C::create_type(self.tag_counter);
        self.tag_counter += 1;
        tag
    }
}

pub(crate) trait MemoryBank<F: Field, C: CellType>: Clone {
    fn new(
        meta: &mut ConstraintSystem<F>,
        cb: &mut ConstraintBuilder<F, C>,
        cm: &mut CellManager<F, C>,
        tag: (C, C),
        phase: u8,
    ) -> Self;
    fn store(
        &mut self,
        cb: &mut ConstraintBuilder<F, C>,
        values: &[Expression<F>],
    ) -> Expression<F>;
    fn load(
        &mut self,
        cb: &mut ConstraintBuilder<F, C>,
        load_offset: Expression<F>,
        values: &[Expression<F>],
    );
    fn columns(&self) -> Vec<Column<Advice>>;
    fn tag(&self) -> C;
    fn witness_store(&mut self, offset: usize, values: &[F]);
    fn witness_load(&self, offset: usize) -> Vec<F>;
    fn build_constraints(&self, cb: &mut ConstraintBuilder<F, C>, q_start: Expression<F>);
    fn assign(&mut self, region: &mut CachedRegion<'_, '_, F>, height: usize) -> Result<(), Error>;
}

pub(crate) fn insert_key<V: Clone>(key: V, values: &[V]) -> Vec<V> {
    [vec![key], values.to_owned()].concat().to_vec()
}

#[derive(Clone, Debug)]
pub(crate) struct RwBank<F, C> {
    tag: (C, C),
    key: Column<Advice>,
    reads: Column<Advice>,
    writes: Column<Advice>,
    store_offsets: Vec<usize>,
    stored_values: Vec<Vec<F>>,
    cur: Expression<F>,
    next: Expression<F>,
    local_conditions: Vec<(usize, Expression<F>)>,
    last_assigned_offset: usize,
}

impl<F: Field, C: CellType> RwBank<F, C> {
    pub(crate) fn key(&self) -> Expression<F> {
        self.cur.expr()
    }
    pub(crate) fn prepend_key(&self, values: &[Expression<F>]) -> Vec<Expression<F>> {
        [&[self.cur.expr() + 1.expr()], values].concat().to_vec()
    }

    pub(crate) fn prepend_offset(
        &self,
        values: &[Expression<F>],
        offset: Expression<F>,
    ) -> Vec<Expression<F>> {
        [&[self.cur.expr() - offset], values].concat().to_vec()
    }
}

impl<F: Field, C: CellType> MemoryBank<F, C> for RwBank<F, C> {
    fn new(
        meta: &mut ConstraintSystem<F>,
        cb: &mut ConstraintBuilder<F, C>,
        cm: &mut CellManager<F, C>,
        tag: (C, C),
        phase: u8,
    ) -> Self {
        let rw: Vec<Column<Advice>> = [tag.0, tag.1]
            .iter()
            .map(|t| {
                cm.add_columns(meta, cb, *t, phase, false, 1);
                cm.get_typed_columns(*t)[0].column
            })
            .collect();
        let key = meta.advice_column();
        let (cur, next, input, table) = query_expression(meta, |meta| {
            (
                meta.query_advice(key, Rotation::cur()),
                meta.query_advice(key, Rotation::next()),
                meta.query_advice(rw[0], Rotation::cur()),
                meta.query_advice(rw[1], Rotation::cur()),
            )
        });

        // Generate the memory lookup
        crate::circuit!([meta, cb], {
            require!((input) => @vec![table]);
        });

        Self {
            tag,
            key,
            reads: rw[0],
            writes: rw[1],
            store_offsets: Vec::new(),
            stored_values: Vec::new(),
            cur,
            next,
            local_conditions: Vec::new(),
            last_assigned_offset: 0,
        }
    }

    fn store(
        &mut self,
        cb: &mut ConstraintBuilder<F, C>,
        values: &[Expression<F>],
    ) -> Expression<F> {
        let key = self.key() + 1.expr();
        cb.store_tuple(
            Box::leak(format!("{:?} store", self.tag.1).into_boxed_str()),
            self.tag.1,
            insert_key(key.expr(), values),
        );
        self.local_conditions
            .push((cb.region_id, cb.get_condition_expr()));
        key
    }

    fn load(
        &mut self,
        cb: &mut ConstraintBuilder<F, C>,
        load_offset: Expression<F>,
        values: &[Expression<F>],
    ) {
        cb.store_tuple(
            Box::leak(format!("{:?} load", self.tag.0).into_boxed_str()),
            self.tag.0,
            insert_key(self.key() - load_offset.expr(), values),
        );
    }

    fn tag(&self) -> C {
        self.tag.0
    }

    fn columns(&self) -> Vec<Column<Advice>> {
        vec![self.key, self.reads, self.writes]
    }

    fn build_constraints(&self, cb: &mut ConstraintBuilder<F, C>, q_start: Expression<F>) {
        let condition = self
            .local_conditions
            .iter()
            .filter(|tc| tc.0 == cb.region_id)
            .fold(0.expr(), |acc, tc| acc + tc.1.expr());
        crate::circuit!([meta, cb], {
            ifx! {q_start => {
                require!(self.cur.expr() => 0);
            }}
            let description = format!("Dynamic lookup table {:?}", self.tag());
            require!(condition => bool);
            require!(description, self.next => self.cur.expr() + condition.expr());
        });
    }

    fn witness_store(&mut self, offset: usize, values: &[F]) {
        self.stored_values.push(values.to_vec());
        self.store_offsets.push(offset);
    }

    fn witness_load(&self, offset: usize) -> Vec<F> {
        self.stored_values[self.stored_values.len() - 1 - offset].clone()
    }

    fn assign(&mut self, region: &mut CachedRegion<'_, '_, F>, height: usize) -> Result<(), Error> {
        // Pad to the full circuit (necessary for reads)
        let mut store_offsets = self.store_offsets.clone();
        store_offsets.push(height);

        let mut offset = self.last_assigned_offset;
        for (store_index, &stored_offset) in store_offsets.iter().enumerate() {
            while offset <= stored_offset {
                region.assign_advice(
                    || "assign memory index".to_string(),
                    self.key,
                    offset,
                    || Value::known(F::from(store_index as u64)),
                )?;
                offset += 1;
            }
        }
        self.last_assigned_offset = height;
        Ok(())
    }
}
