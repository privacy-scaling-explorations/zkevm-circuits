//! Memory
use crate::{
    util::{query_expression, Expr},
};
use eth_types::{Field};
use halo2_proofs::{
    circuit::Value,
    plonk::{
        Advice, Column, ConstraintSystem, Error, Expression,
    },
    poly::Rotation,
};
use itertools::Itertools;
use std::{
    collections::HashMap,
    ops::{Index, IndexMut}, marker::PhantomData,
};

use super::{
    cached_region::CachedRegion,
    cell_manager::{CellType, CellManager},
    constraint_builder::ConstraintBuilder,
};

#[derive(Clone, Debug, Default)]
pub(crate) struct Memory<F: Field, C: CellType, MB: MemoryBank<F, C>> {
    // TODO(Cecilia): want to use dynamic dispatch
    // i.e. dyn MemoryBank<F, C> but trait with generic param is not object safe
    pub(crate) banks: HashMap<C, MB>,
    _phantom: PhantomData<F>
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
    pub(crate) fn new(
        cm: &mut CellManager<F, C>, 
        meta: &mut ConstraintSystem<F>,
        tags: Vec<(C, C, u8)>,
        offset: usize,
    ) -> Self {
        let mut banks = HashMap::new();
        tags
            .into_iter()
            .for_each(|(data_tag, table_tag, phase)| {
                banks.insert(
                    data_tag, 
                    MB::new(meta, cm, (data_tag, table_tag), phase, offset)
                );
            });
        Self { 
            banks,
            _phantom: PhantomData
        }
    }

    pub(crate) fn get_columns(&self) -> Vec<Column<Advice>> {
        self.banks
        .values()
        .fold( Vec::new(),|mut acc, bank| {
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
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        height: usize,
    ) -> Result<(), Error> {
        for (_, bank) in self.banks.iter() {
            bank.assign(region, height)?;
        }
        Ok(())
    }

    pub(crate) fn tags(&self) -> Vec<C> {
        self.banks.iter().map(|(_, bank)| bank.tag().0).collect()
    }
}


pub(crate) trait MemoryBank<F: Field, C: CellType>: Clone {
    fn new(meta: &mut ConstraintSystem<F>, cm: &mut CellManager<F, C>, tag: (C, C), phase: u8, offset: usize) -> Self;
    fn store(&mut self, cb: &mut ConstraintBuilder<F, C>, values: &[Expression<F>]) -> Expression<F>;
    fn load(&mut self, cb: &mut ConstraintBuilder<F, C>, load_offset: Expression<F>, values: &[Expression<F>]);
    fn columns(&self) -> Vec<Column<Advice>>;
    fn tag(&self) -> (C, C);
    fn witness_store(&mut self, offset: usize, values: &[F]);
    fn witness_load(&self, offset: usize) -> Vec<F>;
    fn build_constraints(&self, cb: &mut ConstraintBuilder<F, C>, q_start: Expression<F>);
    fn assign(&self, region: &mut CachedRegion<'_, '_, F>, height: usize) -> Result<(), Error>;
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
    // TODO(Cecilia): get rid of this when we kill regions
    local_conditions: Vec<(usize, Expression<F>)>,
}

impl<F: Field, C: CellType> RwBank<F, C> {
    pub(crate) fn prepend_key(&self, values: &[Expression<F>]) -> Vec<Expression<F>> {
        [&[self.cur.expr() + 1.expr()], values].concat().to_vec()
    }

    pub(crate) fn prepend_offset(&self, values: &[Expression<F>], offset: Expression<F>) -> Vec<Expression<F>> {
        [&[self.cur.expr() - offset], values].concat().to_vec()
    }
}

impl<F: Field, C: CellType> MemoryBank<F, C> for RwBank<F, C> {
    fn new(
        meta: &mut ConstraintSystem<F>,
        cm: &mut CellManager<F, C>, 
        tag: (C, C),
        phase: u8,
        offset: usize,
    ) -> Self {
        let rw: Vec<Column<Advice>> = [tag.0, tag.1].iter()
            .map(|t| {
                let config = (t.clone(), 1usize, phase, false);
                cm.add_celltype(meta, config, offset);
                cm.get_typed_columns(t.clone())[0].column
            }).collect();
        let key = meta.advice_column();
        let (cur, next) = query_expression(meta, |meta| {
            (
                meta.query_advice(key, Rotation(0)),
                meta.query_advice(key, Rotation(1))
            )   
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
        }
    }

    fn store(
        &mut self, 
        cb: &mut ConstraintBuilder<F, C>, 
        values: &[Expression<F>]
    ) -> Expression<F> {
        let values = self.prepend_key(values);
        cb.store_table(
            Box::leak(format!("{:?} store", self.tag.1).into_boxed_str()),
            self.tag.1, 
            values.clone(), 
            true, 
            true, 
            false
        );
        self.local_conditions.push((cb.region_id, cb.get_condition_expr()));
        values[0].expr()
    }

    fn load(
        &mut self, 
        cb: &mut ConstraintBuilder<F, C>, 
        load_offset: Expression<F>, 
        values: &[Expression<F>]
    ) {
        let values = self.prepend_offset(values, load_offset);
        cb.add_lookup(
            Box::leak(format!("{:?} load", self.tag.0).into_boxed_str()), 
            self.tag.0, 
            values, 
            false, 
            true, 
            true, 
            false
        );
    }

    fn tag(&self) -> (C, C) {
        self.tag
    }

    fn columns(&self) -> Vec<Column<Advice>> {
        vec![self.key, self.reads, self.writes]
    }

    fn build_constraints(
        &self, 
        cb: &mut ConstraintBuilder<F, C>, 
        q_start: Expression<F>
    ) {
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

    fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        height: usize,
    ) -> Result<(), Error> {
        // Pad to the full circuit (necessary for reads)
        let mut store_offsets = self.store_offsets.clone();
        store_offsets.push(height);

        // TODO(Brecht): partial updates
        let mut offset = 0;
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
        Ok(())
    }
}