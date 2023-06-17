//! Memory
use crate::util::{query_expression, Expr};
use eth_types::Field;
use halo2_proofs::{
    circuit::{Layouter, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression},
    poly::Rotation,
};
use std::ops::{Index, IndexMut};

use super::{cell_manager::CellType, constraint_builder::ConstraintBuilder};

#[derive(Clone, Debug, Default)]
pub(crate) struct Memory<F, C> {
    columns: Vec<Column<Advice>>,
    banks: Vec<MemoryBank<F, C>>,
}

impl<F: Field, C: CellType> Memory<F, C> {
    pub(crate) fn new(columns: Vec<Column<Advice>>) -> Self {
        Self {
            columns,
            banks: Vec::new(),
        }
    }

    pub(crate) fn allocate(&mut self, meta: &mut ConstraintSystem<F>, tag: C) -> &MemoryBank<F, C> {
        self.banks
            .push(MemoryBank::new(meta, self.columns[self.banks.len()], tag));
        self.banks.last().unwrap()
    }

    pub(crate) fn get(&self, tag: C) -> &MemoryBank<F, C> {
        for bank in self.banks.iter() {
            if bank.tag() == tag {
                return bank;
            }
        }
        unreachable!()
    }

    pub(crate) fn get_mut(&mut self, tag: C) -> &mut MemoryBank<F, C> {
        for bank in self.banks.iter_mut() {
            if bank.tag() == tag {
                return bank;
            }
        }
        unreachable!()
    }

    pub(crate) fn get_columns(&self) -> Vec<Column<Advice>> {
        self.columns.clone()
    }

    pub(crate) fn build_constraints(
        &self,
        cb: &mut ConstraintBuilder<F, C>,
        is_first_row: Expression<F>,
    ) {
        for bank in self.banks.iter() {
            bank.build_constraints(cb, is_first_row.expr());
            cb.generate_lookup_table_checks(bank.tag());
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

    pub(crate) fn tags(&self) -> Vec<C> {
        self.banks.iter().map(|bank| bank.tag()).collect()
    }
}

impl<F: Field, C: CellType> Index<C> for Memory<F, C> {
    type Output = MemoryBank<F, C>;

    fn index(&self, tag: C) -> &Self::Output {
        for bank in self.banks.iter() {
            if bank.tag() == tag {
                return bank;
            }
        }
        unreachable!()
    }
}

impl<F: Field, C: CellType> IndexMut<C> for Memory<F, C> {
    fn index_mut(&mut self, tag: C) -> &mut Self::Output {
        for bank in self.banks.iter_mut() {
            if bank.tag() == tag {
                return bank;
            }
        }
        unreachable!()
    }
}

#[derive(Clone, Debug)]
pub(crate) struct MemoryBank<F, C> {
    column: Column<Advice>,
    tag: C,
    cur: Expression<F>,
    next: Expression<F>,
    store_offsets: Vec<usize>,
    stored_values: Vec<Vec<F>>,
}

impl<F: Field, C: CellType> MemoryBank<F, C> {
    pub(crate) fn new(meta: &mut ConstraintSystem<F>, column: Column<Advice>, tag: C) -> Self {
        let mut cur = 0.expr();
        let mut next = 0.expr();
        query_expression(meta, |meta| {
            cur = meta.query_advice(column, Rotation::cur());
            next = meta.query_advice(column, Rotation::next());
        });
        Self {
            column,
            tag,
            cur,
            next,
            store_offsets: Vec::new(),
            stored_values: Vec::new(),
        }
    }

    pub(crate) fn key(&self) -> Expression<F> {
        self.cur.expr()
    }

    pub(crate) fn load(
        &self,
        description: &'static str,
        cb: &mut ConstraintBuilder<F, C>,
        offset: Expression<F>,
        values: &[Expression<F>],
    ) {
        self.load_with_key(description, cb, self.key() - offset, values);
    }

    pub(crate) fn load_with_key(
        &self,
        description: &'static str,
        cb: &mut ConstraintBuilder<F, C>,
        key: Expression<F>,
        values: &[Expression<F>],
    ) {
        cb.add_dynamic_lookup(description, self.tag(), self.insert_key(key, values), false, true, false);
    }

    pub(crate) fn store(
        &self,
        cb: &mut ConstraintBuilder<F, C>,
        values: &[Expression<F>],
    ) -> Expression<F> {
        let key = self.key() + 1.expr();
        self.store_with_key(cb, key.expr(), values);
        key
    }

    pub(crate) fn store_with_key(
        &self,
        cb: &mut ConstraintBuilder<F, C>,
        key: Expression<F>,
        values: &[Expression<F>],
    ) {
        cb.store_dynamic_table("memory store", self.tag(), self.insert_key(key, values));
    }

    pub(crate) fn witness_store(&mut self, offset: usize, values: &[F]) {
        self.stored_values.push(values.to_vec());
        self.store_offsets.push(offset);
    }

    pub(crate) fn witness_load(&self, offset: usize) -> Vec<F> {
        self.stored_values[self.stored_values.len() - 1 - offset].clone()
    }

    pub(crate) fn clear_witness_data(&mut self) {
        self.store_offsets.clear();
    }

    pub(crate) fn build_constraints(
        &self,
        cb: &mut ConstraintBuilder<F, C>,
        is_first_row: Expression<F>,
    ) {
        let lookup_table = cb.get_dynamic_table(self.tag());
        crate::circuit!([meta, cb], {
            ifx! {is_first_row => {
                require!(self.cur.expr() => 0);
            }}
            let description = format!("{:?}", self.tag());
            require!(description, self.next => self.cur.expr() + lookup_table.0);
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

                let mut offset = 0;
                for (store_index, &stored_offset) in store_offsets.iter().enumerate() {
                    while offset <= stored_offset {
                        region.assign_advice(
                            || "assign memory index".to_string(),
                            self.column,
                            offset,
                            || Value::known(F::from(store_index as u64)),
                        )?;
                        offset += 1;
                    }
                }
                Ok(())
            },
        )
    }

    pub(crate) fn tag(&self) -> C {
        self.tag
    }

    pub(crate) fn insert_key<V: Clone>(&self, key: V, values: &[V]) -> Vec<V> {
        [vec![key], values.to_owned()].concat().to_vec()
    }
}
