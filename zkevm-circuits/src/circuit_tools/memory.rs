//! Memory
use crate::util::{query_expression, Expr};
use eth_types::Field;
use halo2_proofs::{
    circuit::{Layouter, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression},
    poly::Rotation,
};
use std::{
    marker::PhantomData,
    ops::{Index, IndexMut},
};

use super::constraint_builder::ConstraintBuilder;

#[derive(Clone, Debug, Default)]
pub(crate) struct Memory<F> {
    columns: Vec<Column<Advice>>,
    banks: Vec<MemoryBank<F>>,
}

impl<F: Field> Memory<F> {
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

impl<F: Field, S: AsRef<str>> Index<S> for Memory<F> {
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

impl<F: Field, S: AsRef<str>> IndexMut<S> for Memory<F> {
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

impl<F: Field> MemoryBank<F> {
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
