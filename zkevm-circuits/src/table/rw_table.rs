use halo2_proofs::circuit::AssignedCell;

use super::*;

/// The RwTable shared between EVM Circuit and State Circuit, which contains
/// traces of the EVM state operations.
#[derive(Clone, Copy, Debug)]
pub struct RwTable {
    /// Read Write Counter
    pub rw_counter: Column<Advice>,
    /// Is Write
    pub is_write: Column<Advice>,
    /// Tag
    pub tag: Column<Advice>,
    /// Key1 (Id)
    pub id: Column<Advice>,
    /// Key2 (Address)
    pub address: Column<Advice>,
    /// Key3 (FieldTag)
    pub field_tag: Column<Advice>,
    /// Key3 (StorageKey)
    pub storage_key: word::Word<Column<Advice>>,
    /// Value
    pub value: word::Word<Column<Advice>>,
    /// Value Previous
    pub value_prev: word::Word<Column<Advice>>,
    /// InitVal (Committed Value)
    pub init_val: word::Word<Column<Advice>>,
}

impl<F: Field> LookupTable<F> for RwTable {
    fn columns(&self) -> Vec<Column<Any>> {
        vec![
            self.rw_counter.into(),
            self.is_write.into(),
            self.tag.into(),
            self.id.into(),
            self.address.into(),
            self.field_tag.into(),
            self.storage_key.lo().into(),
            self.storage_key.hi().into(),
            self.value.lo().into(),
            self.value.hi().into(),
            self.value_prev.lo().into(),
            self.value_prev.hi().into(),
            self.init_val.lo().into(),
            self.init_val.hi().into(),
        ]
    }

    fn annotations(&self) -> Vec<String> {
        vec![
            String::from("rw_counter"),
            String::from("is_write"),
            String::from("tag"),
            String::from("id"),
            String::from("address"),
            String::from("field_tag"),
            String::from("storage_key_lo"),
            String::from("storage_key_hi"),
            String::from("value_lo"),
            String::from("value_hi"),
            String::from("value_prev_lo"),
            String::from("value_prev_hi"),
            String::from("init_val_lo"),
            String::from("init_val_hi"),
        ]
    }
}

type RwTableFirstNLastAssignedCell<F> = (Vec<AssignedCell<F, F>>, Vec<AssignedCell<F, F>>);

impl RwTable {
    /// Construct a new RwTable
    pub fn construct<F: Field>(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            rw_counter: meta.advice_column(),
            is_write: meta.advice_column(),
            tag: meta.advice_column(),
            id: meta.advice_column(),
            address: meta.advice_column(),
            field_tag: meta.advice_column(),
            storage_key: word::Word::new([meta.advice_column(), meta.advice_column()]),
            value: word::Word::new([meta.advice_column(), meta.advice_column()]),
            value_prev: word::Word::new([meta.advice_column(), meta.advice_column()]),
            init_val: word::Word::new([meta.advice_column(), meta.advice_column()]),
        }
    }
    fn assign<F: Field>(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        row: &RwRow<Value<F>>,
    ) -> Result<Vec<AssignedCell<F, F>>, Error> {
        let mut assigned_cells = vec![];
        for (column, value) in [
            (self.rw_counter, row.rw_counter),
            (self.is_write, row.is_write),
            (self.tag, row.tag),
            (self.id, row.id),
            (self.address, row.address),
            (self.field_tag, row.field_tag),
        ] {
            assigned_cells.push(region.assign_advice(
                || "assign rw row on rw table",
                column,
                offset,
                || value,
            )?);
        }
        for (column, value) in [
            (self.storage_key, row.storage_key),
            (self.value, row.value),
            (self.value_prev, row.value_prev),
            (self.init_val, row.init_val),
        ] {
            assigned_cells.extend(
                value
                    .assign_advice(region, || "assign rw row on rw table", column, offset)?
                    .limbs
                    .clone(),
            );
        }

        Ok(assigned_cells)
    }

    /// Assign the `RwTable` from a `RwMap`, following the same
    /// table layout that the State Circuit uses.
    pub fn load<F: Field>(
        &self,
        layouter: &mut impl Layouter<F>,
        rws: &[Rw],
        n_rows: usize,
    ) -> Result<RwTableFirstNLastAssignedCell<F>, Error> {
        layouter.assign_region(
            || "rw table",
            |mut region| self.load_with_region(&mut region, rws, n_rows),
        )
    }

    pub(crate) fn load_with_region<F: Field>(
        &self,
        region: &mut Region<'_, F>,
        rws: &[Rw],
        n_rows: usize,
    ) -> Result<RwTableFirstNLastAssignedCell<F>, Error> {
        let mut assigned_cells = vec![];
        let (rows, _) = RwMap::table_assignments_prepad(rws, n_rows);
        for (offset, row) in rows.iter().enumerate() {
            let row_assigned_cells = self.assign(region, offset, &row.table_assignment())?;
            if offset == 0 || offset == rows.len() - 1 {
                assigned_cells.push(row_assigned_cells);
            }
        }
        Ok(assigned_cells.iter().cloned().collect_tuple().unwrap())
    }
}
