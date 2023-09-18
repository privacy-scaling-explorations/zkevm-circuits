use super::*;
use crate::{
    circuit,
    circuit_tools::{
        cached_region::CachedRegion, cell_manager::CellType, constraint_builder::ConstraintBuilder,
    },
};
use serde::{Deserialize, Serialize};

/// The types of proofs in the MPT table
#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub enum MPTProofType {
    /// Disabled
    Disabled,
    /// Nonce updated
    NonceChanged = AccountFieldTag::Nonce as isize,
    /// Balance updated
    BalanceChanged = AccountFieldTag::Balance as isize,
    /// Code hash updated
    CodeHashChanged = AccountFieldTag::CodeHash as isize,
    /// Account destroyed
    AccountDestructed,
    /// Account does not exist
    AccountDoesNotExist,
    /// Storage updated
    StorageChanged,
    /// Storage does not exist
    StorageDoesNotExist,
}
impl_expr!(MPTProofType);

impl From<AccountFieldTag> for MPTProofType {
    fn from(tag: AccountFieldTag) -> Self {
        match tag {
            AccountFieldTag::Nonce => Self::NonceChanged,
            AccountFieldTag::Balance => Self::BalanceChanged,
            AccountFieldTag::CodeHash => Self::CodeHashChanged,
            AccountFieldTag::NonExisting => Self::AccountDoesNotExist,
        }
    }
}

/// The MptTable shared between MPT Circuit and State Circuit
#[derive(Clone, Copy, Debug)]
pub struct MptTable {
    /// Account address
    pub address: Column<Advice>,
    /// Storage address
    pub storage_key: word::Word<Column<Advice>>,
    /// Proof type
    pub proof_type: Column<Advice>,
    /// New MPT root
    pub new_root: word::Word<Column<Advice>>,
    /// Previous MPT root
    pub old_root: word::Word<Column<Advice>>,
    /// New value
    pub new_value: word::Word<Column<Advice>>,
    /// Old value
    pub old_value: word::Word<Column<Advice>>,
}

impl<F: Field> LookupTable<F> for MptTable {
    fn columns(&self) -> Vec<Column<Any>> {
        vec![
            self.address,
            self.storage_key.lo(),
            self.storage_key.hi(),
            self.proof_type,
            self.new_root.lo(),
            self.new_root.hi(),
            self.old_root.lo(),
            self.old_root.hi(),
            self.new_value.lo(),
            self.new_value.hi(),
            self.old_value.lo(),
            self.old_value.hi(),
        ]
        .into_iter()
        .map(|col| col.into())
        .collect::<Vec<Column<Any>>>()
    }

    fn annotations(&self) -> Vec<String> {
        vec![
            String::from("address"),
            String::from("storage_key_lo"),
            String::from("storage_key_hi"),
            String::from("proof_type"),
            String::from("new_root_lo"),
            String::from("new_root_hi"),
            String::from("old_root_lo"),
            String::from("old_root_hi"),
            String::from("new_value_lo"),
            String::from("new_value_hi"),
            String::from("old_value_lo"),
            String::from("old_value_hi"),
        ]
    }
}

impl MptTable {
    /// Construct a new MptTable
    pub(crate) fn construct<F: Field>(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            address: meta.advice_column(),
            storage_key: word::Word::new([meta.advice_column(), meta.advice_column()]),
            proof_type: meta.advice_column(),
            new_root: word::Word::new([meta.advice_column(), meta.advice_column()]),
            old_root: word::Word::new([meta.advice_column(), meta.advice_column()]),
            new_value: word::Word::new([meta.advice_column(), meta.advice_column()]),
            old_value: word::Word::new([meta.advice_column(), meta.advice_column()]),
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn constrain<F: Field, C: CellType>(
        &self,
        meta: &mut VirtualCells<'_, F>,
        cb: &mut ConstraintBuilder<F, C>,
        address: Expression<F>,
        proof_type: Expression<F>,
        storage_key: word::Word<Expression<F>>,
        new_root: word::Word<Expression<F>>,
        old_root: word::Word<Expression<F>>,
        new_value: word::Word<Expression<F>>,
        old_value: word::Word<Expression<F>>,
    ) {
        circuit!([meta, cb], {
            require!(a!(self.address) => address);
            require!([a!(self.storage_key.lo()), a!(self.storage_key.hi())] => storage_key);
            require!(a!(self.proof_type) => proof_type);
            require!([a!(self.new_root.lo()), a!(self.new_root.hi())] => new_root);
            require!([a!(self.old_root.lo()), a!(self.old_root.hi())] => old_root);
            require!([a!(self.new_value.lo()), a!(self.new_value.hi())] => new_value);
            require!([a!(self.old_value.lo()), a!(self.old_value.hi())] => old_value);
        })
    }

    pub(crate) fn assign<F: Field>(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        row: &MptUpdateRow<Value<F>>,
    ) -> Result<(), Error> {
        unimplemented!();

        for (column, value) in <MptTable as LookupTable<F>>::advice_columns(self)
            .iter()
            .zip_eq(row.values())
        {

            region.assign_advice(|| "assign mpt table row value", *column, offset, || value)?;
        }
        Ok(())
    }

    pub(crate) fn assign_cached<F: Field>(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        row: &MptUpdateRow<Value<F>>,
    ) -> Result<(), Error> {
        for (column, value) in <MptTable as LookupTable<F>>::advice_columns(self)
            .iter()
            .zip_eq(row.values())
        {
            region.assign_advice(|| "assign mpt table row value", *column, offset, || value)?;
        }
        Ok(())
    }

    pub(crate) fn load<F: Field>(
        &self,
        layouter: &mut impl Layouter<F>,
        updates: &MptUpdates,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "mpt table",
            |mut region| self.load_with_region(&mut region, updates),
        )
    }

    pub(crate) fn load_with_region<F: Field>(
        &self,
        region: &mut Region<'_, F>,
        updates: &MptUpdates,
    ) -> Result<(), Error> {
        for (offset, row) in updates.table_assignments().iter().enumerate() {
            self.assign(region, offset, row)?;
        }
        Ok(())
    }
}
