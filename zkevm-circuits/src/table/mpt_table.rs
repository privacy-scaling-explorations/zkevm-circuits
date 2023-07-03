use super::*;
use crate::{
    circuit,
    circuit_tools::{
        cached_region::CachedRegion, cell_manager::CellType, constraint_builder::ConstraintBuilder,
    },
};

/// The types of proofs in the MPT table
#[derive(Clone, Copy, Debug)]
pub enum MPTProofType {
    /// Disabled
    Disabled,
    /// Nonce updated
    NonceChanged = AccountFieldTag::Nonce as isize,
    /// Balance updated
    BalanceChanged = AccountFieldTag::Balance as isize,
    /// Code hash exists
    CodeHashExists = AccountFieldTag::CodeHash as isize,
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
            AccountFieldTag::CodeHash => Self::CodeHashExists,
            AccountFieldTag::NonExisting => Self::AccountDoesNotExist,
        }
    }
}

/// The MptTable shared between MPT Circuit and State Circuit
#[derive(Clone, Copy, Debug)]
pub struct MptTable {
    /// Account address
    pub address_rlc: Column<Advice>,
    /// Proof type
    pub proof_type: Column<Advice>,
    /// Storage address
    pub key_rlc: Column<Advice>,
    /// Old value
    pub value_prev: Column<Advice>,
    /// New value
    pub value: Column<Advice>,
    /// Previous MPT root
    pub root_prev: Column<Advice>,
    /// New MPT root
    pub root: Column<Advice>,
}

impl<F: Field> LookupTable<F> for MptTable {
    fn columns(&self) -> Vec<Column<Any>> {
        vec![
            self.address_rlc,
            self.proof_type,
            self.key_rlc,
            self.value_prev,
            self.value,
            self.root_prev,
            self.root,
        ]
        .into_iter()
        .map(|col| col.into())
        .collect::<Vec<Column<Any>>>()
    }

    fn annotations(&self) -> Vec<String> {
        vec![
            String::from("address"),
            String::from("proof_type"),
            String::from("storage_key"),
            String::from("old_value"),
            String::from("new_value"),
            String::from("old_root"),
            String::from("new_root"),
        ]
    }
}

impl MptTable {
    /// Construct a new MptTable
    pub(crate) fn construct<F: Field>(meta: &mut ConstraintSystem<F>) -> Self {
        // TODO(Brecht): everything except address and proof type needs to be
        // advice_column_in(SecondPhase)
        Self {
            address_rlc: meta.advice_column_in(SecondPhase),
            proof_type: meta.advice_column(),
            key_rlc: meta.advice_column_in(SecondPhase),
            value_prev: meta.advice_column_in(SecondPhase),
            value: meta.advice_column_in(SecondPhase),
            root_prev: meta.advice_column_in(SecondPhase),
            root: meta.advice_column_in(SecondPhase),
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn constrain<F: Field, C: CellType>(
        &self,
        meta: &mut VirtualCells<'_, F>,
        cb: &mut ConstraintBuilder<F, C>,
        address_rlc: Expression<F>,
        proof_type: Expression<F>,
        key_rlc: Expression<F>,
        value_prev: Expression<F>,
        value: Expression<F>,
        root_prev: Expression<F>,
        root: Expression<F>,
    ) {
        circuit!([meta, cb], {
            require!(a!(self.proof_type) => proof_type);
            require!(a!(self.address_rlc) => address_rlc);
            require!(a!(self.key_rlc) => key_rlc);
            require!(a!(self.value_prev) => value_prev);
            require!(a!(self.value) => value);
            require!(a!(self.root_prev) => root_prev);
            require!(a!(self.root) => root);
        })
    }

    pub(crate) fn assign<F: Field>(
        &self,
        region: &mut Region<'_, F>,
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
        randomness: Value<F>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "mpt table",
            |mut region| self.load_with_region(&mut region, updates, randomness),
        )
    }

    pub(crate) fn load_with_region<F: Field>(
        &self,
        region: &mut Region<'_, F>,
        updates: &MptUpdates,
        randomness: Value<F>,
    ) -> Result<(), Error> {
        for (offset, row) in updates.table_assignments(randomness).iter().enumerate() {
            self.assign(region, offset, row)?;
        }
        Ok(())
    }
}
