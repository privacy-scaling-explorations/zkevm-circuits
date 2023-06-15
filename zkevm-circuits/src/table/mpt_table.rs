use super::*;

/// The types of proofs in the MPT table
#[derive(Clone, Copy, Debug)]
pub enum MPTProofType {
    /// Nonce updated
    NonceMod = AccountFieldTag::Nonce as isize,
    /// Balance updated
    BalanceMod = AccountFieldTag::Balance as isize,
    /// Code hash exists
    CodeHashMod = AccountFieldTag::CodeHash as isize,
    /// Account does not exist
    NonExistingAccountProof = AccountFieldTag::NonExisting as isize,
    /// Storage updated
    StorageMod,
    /// Storage does not exist
    NonExistingStorageProof,
}
impl_expr!(MPTProofType);

impl From<AccountFieldTag> for MPTProofType {
    fn from(tag: AccountFieldTag) -> Self {
        match tag {
            AccountFieldTag::Nonce => Self::NonceMod,
            AccountFieldTag::Balance => Self::BalanceMod,
            AccountFieldTag::CodeHash => Self::CodeHashMod,
            AccountFieldTag::NonExisting => Self::NonExistingAccountProof,
        }
    }
}

/// The MptTable shared between MPT Circuit and State Circuit
#[derive(Clone, Copy, Debug)]
pub struct MptTable([Column<Advice>; 12]);

impl<F: Field> LookupTable<F> for MptTable {
    fn columns(&self) -> Vec<Column<Any>> {
        self.0.iter().map(|&col| col.into()).collect()
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
        Self([
            meta.advice_column(), // Address
            meta.advice_column(), // Storage key lo
            meta.advice_column(), // Storage key hi
            meta.advice_column(), // Proof type
            meta.advice_column(), // New root lo
            meta.advice_column(), // New root hi
            meta.advice_column(), // Old root lo
            meta.advice_column(), // Old root hi
            meta.advice_column(), // New value lo
            meta.advice_column(), // New value hi
            meta.advice_column(), // Old value lo
            meta.advice_column(), // Old value hi
        ])
    }

    pub(crate) fn assign<F: Field>(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        row: &MptUpdateRow<Value<F>>,
    ) -> Result<(), Error> {
        for (column, value) in self.0.iter().zip_eq(row.values()) {
            region.assign_advice(|| "assign mpt table row value", *column, offset, || *value)?;
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
