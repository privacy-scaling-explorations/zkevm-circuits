use crate::evm_circuit::util::U256;
use crate::util::Expr;
use bus_mapping::evm::GasCost;
use halo2::{
    arithmetic::FieldExt,
    plonk::{Error, Expression},
};

/// Returns storage gas cost for a storage access.
#[derive(Clone, Debug)]
pub(crate) struct StorageGasGadget<F> {
    storage_gas_cost: Expression<F>,
}

impl<F: FieldExt> StorageGasGadget<F> {
    pub const GAS_STOR: GasCost = GasCost::COLD_SLOAD_COST; // TODO:

    pub(crate) fn construct() -> Self {
        // Calculate the gas cost for the storage expansion.
        let storage_gas_cost = Self::GAS_STOR.expr();

        Self { storage_gas_cost }
    }
    pub(crate) fn expr(&self) -> Expression<F> {
        // Return the new storage size and the storage expansion gas cost
        self.storage_gas_cost.clone()
    }
    pub(crate) fn assign(
        &self,
        _is_sload: Expression<F>,
        _address: U256,
        _value: U256,
    ) -> Result<F, Error> {
        // Return the new storage size and the storage expansion gas cost
        // TODO:
        Ok(F::from(1))
    }
}
