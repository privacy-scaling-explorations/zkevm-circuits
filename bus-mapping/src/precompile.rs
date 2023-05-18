//! precompile helpers

use eth_types::{evm_types::GasCost, Address};
use revm_precompile::{Precompile, Precompiles};
use strum::EnumIter;

/// Check if address is a precompiled or not.
pub fn is_precompiled(address: &Address) -> bool {
    Precompiles::berlin()
        .get(address.as_fixed_bytes())
        .is_some()
}

pub(crate) fn execute_precompiled(address: &Address, input: &[u8], gas: u64) -> (Vec<u8>, u64) {
    let Some(Precompile::Standard(precompile_fn)) = Precompiles::berlin()
        .get(address.as_fixed_bytes())  else {
        panic!("calling non-exist precompiled contract address")
    };

    match precompile_fn(input, gas) {
        Ok((gas_cost, return_value)) => (return_value, gas_cost),
        Err(_) => (vec![], gas),
    }
}

/// Addresses of the precompiled contracts.
#[derive(Copy, Clone, Debug, EnumIter)]
pub enum PrecompileCalls {
    /// Elliptic Curve Recovery
    ECRecover = 0x01,
    /// SHA2-256 hash function
    Sha256 = 0x02,
    /// Ripemd-160 hash function
    Ripemd160 = 0x03,
    /// Identity function
    Identity = 0x04,
    /// Modular exponentiation
    Modexp = 0x05,
    /// Point addition
    Bn128Add = 0x06,
    /// Scalar multiplication
    Bn128Mul = 0x07,
    /// Bilinear function
    Bn128Pairing = 0x08,
    /// Compression function
    Blake2F = 0x09,
}

impl From<PrecompileCalls> for u64 {
    fn from(value: PrecompileCalls) -> Self {
        value as u64
    }
}

impl From<PrecompileCalls> for usize {
    fn from(value: PrecompileCalls) -> Self {
        value as usize
    }
}

impl PrecompileCalls {
    /// Get the base gas cost for the precompile call.
    pub fn base_gas_cost(&self) -> GasCost {
        match self {
            Self::ECRecover => GasCost::PRECOMPILE_EC_RECOVER_BASE,
            Self::Sha256 => GasCost::PRECOMPILE_SHA256_BASE,
            Self::Ripemd160 => GasCost::PRECOMPILE_RIPEMD160_BASE,
            Self::Identity => GasCost::PRECOMPILE_IDENTITY_BASE,
            Self::Modexp => GasCost::PRECOMPILE_MODEXP,
            Self::Bn128Add => GasCost::PRECOMPILE_BN256ADD,
            Self::Bn128Mul => GasCost::PRECOMPILE_BN256MUL,
            Self::Bn128Pairing => GasCost::PRECOMPILE_BN256PAIRING,
            Self::Blake2F => GasCost::PRECOMPILE_BLAKE2F,
        }
    }
}
