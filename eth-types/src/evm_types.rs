//! Evm types needed for parsing instruction sets as well

// use serde::{Deserialize, Serialize};
// use std::fmt;

pub mod gas_utils;
pub mod memory;
pub mod opcode_ids;
pub mod stack;
pub mod storage;

pub use memory::{Memory, MemoryAddress};
pub use opcode_ids::OpcodeId;
pub use stack::{Stack, StackAddress};
pub use storage::Storage;

/// Quotient for max refund of gas used
pub const MAX_REFUND_QUOTIENT_OF_GAS_USED: usize = 5;
/// Gas stipend when CALL or CALLCODE is attached with value.
pub const GAS_STIPEND_CALL_WITH_VALUE: u64 = 2300;

/// Defines the gas consumption.
pub struct GasCost;

impl GasCost {
    /// Constant cost for free step
    pub const ZERO: u64 = 0;
    /// Constant cost for jumpdest step, only takes one gas
    pub const ONE: u64 = 1;
    /// Constant cost for quick step
    pub const QUICK: u64 = 2;
    /// Constant cost for fastest step
    pub const FASTEST: u64 = 3;
    /// Constant cost for fast step
    pub const FAST: u64 = 5;
    /// Constant cost for mid step
    pub const MID: u64 = 8;
    /// Constant cost for slow step
    pub const SLOW: u64 = 10;
    /// Constant cost for ext step
    pub const EXT: u64 = 20;
    /// Constant cost for SHA3
    pub const SHA3: u64 = 30;
    /// Constant cost for SELFDESTRUCT
    pub const SELFDESTRUCT: u64 = 5000;
    /// Constant cost for CREATE and CREATE2
    pub const CREATE: u64 = 32000;
    /// Constant cost for copying every word
    pub const COPY: u64 = 3;
    /// Constant cost for copying every word, specifically in the case of SHA3
    /// opcode.
    pub const COPY_SHA3: u64 = 6;
    /// Constant cost for accessing account or storage key
    pub const WARM_ACCESS: u64 = 100;
    /// Constant cost for a cold SLOAD
    pub const COLD_SLOAD: u64 = 2100;
    /// Constant cost for a cold account access
    pub const COLD_ACCOUNT_ACCESS: u64 = 2600;
    /// SSTORE reentrancy sentry
    pub const SSTORE_SENTRY: u64 = 2300;
    /// Constant cost for a storage set
    pub const SSTORE_SET: u64 = 20000;
    /// Constant cost for a storage reset
    pub const SSTORE_RESET: u64 = 2900;
    /// Constant cost for a storage clear. EIP-3529 changed it to 4800 from
    /// 15000.
    pub const SSTORE_CLEARS_SCHEDULE: u64 = 4800;
    /// Constant cost for a non-creation transaction
    pub const TX: u64 = 21000;
    /// Constant cost for a creation transaction
    pub const CREATION_TX: u64 = 53000;
    /// Constant cost for calling with non-zero value
    pub const CALL_WITH_VALUE: u64 = 9000;
    /// Constant cost for turning empty account into non-empty account
    pub const NEW_ACCOUNT: u64 = 25000;
    /// Cost per byte of deploying a new contract
    pub const CODE_DEPOSIT_BYTE_COST: u64 = 200;
    /// Denominator of quadratic part of memory expansion gas cost
    pub const MEMORY_EXPANSION_QUAD_DENOMINATOR: u64 = 512;
    /// Coefficient of linear part of memory expansion gas cost
    pub const MEMORY_EXPANSION_LINEAR_COEFF: u64 = 3;
    /// Constant gas for LOG[0-4] op codes
    pub const LOG: u64 = 375;
    /// Times ceil exponent byte size for the EXP instruction, EIP-158 changed
    /// it from 10 to 50.
    pub const EXP_BYTE_TIMES: u64 = 50;
}
