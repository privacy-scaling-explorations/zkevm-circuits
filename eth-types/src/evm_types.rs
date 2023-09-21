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

/// According to EIP-3541, disallow new code starting with 0xEF to be deployed.
pub const INVALID_INIT_CODE_FIRST_BYTE: u8 = 0xef;
/// Once per word of the init code when creating a contract.
pub const INIT_CODE_WORD_GAS: u64 = 2;
/// Quotient for max refund of gas used
pub const MAX_REFUND_QUOTIENT_OF_GAS_USED: usize = 5;
/// Gas stipend when CALL or CALLCODE is attached with value.
pub const GAS_STIPEND_CALL_WITH_VALUE: u64 = 2300;

/// This constant ((2^32 - 1) * 32) is the highest number that can be used without overflowing the
/// square operation of gas calculation.
/// <https://github.com/ethereum/go-ethereum/blob/e6b6a8b738069ad0579f6798ee59fde93ed13b43/core/vm/gas_table.go#L38>
pub const MAX_EXPANDED_MEMORY_ADDRESS: u64 = 0x1FFFFFFFE0;

#[cfg(feature = "shanghai")]
mod gas_create {
    // For EIP-3860, there are 2 special gas cost constraints in geth
    // [gasCreate2Eip3860](https://github.com/ethereum/go-ethereum/blob/eb83e7c54021573eaceb14236af3a7a8c64f6027/core/vm/gas_table.go#L321)
    // (similar for CREATE).
    // 1. size <= 49152 (MaxInitCodeSize)
    // 2. gasCost = memoryGasCost + (2 + 6) * ((size + 31) / 32) should not
    //    overflow for Uint64.
    // No need to constrain the second condition, since the maximum gas cost
    // cannot overflow for Uint64 (36028809887100925 calculated by
    // `memorySize = 0x1FFFFFFFE0` and `size = 49152`) if the first condition is
    // satisfied.

    /// Maximum init code size to permit in a creation transaction and create instructions.
    pub const MAX_INIT_CODE_SIZE: u64 = 2 * super::MAX_CODE_SIZE;
    /// Once per word of the init code when creating a contract.
    pub const INIT_CODE_WORD_GAS: u64 = 2;
    /// Gas per code word for CREATE.
    pub const CREATE_GAS_PER_CODE_WORD: u64 = INIT_CODE_WORD_GAS;
    /// Gas per code word for CREATE2.
    pub const CREATE2_GAS_PER_CODE_WORD: u64 = INIT_CODE_WORD_GAS + super::GasCost::COPY_SHA3.0;
}
#[cfg(not(feature = "shanghai"))]
mod gas_create {
    /// Maximum init code size (0x1FFFFFFFE0) if not EIP-3860.
    pub use super::MAX_EXPANDED_MEMORY_ADDRESS as MAX_INIT_CODE_SIZE;
    /// Gas per code word for CREATE if not EIP-3860.
    pub const CREATE_GAS_PER_CODE_WORD: u64 = 0;
    /// Gas per code word for CREATE2 if not EIP-3860.
    pub const CREATE2_GAS_PER_CODE_WORD: u64 = super::GasCost::COPY_SHA3;
}
pub use gas_create::*;

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
