//! Module for declaring constants.

/// Maximum number of bytes copied in a single iteration of internal steps like
/// CopyToMemory and CopyCodeToMemory.
pub const MAX_COPY_BYTES: usize = 32usize;

/// Maximum permitted code size for an account. Ref: https://github.com/ethereum/EIPs/blob/master/EIPS/eip-170.md
pub const MAX_CODE_SIZE: usize = 0x6000;
