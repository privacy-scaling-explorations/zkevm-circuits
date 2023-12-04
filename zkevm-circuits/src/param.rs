/// Maximum number of bytes that an integer can fit in field without wrapping
/// around.
pub(crate) const MAX_N_BYTES_INTEGER: usize = 31;

// Number of bytes an EVM word has.
pub(crate) const N_BYTES_WORD: usize = 32;

// Number of bytes an half EVM word has.
pub(crate) const N_BYTES_HALF_WORD: usize = N_BYTES_WORD / 2;

// Number of bytes an u64 has.
pub(crate) const N_BYTES_U64: usize = 8;

pub(crate) const N_BYTES_ACCOUNT_ADDRESS: usize = 20;
