// Step dimension
pub(crate) const STEP_WIDTH: usize = 32;
pub(crate) const STEP_HEIGHT: usize = 10;
pub(crate) const NUM_CELLS_STEP_STATE: usize = 10;

// The number of bytes an u64 has.
pub(crate) const NUM_BYTES_U64: usize = 8;

/// The maximum number of bytes that a field element
/// can be broken down into without causing the value it
/// represents to overflow a single field element.
pub(crate) const MAX_BYTES_FIELD: usize = 31;

pub(crate) const STACK_START_IDX: usize = 1024;
pub(crate) const MAX_GAS_SIZE_IN_BYTES: usize = 8;
// Number of bytes that will be used of the address word.
// If any of the other more signficant bytes are used it will
// always result in an out-of-gas error.
pub(crate) const NUM_ADDRESS_BYTES_USED: usize = 5;
pub(crate) const MAX_MEMORY_SIZE_IN_BYTES: usize = 5;
// Number of bytes that will be used of prorgam counter. Although the maximum
// size of execution bytecode could be at most 128kB due to the size limit of a
// transaction, which could be covered by 3 bytes, we still support program
// counter to u64 as go-ethereum in case transaction size is allowed larger in
// the future.
pub(crate) const NUM_BYTES_PROGRAM_COUNTER: usize = NUM_BYTES_U64;
