// FIXME: decide a optimal circuit dimension in the future
// Circuit dimension
// NOTE: CIRCUIT_WIDTH should be divide 32 evenly for whole row byte lookup
pub const CIRCUIT_WIDTH: usize = 32;
pub const CIRCUIT_HEIGHT: usize = 10;

// Number of cells used for each purpose
// TODO: pub const NUM_CELL_CALL_INITIALIZATION_STATE: usize = ;
pub const NUM_CELL_OP_EXECUTION_STATE: usize = 8;
// FIXME: naive estimation, should be optmize to fit in the future
pub const NUM_CELL_OP_GADGET_SELECTOR: usize = 80;
pub const NUM_CELL_RESUMPTION: usize = 2;

/// The maximum number of bytes that a field element
/// can be broken down into without causing the value it
/// represents to overflow a single field element.
pub const MAX_BYTES_FIELD: usize = 31;

pub const STACK_START_IDX: usize = 1024;
pub const MAX_GAS_SIZE_IN_BYTES: usize = 8;
// Number of bytes that will be used of the address word.
// If any of the other more signficant bytes are used it will
// always result in an out-of-gas error.
pub const NUM_ADDRESS_BYTES_USED: usize = 5;
pub const MAX_MEMORY_SIZE_IN_BYTES: usize = 5;
