// FIXME: decide a optimal circuit dimension in the future
// Circuit dimension
// NOTE: CIRCUIT_WIDTH should be divide 32 evenly for whole row byte lookup
pub const CIRCUIT_WIDTH: usize = 32;
pub const CIRCUIT_HEIGHT: usize = 10;

// Number of cells used for each purpose
// TODO: pub const NUM_CELL_CALL_INITIALIZATION_STATE: usize = ;
pub const NUM_CELL_OP_EXECUTION_STATE: usize = 7;
// FIXME: naive estimation, should be optmize to fit in the future
pub const NUM_CELL_OP_GADGET_SELECTOR: usize = 80;
pub const NUM_CELL_RESUMPTION: usize = 2;
