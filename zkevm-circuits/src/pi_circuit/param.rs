use halo2_proofs::circuit::AssignedCell;

use crate::util::word::Word;

/// Fixed by the spec
pub(super) const BYTE_POW_BASE: u64 = 256;
pub(super) const EMPTY_TX_ROW_COUNT: usize = 1;
pub(super) const N_BYTES_ONE: usize = 1;

pub(super) type AssignedByteCells<F> = (AssignedCell<F, F>, Word<AssignedCell<F, F>>);
