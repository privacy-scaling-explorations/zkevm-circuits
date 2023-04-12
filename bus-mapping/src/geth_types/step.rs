//! Types needed for execution steps

use eth_types::evm_types::OpcodeId;

use crate::operation::RwTableTag;

///
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ZkEvmExecStep {
    /// The index in the Transaction calls
    pub call_index: usize,
    /// Number of rw operations performed via a copy event in this step.
    pub copy_rw_counter_delta: u64,
    /// The Read/Write counter before the step
    pub rw_counter: usize,
    /// The program counter
    pub program_counter: u64,
    /// The stack pointer
    pub stack_pointer: usize,
    /// The amount of gas left
    pub gas_left: u64,
    /// The gas cost in this step
    pub gas_cost: u64,
    /// The memory size in bytes
    pub memory_size: u64,
    /// The counter for reversible writes at the beginning of the step
    pub reversible_write_counter: usize,
    /// The number of reversible writes from this step
    pub reversible_write_counter_delta: usize,
    /// The counter for log index within tx
    pub log_id: usize,
    /// The indices in the RW trace incurred in this step
    pub rw_indices: Vec<(RwTableTag, usize)>,
    /// The opcode corresponds to the step
    pub opcode: Option<OpcodeId>,
}
