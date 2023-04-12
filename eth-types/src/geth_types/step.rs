//! Types needed for execution steps

///
#[derive(Debug, Default, Clone, PartialEq, Eq)]
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
}
