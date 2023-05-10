use bus_mapping::{
    circuit_input_builder,
    error::{ExecError, OogError},
    evm::OpcodeId,
    operation,
};
use eth_types::evm_unimplemented;

use crate::{
    evm_circuit::{
        param::{N_BYTES_WORD, STACK_CAPACITY},
        step::ExecutionState,
    },
    table::RwTableTag,
};

/// Step executed in a transaction
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ExecStep {
    /// The index in the Transaction calls
    pub call_index: usize,
    /// The indices in the RW trace incurred in this step
    pub rw_indices: Vec<(RwTableTag, usize)>,
    /// Number of rw operations performed via a copy event in this step.
    pub copy_rw_counter_delta: u64,
    /// The execution state for the step
    pub execution_state: ExecutionState,
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
    /// The opcode corresponds to the step
    pub opcode: Option<OpcodeId>,
}

impl ExecStep {
    /// The memory size in word **before** this step
    pub fn memory_word_size(&self) -> u64 {
        // EVM always pads the memory size to word size
        // https://github.com/ethereum/go-ethereum/blob/master/core/vm/interpreter.go#L212-L216
        // Thus, the memory size must be a multiple of 32 bytes.
        assert_eq!(self.memory_size % N_BYTES_WORD as u64, 0);
        self.memory_size / N_BYTES_WORD as u64
    }
}

pub(super) fn step_convert(step: &circuit_input_builder::ExecStep) -> ExecStep {
    ExecStep {
        call_index: step.call_index,
        rw_indices: step
            .bus_mapping_instance
            .iter()
            .map(|x| {
                let tag = match x.target() {
                    operation::Target::Memory => RwTableTag::Memory,
                    operation::Target::Stack => RwTableTag::Stack,
                    operation::Target::Storage => RwTableTag::AccountStorage,
                    operation::Target::TxAccessListAccount => RwTableTag::TxAccessListAccount,
                    operation::Target::TxAccessListAccountStorage => {
                        RwTableTag::TxAccessListAccountStorage
                    }
                    operation::Target::TxRefund => RwTableTag::TxRefund,
                    operation::Target::Account => RwTableTag::Account,
                    operation::Target::CallContext => RwTableTag::CallContext,
                    operation::Target::TxReceipt => RwTableTag::TxReceipt,
                    operation::Target::TxLog => RwTableTag::TxLog,
                    operation::Target::Start => RwTableTag::Start,
                };
                (tag, x.as_usize())
            })
            .collect(),
        copy_rw_counter_delta: step.copy_rw_counter_delta,
        execution_state: ExecutionState::from(step),
        rw_counter: usize::from(step.rwc),
        program_counter: usize::from(step.pc) as u64,
        stack_pointer: STACK_CAPACITY - step.stack_size,
        gas_left: step.gas_left.0,
        gas_cost: step.gas_cost.as_u64(),
        opcode: match step.exec_state {
            circuit_input_builder::ExecState::Op(op) => Some(op),
            _ => None,
        },
        memory_size: step.memory_size as u64,
        reversible_write_counter: step.reversible_write_counter,
        reversible_write_counter_delta: step.reversible_write_counter_delta,
        log_id: step.log_id,
    }
}
