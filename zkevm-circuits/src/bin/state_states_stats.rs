use zkevm_circuits::{
    evm_circuit::step::ExecutionState,
    stats::{bytecode_prefix_op_big_rws, print_circuit_stats_by_states},
};

/// Prints the stats of State circuit per execution state.  See
/// `print_circuit_stats_by_states` for more details.

pub fn main() {
    print_circuit_stats_by_states(
        |state| {
            // TODO: Enable CREATE/CREATE2 once they are supported
            !matches!(
                state,
                ExecutionState::ErrorInvalidOpcode
                    | ExecutionState::CREATE
                    | ExecutionState::CREATE2
                    | ExecutionState::SELFDESTRUCT
            )
        },
        bytecode_prefix_op_big_rws,
        |block, _, step_index| {
            let step = &block.txs[0].steps()[step_index];
            let step_next = &block.txs[0].steps()[step_index + 1];
            step_next.rwc.0 - step.rwc.0
        },
    );
}
