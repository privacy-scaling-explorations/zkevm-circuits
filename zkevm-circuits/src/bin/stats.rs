use eth_types::{bytecode, evm_types::OpcodeId, ToWord};
use mock::MOCK_ACCOUNTS;
use std::env;
use zkevm_circuits::{
    evm_circuit::step::ExecutionState,
    stats::{bytecode_prefix_op_big_rws, print_circuit_stats_by_states},
};
fn main() {
    let args: Vec<String> = env::args().collect();

    match &args[1][..] {
        "evm" => evm_states_stats(),
        "state" => state_states_stats(),
        &_ => unreachable!("Unsupported arg"),
    }
}

/// Prints the stats of EVM circuit per execution state.
fn evm_states_stats() {
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
        |opcode| match opcode {
            OpcodeId::RETURNDATACOPY => {
                bytecode! {
                PUSH1(0x00) // retLength
                PUSH1(0x00) // retOffset
                PUSH1(0x00) // argsLength
                PUSH1(0x00) // argsOffset
                PUSH1(0x00) // value
                PUSH32(MOCK_ACCOUNTS[3].to_word())
                PUSH32(0x1_0000) // gas
                CALL
                PUSH2(0x01) // size
                PUSH2(0x00) // offset
                PUSH2(0x00) // destOffset
                }
            }
            _ => bytecode! {
                PUSH2(0x40)
                PUSH2(0x50)
            },
        },
        |_, state, _| state.get_step_height_option().unwrap(),
    );
}

/// Prints the stats of State circuit per execution state.
fn state_states_stats() {
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
