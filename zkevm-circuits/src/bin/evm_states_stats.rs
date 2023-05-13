use eth_types::{bytecode, evm_types::OpcodeId, ToWord};
use mock::MOCK_ACCOUNTS;
use zkevm_circuits::{evm_circuit::step::ExecutionState, stats::print_circuit_stats_by_states};

/// Prints the stats of EVM circuit per execution state.  See
/// `print_circuit_stats_by_states` for more details.
fn main() {
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
