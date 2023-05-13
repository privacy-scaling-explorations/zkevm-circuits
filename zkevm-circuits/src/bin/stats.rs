use cli_table::{print_stdout, Cell, Style, Table};
use eth_types::{bytecode, evm_types::OpcodeId, ToWord};
use halo2_proofs::{
    halo2curves::bn256::Fr,
    plonk::{Circuit, ConstraintSystem},
};
use itertools::Itertools;
use mock::MOCK_ACCOUNTS;
use std::env;
use zkevm_circuits::{
    evm_circuit::{
        param::{
            LOOKUP_CONFIG, N_BYTE_LOOKUPS, N_COPY_COLUMNS, N_PHASE1_COLUMNS, N_PHASE2_COLUMNS,
        },
        step::ExecutionState,
        EvmCircuit,
    },
    stats::{bytecode_prefix_op_big_rws, print_circuit_stats_by_states},
};

fn main() {
    let args: Vec<String> = env::args().collect();

    match &args[1][..] {
        "evm" => evm_states_stats(),
        "state" => state_states_stats(),
        "copy" => copy_states_stats(),
        "exec" => get_exec_steps_occupancy(),
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

/// Prints the stats of Copy circuit per execution state.
fn copy_states_stats() {
    print_circuit_stats_by_states(
        |state| {
            // TODO: Enable CREATE/CREATE2 once they are supported
            matches!(
                state,
                ExecutionState::RETURNDATACOPY
                    | ExecutionState::CODECOPY
                    | ExecutionState::LOG
                    | ExecutionState::CALLDATACOPY
                    | ExecutionState::EXTCODECOPY
                    | ExecutionState::RETURN_REVERT
            )
        },
        bytecode_prefix_op_big_rws,
        |block, _, _| {
            assert!(block.copy_events.len() <= 1);
            block
                .copy_events
                .iter()
                .map(|c| c.bytes.len() * 2)
                .sum::<usize>()
        },
    );
}

/// This function prints to stdout a table with the top X ExecutionState
/// cell consumers of each EVM Cell type.
fn get_exec_steps_occupancy() {
    let mut meta = ConstraintSystem::<Fr>::default();
    let circuit = EvmCircuit::configure(&mut meta);

    let report = circuit.0.execution.instrument().clone().analyze();
    macro_rules! gen_report {
        ($report:expr, $($id:ident, $cols:expr), +) => {
            $(
            let row_report = report
                .iter()
                .sorted_by(|a, b| a.$id.utilization.partial_cmp(&b.$id.utilization).unwrap())
                .rev()
                .take(10)
                .map(|exec| {
                    vec![
                        format!("{:?}", exec.state),
                        format!("{:?}", exec.$id.available_cells),
                        format!("{:?}", exec.$id.unused_cells),
                        format!("{:?}", exec.$id.used_cells),
                        format!("{:?}", exec.$id.top_height),
                        format!("{:?}", exec.$id.used_columns),
                        format!("{:?}", exec.$id.utilization),
                    ]
                })
                .collect::<Vec<Vec<String>>>();

            let table = row_report.table().title(vec![
                format!("{:?}", stringify!($id)).cell().bold(true),
                format!("total_available_cells").cell().bold(true),
                format!("unused_cells").cell().bold(true),
                format!("cells").cell().bold(true),
                format!("top_height").cell().bold(true),
                format!("used columns (Max: {:?})", $cols).cell().bold(true),
                format!("Utilization").cell().bold(true),
            ]);
            print_stdout(table).unwrap();
            )*
        };
    }

    gen_report!(
        report,
        storage_1,
        N_PHASE1_COLUMNS,
        storage_2,
        N_PHASE2_COLUMNS,
        storage_perm,
        N_COPY_COLUMNS,
        byte_lookup,
        N_BYTE_LOOKUPS,
        fixed_table,
        LOOKUP_CONFIG[0].1,
        tx_table,
        LOOKUP_CONFIG[1].1,
        rw_table,
        LOOKUP_CONFIG[2].1,
        bytecode_table,
        LOOKUP_CONFIG[3].1,
        block_table,
        LOOKUP_CONFIG[4].1,
        copy_table,
        LOOKUP_CONFIG[5].1,
        keccak_table,
        LOOKUP_CONFIG[6].1,
        exp_table,
        LOOKUP_CONFIG[7].1
    );
}
