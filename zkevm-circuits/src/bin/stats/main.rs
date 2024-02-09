//! Build with `--features="stats"`

mod halo2_stats;
mod helpers;

use bus_mapping::circuit_input_builder::FeatureConfig;
use cli_table::{print_stdout, Cell, Style, Table};
use eth_types::{bytecode, evm_types::OpcodeId, ToWord};
use halo2_proofs::{
    halo2curves::bn256::Fr,
    plonk::{Circuit, ConstraintSystem, Expression},
};
use halo2_stats::StatsCollection;
use helpers::{bytecode_prefix_op_big_rws, print_circuit_stats_by_states};
use itertools::Itertools;
use mock::MOCK_ACCOUNTS;
use std::{array, env, iter};
use zkevm_circuits::{
    bytecode_circuit::{BytecodeCircuitConfig, BytecodeCircuitConfigArgs},
    copy_circuit::{CopyCircuitConfig, CopyCircuitConfigArgs},
    evm_circuit::{
        param::{
            LOOKUP_CONFIG, N_COPY_COLUMNS, N_PHASE1_COLUMNS, N_PHASE2_COLUMNS, N_U16_LOOKUPS,
            N_U8_LOOKUPS,
        },
        step::ExecutionState,
        EvmCircuit, EvmCircuitConfig, EvmCircuitConfigArgs,
    },
    exp_circuit::ExpCircuitConfig,
    keccak_circuit::{KeccakCircuitConfig, KeccakCircuitConfigArgs},
    pi_circuit::{PiCircuitConfig, PiCircuitConfigArgs},
    state_circuit::{StateCircuitConfig, StateCircuitConfigArgs},
    table::{
        BlockTable, BytecodeTable, CopyTable, ExpTable, KeccakTable, MptTable, RwTable, TxTable,
        UXTable, WdTable,
    },
    tx_circuit::{TxCircuitConfig, TxCircuitConfigArgs},
    util::{Challenges, SubCircuitConfig},
};

fn main() {
    let args: Vec<String> = env::args().collect();

    match &args[1][..] {
        "evm" => evm_states_stats(),
        "state" => state_states_stats(),
        "copy" => copy_states_stats(),
        "exec" => get_exec_steps_occupancy(),
        "general" => general_subcircuit_stats(),
        &_ => unreachable!("Unsupported arg"),
    }
}

/// Prints the stats of EVM circuit per execution state.
fn evm_states_stats() {
    print_circuit_stats_by_states(
        |state| {
            !matches!(
                state,
                ExecutionState::ErrorInvalidOpcode | ExecutionState::SELFDESTRUCT
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
            !matches!(
                state,
                ExecutionState::ErrorInvalidOpcode | ExecutionState::SELFDESTRUCT
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
            matches!(
                state,
                ExecutionState::RETURNDATACOPY
                    | ExecutionState::CODECOPY
                    | ExecutionState::LOG
                    | ExecutionState::CALLDATACOPY
                    | ExecutionState::EXTCODECOPY
                    | ExecutionState::RETURN_REVERT
                    | ExecutionState::CREATE
                    | ExecutionState::CREATE2
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
    let circuit = EvmCircuit::configure_with_params(&mut meta, FeatureConfig::default());

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
                format!("Utilization (%)").cell().bold(true),
            ]);
            print_stdout(table).unwrap();

            // consider use stats package, e.g. https://github.com/statrs-dev/statrs to output more insightful result
            let raw_statistics_data = report
                .iter()
                .fold(vec![0; 2], |mut accu, exec| {
                    accu[0] += exec.$id.available_cells;
                    accu[1] += exec.$id.used_cells;
                    accu
                });

            let table = vec![vec![
                format!("{:?}", raw_statistics_data[0]),
                format!("{:?}", raw_statistics_data[1]),
                format!("{:.1}", (raw_statistics_data[1] as f64/raw_statistics_data[0] as f64) * 100.0),
            ]].table().title(vec![
                format!("{:?} total_available_cells", stringify!($id)).cell().bold(true),
                format!("{:?} total_used_cells", stringify!($id)).cell().bold(true),
                format!("{:?} Utilization (%)", stringify!($id)).cell().bold(true),
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
        u8_lookup,
        N_U8_LOOKUPS,
        u16_lookup,
        N_U16_LOOKUPS,
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

#[allow(unused_variables)]
fn record_stats<F: eth_types::Field>(
    stats: &mut StatsCollection<F>,
    meta: &mut ConstraintSystem<F>,
) {
    let max_txs = 1;
    let max_withdrawals = 5;
    let max_calldata = 32;
    let mock_randomness = F::from(0x100);
    let feature_config = FeatureConfig::default();

    // Shared Tables
    let tx_table = TxTable::construct(meta);
    stats.record_shared("tx_table", meta);
    let wd_table = WdTable::construct(meta);
    stats.record_shared("wd_table", meta);
    let rw_table = RwTable::construct(meta);
    stats.record_shared("rw_table", meta);
    let mpt_table = MptTable::construct(meta);
    stats.record_shared("mpt_table", meta);
    let bytecode_table = BytecodeTable::construct(meta);
    stats.record_shared("bytecode_table", meta);
    let block_table = BlockTable::construct(meta);
    stats.record_shared("block_table", meta);
    let q_copy_table = meta.fixed_column();
    let copy_table = CopyTable::construct(meta, q_copy_table);
    stats.record_shared("copy_table", meta);
    let exp_table = ExpTable::construct(meta);
    stats.record_shared("exp_table", meta);
    let keccak_table = KeccakTable::construct(meta);
    stats.record_shared("keccak_table", meta);
    let u8_table = UXTable::construct(meta);
    stats.record_shared("u8_table", meta);
    let u10_table = UXTable::construct(meta);
    stats.record_shared("u10_table", meta);
    let u16_table = UXTable::construct(meta);
    stats.record_shared("u16_table", meta);

    // Use a mock randomness instead of the randomness derived from the challenge
    // (either from mock or real prover) to help debugging assignments.
    let power_of_randomness: [Expression<F>; 31] =
        array::from_fn(|i| Expression::Constant(mock_randomness.pow([1 + i as u64, 0, 0, 0])));

    let challenges = Challenges::mock(
        power_of_randomness[0].clone(),
        power_of_randomness[0].clone(),
    );

    let keccak_circuit = KeccakCircuitConfig::new(
        meta,
        KeccakCircuitConfigArgs {
            keccak_table: keccak_table.clone(),
            challenges: challenges.clone(),
        },
    );
    stats.record("keccak", meta);

    let pi_circuit = PiCircuitConfig::new(
        meta,
        PiCircuitConfigArgs {
            max_txs,
            max_withdrawals,
            max_calldata,
            block_table: block_table.clone(),
            tx_table: tx_table.clone(),
            wd_table,
            keccak_table: keccak_table.clone(),
            challenges: challenges.clone(),
        },
    );
    stats.record("pi", meta);
    let tx_circuit = TxCircuitConfig::new(
        meta,
        TxCircuitConfigArgs {
            tx_table: tx_table.clone(),
            keccak_table: keccak_table.clone(),
            challenges: challenges.clone(),
        },
    );
    stats.record("tx", meta);
    let bytecode_circuit = BytecodeCircuitConfig::new(
        meta,
        BytecodeCircuitConfigArgs {
            bytecode_table: bytecode_table.clone(),
            keccak_table: keccak_table.clone(),
            challenges: challenges.clone(),
        },
    );
    stats.record("bytecode", meta);
    let copy_circuit = CopyCircuitConfig::new(
        meta,
        CopyCircuitConfigArgs {
            tx_table: tx_table.clone(),
            rw_table,
            bytecode_table: bytecode_table.clone(),
            copy_table,
            q_enable: q_copy_table,
            challenges: challenges.clone(),
        },
    );
    stats.record("copy", meta);
    let state_circuit = StateCircuitConfig::new(
        meta,
        StateCircuitConfigArgs {
            rw_table,
            mpt_table,
            u8_table,
            u10_table,
            u16_table,
            challenges: challenges.clone(),
        },
    );
    stats.record("state", meta);
    let exp_circuit = ExpCircuitConfig::new(meta, exp_table);
    stats.record("exp", meta);
    let evm_circuit = EvmCircuitConfig::new(
        meta,
        EvmCircuitConfigArgs {
            challenges,
            tx_table,
            rw_table,
            bytecode_table,
            block_table,
            copy_table,
            keccak_table,
            exp_table,
            u8_table,
            u16_table,
            feature_config,
        },
    );
    stats.record("evm", meta);
}

fn general_subcircuit_stats() {
    let mut stats_list = StatsCollection::<Fr>::new(false);
    let mut meta = ConstraintSystem::<Fr>::default();
    record_stats(&mut stats_list, &mut meta);
    let mut stats_agg = StatsCollection::<Fr>::new(true);
    let mut meta = ConstraintSystem::<Fr>::default();
    record_stats(&mut stats_agg, &mut meta);

    let mut table = Vec::new();
    for (name, stats) in stats_list
        .list
        .iter()
        .chain(iter::once(&("super".to_string(), stats_agg.agg)))
    {
        // At 0.0139 gas/row this gives us 2^26 * 0.0139 = ~900k gas.  For 30M gas we would need 33
        // chunks.
        let k = 26;
        let peak_mem_gb = stats.estimate_peak_mem(k) / 1024 / 1024 / 1024;
        table.push(vec![
            name.cell(),
            stats.num_constraints.cell(),
            stats.num_rotation.cell(),
            format!("{}/{}", stats.min_rotation, stats.max_rotation).cell(),
            stats.num_fixed_columns.cell(),
            stats.num_selectors.cell(),
            stats.num_advice_columns.cell(),
            stats.num_permutation_columns.cell(),
            stats.num_lookups.cell(),
            stats.degree.cell(),
            peak_mem_gb.cell(),
        ]);
    }
    let table = table
        .table()
        .title(
            [
                "circuit",
                "constraints",
                "rots",
                "min/max(rots)",
                "fix_cols",
                "selectors",
                "adv_cols",
                "perm_cols",
                "lookups",
                "degree",
                "mem_gb",
            ]
            .iter()
            .map(|s| s.cell().bold(true)),
        )
        .bold(true);

    assert!(print_stdout(table).is_ok());
}
