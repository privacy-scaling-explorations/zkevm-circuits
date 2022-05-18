use anyhow::Result;
use eth_types::{evm_types::OpcodeId, GethExecTrace, U256};
use prettytable::Table;
use zkevm_circuits::test_util::{get_fixed_table, BytecodeTestConfig, FixedTableConfig};

const OPCODES_NEED_FULL_FIXED_TABLE: [OpcodeId; 3] = [OpcodeId::AND, OpcodeId::OR, OpcodeId::XOR];

// see https://github.com/appliedzkp/zkevm-circuits/issues/477
pub const OPCODES_UNIMPLEMENTED: [OpcodeId; 31] = [
    OpcodeId::SDIV,
    OpcodeId::SMOD,
    OpcodeId::ADDMOD,
    OpcodeId::MULMOD,
    OpcodeId::EXP,
    OpcodeId::NOT,
    OpcodeId::CODESIZE,
    OpcodeId::SHL,
    OpcodeId::SHR,
    OpcodeId::SAR,
    OpcodeId::RETURN,
    OpcodeId::REVERT,
    OpcodeId::SHA3,
    OpcodeId::ADDRESS,
    OpcodeId::BALANCE,
    OpcodeId::EXTCODESIZE,
    OpcodeId::EXTCODECOPY,
    OpcodeId::RETURNDATASIZE,
    OpcodeId::RETURNDATACOPY,
    OpcodeId::BLOCKHASH,
    OpcodeId::LOG1,
    OpcodeId::LOG2,
    OpcodeId::LOG3,
    OpcodeId::LOG4,
    OpcodeId::LOG0,
    OpcodeId::CREATE,
    OpcodeId::CREATE2,
    OpcodeId::CALLCODE,
    OpcodeId::DELEGATECALL,
    OpcodeId::STATICCALL,
    OpcodeId::SELFDESTRUCT,
];

pub fn config_bytecode_test_config<OPS: Iterator<Item = OpcodeId>>(
    cfg: &mut BytecodeTestConfig,
    mut ops: OPS,
) {
    let needs_complete_fixed_table = ops
        .find(|op| OPCODES_NEED_FULL_FIXED_TABLE.contains(op))
        .is_some();

    if needs_complete_fixed_table {
        cfg.evm_circuit_lookup_tags = get_fixed_table(FixedTableConfig::Complete);
    }
}

pub fn print_trace(trace: GethExecTrace) -> Result<()> {
    fn kv(storage: std::collections::HashMap<U256, U256>) -> Vec<String> {
        let mut keys: Vec<_> = storage.keys().collect();
        keys.sort();
        keys.iter()
            .map(|k| format!("{:?}: {:?}", k, storage[k]))
            .collect()
    }
    fn split(strs: Vec<String>, len: usize) -> String {
        let mut out = String::new();
        let mut current_len = 0;
        let mut it = strs.iter();
        let mut current = it.next();

        while let Some(v) = current {
            let mut count = 1usize;
            current = it.next();
            while current == Some(v) {
                count += 1;
                current = it.next();
            }

            let item = if count == 1 {
                v.to_string()
            } else {
                format!("{}[{}]", v, count)
            };

            if current_len > len {
                current_len = 0;
                out.push('\n');
            } else if current_len > 0 {
                out.push_str(", ");
            }
            out.push_str(&item);
            current_len += item.len();
        }
        out
    }

    let mut table = Table::new();
    table.add_row(row![
        "PC", "OP", "GAS", "GAS_COST", "DEPTH", "ERR", "STACK", "MEMORY", "STORAGE"
    ]);
    for step in trace.struct_logs {
        table.add_row(row![
            format!("{}", step.pc.0),
            format!("{:?}", step.op),
            format!("{}", step.gas.0),
            format!("{}", step.gas_cost.0),
            format!("{}", step.depth),
            step.error.unwrap_or("".to_string()),
            split(step.stack.0.iter().map(ToString::to_string).collect(), 30),
            split(step.memory.0.iter().map(ToString::to_string).collect(), 30),
            split(kv(step.storage.0), 30)
        ]);
    }

    println!("FAILED: {:?}", trace.failed);
    println!("GAS: {:?}", trace.gas);
    table.printstd();

    Ok(())
}
