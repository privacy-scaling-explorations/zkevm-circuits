use eth_types::evm_types::OpcodeId;
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
