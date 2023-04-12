use bus_mapping::{
    circuit_input_builder,
    error::{ExecError, OogError},
    evm::OpcodeId,
    geth_types::ZkEvmExecStep,
};
use eth_types::evm_unimplemented;

use crate::evm_circuit::{param::N_BYTES_WORD, step::ExecutionState};

/// Step executed in a transaction
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ExecStep {
    /// execution step
    pub step: ZkEvmExecStep,
    /// The execution state for the step
    pub execution_state: ExecutionState,
    // /// The indices in the RW trace incurred in this step
    // pub rw_indices: Vec<(RwTableTag, usize)>,
    // /// The opcode corresponds to the step
    // pub opcode: Option<OpcodeId>,
}

impl ExecStep {
    /// The memory size in word **before** this step
    pub fn memory_word_size(&self) -> u64 {
        // EVM always pads the memory size to word size
        // https://github.com/ethereum/go-ethereum/blob/master/core/vm/interpreter.go#L212-L216
        // Thus, the memory size must be a multiple of 32 bytes.
        assert_eq!(self.step.memory_size % N_BYTES_WORD as u64, 0);
        self.step.memory_size / N_BYTES_WORD as u64
    }
}

impl From<&ExecError> for ExecutionState {
    fn from(error: &ExecError) -> Self {
        match error {
            ExecError::InvalidOpcode => ExecutionState::ErrorInvalidOpcode,
            ExecError::StackOverflow | ExecError::StackUnderflow => ExecutionState::ErrorStack,
            ExecError::WriteProtection => ExecutionState::ErrorWriteProtection,
            ExecError::Depth => ExecutionState::ErrorDepth,
            ExecError::InsufficientBalance => ExecutionState::ErrorInsufficientBalance,
            ExecError::ContractAddressCollision => ExecutionState::ErrorContractAddressCollision,
            ExecError::InvalidCreationCode => ExecutionState::ErrorInvalidCreationCode,
            ExecError::InvalidJump => ExecutionState::ErrorInvalidJump,
            ExecError::ReturnDataOutOfBounds => ExecutionState::ErrorReturnDataOutOfBound,
            ExecError::CodeStoreOutOfGas => ExecutionState::ErrorOutOfGasCodeStore,
            ExecError::MaxCodeSizeExceeded => ExecutionState::ErrorMaxCodeSizeExceeded,
            ExecError::OutOfGas(oog_error) => match oog_error {
                OogError::Constant => ExecutionState::ErrorOutOfGasConstant,
                OogError::StaticMemoryExpansion => {
                    ExecutionState::ErrorOutOfGasStaticMemoryExpansion
                }
                OogError::DynamicMemoryExpansion => {
                    ExecutionState::ErrorOutOfGasDynamicMemoryExpansion
                }
                OogError::MemoryCopy => ExecutionState::ErrorOutOfGasMemoryCopy,
                OogError::AccountAccess => ExecutionState::ErrorOutOfGasAccountAccess,
                OogError::CodeStore => ExecutionState::ErrorOutOfGasCodeStore,
                OogError::Log => ExecutionState::ErrorOutOfGasLOG,
                OogError::Exp => ExecutionState::ErrorOutOfGasEXP,
                OogError::Sha3 => ExecutionState::ErrorOutOfGasSHA3,
                OogError::ExtCodeCopy => ExecutionState::ErrorOutOfGasEXTCODECOPY,
                OogError::Call => ExecutionState::ErrorOutOfGasCall,
                OogError::SloadSstore => ExecutionState::ErrorOutOfGasSloadSstore,
                OogError::Create2 => ExecutionState::ErrorOutOfGasCREATE2,
                OogError::SelfDestruct => ExecutionState::ErrorOutOfGasSELFDESTRUCT,
            },
        }
    }
}

impl From<&circuit_input_builder::ExecStep> for ExecutionState {
    fn from(step: &circuit_input_builder::ExecStep) -> Self {
        if let Some(error) = step.error.as_ref() {
            return error.into();
        }
        match step.exec_state {
            circuit_input_builder::ExecState::Op(op) => {
                if op.is_dup() {
                    return ExecutionState::DUP;
                }
                if op.is_push() {
                    return ExecutionState::PUSH;
                }
                if op.is_swap() {
                    return ExecutionState::SWAP;
                }
                if op.is_log() {
                    return ExecutionState::LOG;
                }

                macro_rules! dummy {
                    ($name:expr) => {{
                        evm_unimplemented!("{:?} is implemented with DummyGadget", $name);
                        $name
                    }};
                }

                match op {
                    OpcodeId::ADD | OpcodeId::SUB => ExecutionState::ADD_SUB,
                    OpcodeId::ADDMOD => ExecutionState::ADDMOD,
                    OpcodeId::ADDRESS => ExecutionState::ADDRESS,
                    OpcodeId::BALANCE => ExecutionState::BALANCE,
                    OpcodeId::MUL | OpcodeId::DIV | OpcodeId::MOD => ExecutionState::MUL_DIV_MOD,
                    OpcodeId::MULMOD => ExecutionState::MULMOD,
                    OpcodeId::SDIV | OpcodeId::SMOD => ExecutionState::SDIV_SMOD,
                    OpcodeId::EQ | OpcodeId::LT | OpcodeId::GT => ExecutionState::CMP,
                    OpcodeId::SLT | OpcodeId::SGT => ExecutionState::SCMP,
                    OpcodeId::SIGNEXTEND => ExecutionState::SIGNEXTEND,
                    OpcodeId::STOP => ExecutionState::STOP,
                    OpcodeId::AND => ExecutionState::BITWISE,
                    OpcodeId::XOR => ExecutionState::BITWISE,
                    OpcodeId::OR => ExecutionState::BITWISE,
                    OpcodeId::NOT => ExecutionState::NOT,
                    OpcodeId::EXP => ExecutionState::EXP,
                    OpcodeId::POP => ExecutionState::POP,
                    OpcodeId::PUSH32 => ExecutionState::PUSH,
                    OpcodeId::BYTE => ExecutionState::BYTE,
                    OpcodeId::MLOAD => ExecutionState::MEMORY,
                    OpcodeId::MSTORE => ExecutionState::MEMORY,
                    OpcodeId::MSTORE8 => ExecutionState::MEMORY,
                    OpcodeId::JUMPDEST => ExecutionState::JUMPDEST,
                    OpcodeId::JUMP => ExecutionState::JUMP,
                    OpcodeId::JUMPI => ExecutionState::JUMPI,
                    OpcodeId::GASPRICE => ExecutionState::GASPRICE,
                    OpcodeId::PC => ExecutionState::PC,
                    OpcodeId::MSIZE => ExecutionState::MSIZE,
                    OpcodeId::CALLER => ExecutionState::CALLER,
                    OpcodeId::CALLVALUE => ExecutionState::CALLVALUE,
                    OpcodeId::EXTCODEHASH => ExecutionState::EXTCODEHASH,
                    OpcodeId::EXTCODESIZE => ExecutionState::EXTCODESIZE,
                    OpcodeId::BLOCKHASH => ExecutionState::BLOCKHASH,
                    OpcodeId::TIMESTAMP | OpcodeId::NUMBER | OpcodeId::GASLIMIT => {
                        ExecutionState::BLOCKCTXU64
                    }
                    OpcodeId::COINBASE => ExecutionState::BLOCKCTXU160,
                    OpcodeId::DIFFICULTY | OpcodeId::BASEFEE => ExecutionState::BLOCKCTXU256,
                    OpcodeId::GAS => ExecutionState::GAS,
                    OpcodeId::SAR => ExecutionState::SAR,
                    OpcodeId::SELFBALANCE => ExecutionState::SELFBALANCE,
                    OpcodeId::SHA3 => ExecutionState::SHA3,
                    OpcodeId::SHL | OpcodeId::SHR => ExecutionState::SHL_SHR,
                    OpcodeId::SLOAD => ExecutionState::SLOAD,
                    OpcodeId::SSTORE => ExecutionState::SSTORE,
                    OpcodeId::CALLDATASIZE => ExecutionState::CALLDATASIZE,
                    OpcodeId::CALLDATACOPY => ExecutionState::CALLDATACOPY,
                    OpcodeId::CHAINID => ExecutionState::CHAINID,
                    OpcodeId::ISZERO => ExecutionState::ISZERO,
                    OpcodeId::CALL
                    | OpcodeId::CALLCODE
                    | OpcodeId::DELEGATECALL
                    | OpcodeId::STATICCALL => ExecutionState::CALL_OP,
                    OpcodeId::ORIGIN => ExecutionState::ORIGIN,
                    OpcodeId::CODECOPY => ExecutionState::CODECOPY,
                    OpcodeId::CALLDATALOAD => ExecutionState::CALLDATALOAD,
                    OpcodeId::CODESIZE => ExecutionState::CODESIZE,
                    OpcodeId::RETURN | OpcodeId::REVERT => ExecutionState::RETURN_REVERT,
                    OpcodeId::RETURNDATASIZE => ExecutionState::RETURNDATASIZE,
                    OpcodeId::RETURNDATACOPY => ExecutionState::RETURNDATACOPY,
                    // dummy ops
                    OpcodeId::EXTCODECOPY => dummy!(ExecutionState::EXTCODECOPY),
                    OpcodeId::CREATE => dummy!(ExecutionState::CREATE),
                    OpcodeId::CREATE2 => dummy!(ExecutionState::CREATE2),
                    OpcodeId::SELFDESTRUCT => dummy!(ExecutionState::SELFDESTRUCT),
                    _ => unimplemented!("unimplemented opcode {:?}", op),
                }
            }
            circuit_input_builder::ExecState::BeginTx => ExecutionState::BeginTx,
            circuit_input_builder::ExecState::EndTx => ExecutionState::EndTx,
            circuit_input_builder::ExecState::EndBlock => ExecutionState::EndBlock,
        }
    }
}

pub(super) fn step_convert(step: &circuit_input_builder::ExecStep) -> ExecStep {
    ExecStep {
        step: step.step.clone(),
        execution_state: ExecutionState::from(step),
    }
}
