//! precompile helpers

use eth_types::{
    evm_types::{GasCost, OpcodeId},
    Address, Bytecode, Word,
};
#[cfg(not(target_arch = "wasm32"))]
use revm_precompile::{Precompile, PrecompileError, Precompiles};

#[allow(unused_variables)]
/// Check if address is a precompiled or not.
pub fn is_precompiled(address: &Address) -> bool {
    #[cfg(target_arch = "wasm32")]
    if address.0[0..19] == [0u8; 19] && (1..=9).contains(&address.0[19]) {
        // TODO add support for precompiles in WASM
        panic!("Precompile {address} is currently not supported in WASM");
    } else {
        return false;
    }

    #[cfg(not(target_arch = "wasm32"))]
    Precompiles::berlin()
        .get(address.as_fixed_bytes())
        .is_some()
}

#[allow(unused_variables)]
pub(crate) fn execute_precompiled(
    address: &Address,
    input: &[u8],
    gas: u64,
) -> (Vec<u8>, u64, bool) {
    #[cfg(target_arch = "wasm32")]
    // TODO add support for precompiles in WASM
    panic!("Running precompile {address} is currently not supported in WASM");

    #[cfg(not(target_arch = "wasm32"))]
    {
        let Some(Precompile::Standard(precompile_fn)) = Precompiles::berlin()
        .get(address.as_fixed_bytes())  else {
            panic!("calling non-exist precompiled contract address")
        };
        let (return_data, gas_cost, is_oog, is_ok) = match precompile_fn(input, gas) {
            Ok((gas_cost, return_value)) => {
                // Some Revm behavior for invalid inputs might be overridden.
                (return_value, gas_cost, false, true)
            }
            Err(err) => match err {
                PrecompileError::OutOfGas => (vec![], gas, true, false),
                _ => {
                    log::warn!("unknown precompile err {err:?}");
                    (vec![], gas, false, false)
                }
            },
        };
        log::trace!("called precompile with is_ok {is_ok} is_oog {is_oog}, gas_cost {gas_cost}, return_data len {}", return_data.len());
        (return_data, gas_cost, is_oog)
    }
}

/// Addresses of the precompiled contracts.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum PrecompileCalls {
    /// Elliptic Curve Recovery
    Ecrecover = 0x01,
    /// SHA2-256 hash function
    Sha256 = 0x02,
    /// Ripemd-160 hash function
    Ripemd160 = 0x03,
    /// Identity function
    Identity = 0x04,
    /// Modular exponentiation
    Modexp = 0x05,
    /// Point addition
    Bn128Add = 0x06,
    /// Scalar multiplication
    Bn128Mul = 0x07,
    /// Bilinear function
    Bn128Pairing = 0x08,
    /// Compression function
    Blake2F = 0x09,
}

impl Default for PrecompileCalls {
    fn default() -> Self {
        Self::Ecrecover
    }
}

impl From<PrecompileCalls> for Address {
    fn from(value: PrecompileCalls) -> Self {
        let mut addr = [0u8; 20];
        addr[19] = value as u8;
        Self(addr)
    }
}

impl From<PrecompileCalls> for u64 {
    fn from(value: PrecompileCalls) -> Self {
        value as u64
    }
}

impl From<PrecompileCalls> for usize {
    fn from(value: PrecompileCalls) -> Self {
        value as usize
    }
}

impl From<u8> for PrecompileCalls {
    fn from(value: u8) -> Self {
        match value {
            0x01 => Self::Ecrecover,
            0x02 => Self::Sha256,
            0x03 => Self::Ripemd160,
            0x04 => Self::Identity,
            0x05 => Self::Modexp,
            0x06 => Self::Bn128Add,
            0x07 => Self::Bn128Mul,
            0x08 => Self::Bn128Pairing,
            0x09 => Self::Blake2F,
            _ => unreachable!("precompile contracts only from 0x01 to 0x09"),
        }
    }
}

impl PrecompileCalls {
    /// Get the base gas cost for the precompile call.
    pub fn base_gas_cost(&self) -> u64 {
        match self {
            Self::Ecrecover => GasCost::PRECOMPILE_ECRECOVER_BASE,
            Self::Sha256 => GasCost::PRECOMPILE_SHA256_BASE,
            Self::Ripemd160 => GasCost::PRECOMPILE_RIPEMD160_BASE,
            Self::Identity => GasCost::PRECOMPILE_IDENTITY_BASE,
            Self::Modexp => GasCost::PRECOMPILE_MODEXP,
            Self::Bn128Add => GasCost::PRECOMPILE_BN256ADD,
            Self::Bn128Mul => GasCost::PRECOMPILE_BN256MUL,
            Self::Bn128Pairing => GasCost::PRECOMPILE_BN256PAIRING,
            Self::Blake2F => GasCost::PRECOMPILE_BLAKE2F,
        }
    }

    /// Get the EVM address for this precompile call.
    pub fn address(&self) -> u64 {
        (*self).into()
    }

    /// Maximum length of input bytes considered for the precompile call.
    pub fn input_len(&self) -> Option<usize> {
        match self {
            Self::Ecrecover | Self::Bn128Add => Some(128),
            Self::Bn128Mul => Some(96),
            _ => None,
        }
    }
}

/// Precompile call args
pub struct PrecompileCallArgs {
    /// description for the instance of a precompile call.
    pub name: &'static str,
    /// the bytecode that when call can produce the desired precompile call.
    pub setup_code: Bytecode,
    /// the call's return data size.
    pub ret_size: Word,
    /// the call's return data offset.
    pub ret_offset: Word,
    /// the call's calldata offset.
    pub call_data_offset: Word,
    /// the call's calldata length.
    pub call_data_length: Word,
    /// the address to which the call is made, i.e. callee address.
    pub address: Word,
    /// the optional value sent along with the call.
    pub value: Word,
    /// the gas limit for the call.
    pub gas: Word,
    /// stack values during the call.
    pub stack_value: Vec<(Word, Word)>,
    /// maximum number of RW entries for the call.
    pub max_rws: usize,
}

impl Default for PrecompileCallArgs {
    fn default() -> Self {
        PrecompileCallArgs {
            name: "precompiled call",
            setup_code: Bytecode::default(),
            ret_size: Word::zero(),
            ret_offset: Word::zero(),
            call_data_offset: Word::zero(),
            call_data_length: Word::zero(),
            address: Word::zero(),
            value: Word::zero(),
            gas: Word::from(0xFFFFFFF),
            stack_value: vec![],
            max_rws: 1000,
        }
    }
}

impl PrecompileCallArgs {
    /// Get the setup bytecode for call to a precompiled contract.
    pub fn with_call_op(&self, call_op: OpcodeId) -> Bytecode {
        assert!(
            call_op.is_call(),
            "invalid setup, {:?} is not a call op",
            call_op
        );
        let mut code = self.setup_code.clone();
        code.push(32, self.ret_size)
            .push(32, self.ret_offset)
            .push(32, self.call_data_length)
            .push(32, self.call_data_offset);
        if call_op == OpcodeId::CALL || call_op == OpcodeId::CALLCODE {
            code.push(32, self.value);
        }
        code.push(32, self.address)
            .push(32, self.gas)
            .write_op(call_op)
            .write_op(OpcodeId::POP);
        for (offset, _) in self.stack_value.iter().rev() {
            code.push(32, *offset).write_op(OpcodeId::MLOAD);
        }

        code
    }
}

/// Auxiliary data for Ecrecover
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct EcrecoverAuxData {
    /// Keccak hash of the message being signed.
    pub msg_hash: Word,
    /// v-component of signature.
    pub sig_v: Word,
    /// r-component of signature.
    pub sig_r: Word,
    /// s-component of signature.
    pub sig_s: Word,
    /// Address that was recovered.
    pub recovered_addr: Address,
    /// Input bytes to the ecrecover call.
    pub input_bytes: Vec<u8>,
    /// Output bytes from the ecrecover call.
    pub output_bytes: Vec<u8>,
    /// Bytes returned to the caller from the ecrecover call.
    pub return_bytes: Vec<u8>,
}

impl EcrecoverAuxData {
    /// Create a new instance of ecrecover auxiliary data.
    pub fn new(input: &[u8], output: &[u8], return_bytes: &[u8]) -> Self {
        let mut resized_input = input.to_vec();
        resized_input.resize(128, 0u8);
        let mut resized_output = output.to_vec();
        resized_output.resize(32, 0u8);

        // assert that recovered address is 20 bytes.
        assert!(resized_output[0x00..0x0c].iter().all(|&b| b == 0));
        let recovered_addr = Address::from_slice(&resized_output[0x0c..0x20]);

        Self {
            msg_hash: Word::from_big_endian(&resized_input[0x00..0x20]),
            sig_v: Word::from_big_endian(&resized_input[0x20..0x40]),
            sig_r: Word::from_big_endian(&resized_input[0x40..0x60]),
            sig_s: Word::from_big_endian(&resized_input[0x60..0x80]),
            recovered_addr,
            input_bytes: input.to_vec(),
            output_bytes: output.to_vec(),
            return_bytes: return_bytes.to_vec(),
        }
    }

    /// Sanity check and returns recovery ID.
    pub fn recovery_id(&self) -> Option<u8> {
        let sig_v_bytes = self.sig_v.to_be_bytes();
        let sig_v = sig_v_bytes[31];
        if sig_v_bytes.iter().take(31).all(|&b| b == 0) && (sig_v == 27 || sig_v == 28) {
            Some(sig_v - 27)
        } else {
            None
        }
    }
}

/// Auxiliary data attached to an internal state for precompile verification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PrecompileAuxData {
    /// Base precompile (used for Identity, SHA256, RIPEMD-160 and BLAKE2F).
    Base {
        /// input bytes to the identity call.
        input_bytes: Vec<u8>,
        /// output bytes from the identity call.
        output_bytes: Vec<u8>,
        /// bytes returned back to the caller from the identity call.
        return_bytes: Vec<u8>,
    },
    /// Ecrecover.
    Ecrecover(EcrecoverAuxData),
}

impl Default for PrecompileAuxData {
    fn default() -> Self {
        Self::Ecrecover(EcrecoverAuxData::default())
    }
}
