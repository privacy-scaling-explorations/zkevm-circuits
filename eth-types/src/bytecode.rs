//! EVM byte code generator

use crate::{evm_types::OpcodeId, Bytes, Word};
use std::collections::HashMap;

/// Helper struct that represents a single element in a bytecode.
#[derive(Copy, Clone, Debug, Default, PartialEq)]
pub struct BytecodeElement {
    /// The byte value of the element.
    pub value: u8,
    /// Whether the element is an opcode or push data byte.
    pub is_code: bool,
}

/// EVM Bytecode
#[derive(Debug, Default, Clone, PartialEq)]
pub struct Bytecode {
    code: Vec<BytecodeElement>,
    num_opcodes: usize,
    markers: HashMap<String, usize>,
}

impl From<Bytecode> for Bytes {
    fn from(code: Bytecode) -> Self {
        code.code
            .iter()
            .map(|e| e.value)
            .collect::<Vec<u8>>()
            .into()
    }
}

impl Bytecode {
    /// Get the bytecode element at an index.
    pub fn get(&self, index: usize) -> Option<BytecodeElement> {
        self.code.get(index).cloned()
    }

    /// Get the generated code
    pub fn to_vec(&self) -> Vec<u8> {
        self.code.iter().map(|e| e.value).collect()
    }

    /// Append
    pub fn append(&mut self, other: &Bytecode) {
        self.code.extend_from_slice(&other.code);
        for (key, val) in other.markers.iter() {
            self.insert_marker(key, self.num_opcodes + val);
        }
        self.num_opcodes += other.num_opcodes;
    }

    /// Write op
    pub fn write_op(&mut self, op: OpcodeId) -> &mut Self {
        self.write_op_internal(op.as_u8())
    }

    fn write_op_internal(&mut self, op: u8) -> &mut Self {
        self.num_opcodes += 1;
        self.write(op, true)
    }

    /// Write byte
    pub fn write(&mut self, value: u8, is_code: bool) -> &mut Self {
        self.code.push(BytecodeElement { value, is_code });
        self
    }

    /// Push
    pub fn push(&mut self, n: usize, value: Word) -> &mut Self {
        debug_assert!((1..=32).contains(&n), "invalid push");

        // Write the op code
        self.write_op_internal(OpcodeId::PUSH1.as_u8() + ((n - 1) as u8));

        let mut bytes = [0u8; 32];
        value.to_little_endian(&mut bytes);
        // Write the bytes MSB to LSB
        for i in 0..n {
            self.write(bytes[n - 1 - i], false);
        }
        // Check if the full value could be pushed
        for byte in bytes.iter().skip(n) {
            debug_assert!(*byte == 0u8, "value too big for PUSH{}: {}", n, value);
        }
        self
    }

    /// Add marker
    pub fn add_marker(&mut self, marker: String) -> &mut Self {
        self.insert_marker(&marker, self.num_opcodes);
        self
    }

    /// Insert marker
    pub fn insert_marker(&mut self, marker: &str, pos: usize) {
        debug_assert!(
            !self.markers.contains_key(marker),
            "marker already used: {}",
            marker
        );
        self.markers.insert(marker.to_string(), pos);
    }

    /// Get the position of a marker
    pub fn get_pos(&self, marker: &str) -> usize {
        *self
            .markers
            .get(&marker.to_string())
            .unwrap_or_else(|| panic!("marker '{}' not found", marker))
    }

    /// Setup state
    pub fn setup_state(&mut self) -> &mut Self {
        self.append(&crate::bytecode! {
            PUSH1(0x80u64)
            PUSH1(0x40u64)
            MSTORE
        });
        self
    }

    /// Call a contract
    #[allow(clippy::too_many_arguments)]
    pub fn call(
        &mut self,
        gas: Word,
        address: Word,
        value: Word,
        mem_in: Word,
        mem_in_size: Word,
        mem_out: Word,
        mem_out_size: Word,
    ) -> &mut Self {
        self.append(&crate::bytecode! {
            PUSH32(mem_out_size)
            PUSH32(mem_out)
            PUSH32(mem_in_size)
            PUSH32(mem_in)
            PUSH32(value)
            PUSH32(address)
            PUSH32(gas)
            CALL
        });
        self
    }
}

impl From<Vec<u8>> for Bytecode {
    fn from(input: Vec<u8>) -> Self {
        let mut code = Bytecode::default();

        let mut input_iter = input.iter();
        while let Some(byte) = input_iter.next() {
            if let Ok(op) = OpcodeId::try_from(*byte) {
                code.write_op(op);
                if op.is_push() {
                    let n = (op.as_u8() - OpcodeId::PUSH1.as_u8() + 1) as usize;
                    for _ in 0..n {
                        match input_iter.next() {
                            Some(v) => {
                                code.write(*v, false);
                            }
                            None => {
                                // out of boundary is allowed
                                // see also: https://github.com/ethereum/go-ethereum/blob/997f1c4f0abcd78f645e6e7ced6db4b42ad59c9d/core/vm/analysis.go#L65
                                break;
                            }
                        }
                    }
                }
            } else {
                code.write_op(OpcodeId::INVALID(*byte));
            }
        }

        code
    }
}

/// EVM code macro
#[macro_export]
macro_rules! bytecode {
    ($($args:tt)*) => {{
        let mut code = $crate::bytecode::Bytecode::default();
        $crate::bytecode_internal!(code, $($args)*);
        code
    }};
}

#[macro_export]
#[doc(hidden)]
macro_rules! bytecode_internal {
    // Nothing left to do
    ($code:ident, ) => {};
    // PUSHX op codes
    ($code:ident, $x:ident ($v:expr) $($rest:tt)*) => {{
        debug_assert!($crate::evm_types::OpcodeId::$x.is_push(), "invalid push");
        let n = $crate::evm_types::OpcodeId::$x.as_u8()
            - $crate::evm_types::OpcodeId::PUSH1.as_u8()
            + 1;
        $code.push(n as usize, $v.into());
        $crate::bytecode_internal!($code, $($rest)*);
    }};
    // Default opcode without any inputs
    ($code:ident, $x:ident $($rest:tt)*) => {{
        debug_assert!(!$crate::evm_types::OpcodeId::$x.is_push(), "invalid push");
        $code.write_op($crate::evm_types::OpcodeId::$x);
        $crate::bytecode_internal!($code, $($rest)*);
    }};
    // Marker
    ($code:ident, #[$marker:tt] $($rest:tt)*) => {{
        $code.add_marker(stringify!($marker).to_string());
        $crate::bytecode_internal!($code, $($rest)*);
    }};
    // Function calls
    ($code:ident, .$function:ident ($($args:expr),*) $($rest:tt)*) => {{
        $code.$function($($args.into(),)*);
        $crate::bytecode_internal!($code, $($rest)*);
    }};
}

#[cfg(test)]
mod tests {
    use crate::Bytecode;

    #[test]
    fn test_bytecode_roundtrip() {
        let code = bytecode! {
            PUSH8(0x123)
            POP
            PUSH24(0x321)
            PUSH32(0x432)
            MUL
            CALLVALUE
            CALLER
            POP
            POP
            POP
            STOP
        };
        assert_eq!(Bytecode::try_from(code.to_vec()).unwrap(), code);
    }
}
