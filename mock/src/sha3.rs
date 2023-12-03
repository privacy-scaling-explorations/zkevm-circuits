use eth_types::{bytecode, Bytecode, U256};
use rand::{rngs::ThreadRng, Rng};

/// Generate Sha3 opcode
pub struct Sha3CodeGen {
    /// The offset
    pub offset: usize,
    /// The size
    pub size: usize,
    data_len: usize,
    rng: ThreadRng,
}
impl Sha3CodeGen {
    /// Construct with memory less than size
    pub fn mem_lt_size(offset: usize, size: usize) -> Self {
        let mut rng = rand::thread_rng();
        let data_len = offset
            + if size.gt(&0) {
                rng.gen_range(0..size)
            } else {
                0
            };
        Self {
            offset,
            size,
            data_len,
            rng,
        }
    }
    /// Construct with memory equal to size
    pub fn mem_eq_size(offset: usize, size: usize) -> Self {
        let data_len = offset + size;
        Self {
            offset,
            size,
            data_len,
            rng: rand::thread_rng(),
        }
    }
    /// Construct with memory greater than size
    pub fn mem_gt_size(offset: usize, size: usize) -> Self {
        let mut rng = rand::thread_rng();
        let data_len = offset
            + size
            + if size.gt(&0) {
                rng.gen_range(0..size)
            } else {
                0
            };
        Self {
            offset,
            size,
            data_len,
            rng,
        }
    }
    /// Construct with empty memory
    pub fn mem_empty(offset: usize, size: usize) -> Self {
        Self {
            offset,
            size,
            data_len: 0,
            rng: rand::thread_rng(),
        }
    }
    fn rand_bytes(&mut self) -> Vec<u8> {
        (0..self.data_len)
            .map(|_| self.rng.gen())
            .collect::<Vec<u8>>()
    }
    /// Generate bytecode for SHA3 opcode after having populated sufficient
    /// memory given the offset and size arguments for SHA3.
    pub fn gen_sha3_code(&mut self) -> (Bytecode, Vec<u8>) {
        let data = self.rand_bytes();
        let mut memory = Vec::with_capacity(self.data_len);

        // add opcodes to populate memory in the current context.
        let mut code = Bytecode::default();
        for (i, memchunk) in data.chunks(32).enumerate() {
            let mem_value = if memchunk.len() < 32 {
                std::iter::repeat(0u8)
                    .take(32 - memchunk.len())
                    .chain(memchunk.to_vec())
                    .collect::<Vec<u8>>()
            } else {
                memchunk.to_vec()
            };
            memory.extend_from_slice(&mem_value);
            code.op_mstore(32 * i, U256::from_big_endian(&mem_value));
        }
        // append SHA3 related opcodes at the tail end.
        let code_tail = bytecode! {
            PUSH32(self.size)
            PUSH32(self.offset)
            SHA3
            STOP
        };
        code.append(&code_tail);
        (code, memory)
    }
}
