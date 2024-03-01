use super::{Call, ExecStep, FixedCParams};
use crate::operation::RWCounter;

#[derive(Debug, Default, Clone)]
pub struct Chunk {
    /// current context
    pub ctx: ChunkContext,
    /// fixed param for the chunk
    pub fixed_param: FixedCParams,
    /// Begin op of a chunk
    pub begin_chunk: Option<ExecStep>,
    /// End op of a chunk
    pub end_chunk: Option<ExecStep>,
    /// Padding step that is repeated after the last transaction and before
    /// reaching the last EVM row.
    pub padding: Option<ExecStep>,
    ///
    pub prev_last_call: Option<Call>,
}

/// Context of chunking, used to track the current chunk index and inner rw counter
/// also the global rw counter from start to end.
#[derive(Debug, Clone)]
pub struct ChunkContext {
    /// Index of current chunk, start from 0
    pub idx: usize,
    /// Used to track the inner chunk counter in every operation in the chunk.
    /// it will be reset for every new chunk.
    /// Contains the next available value.
    pub rwc: RWCounter,
    /// Number of chunks
    pub total_chunks: usize,
    /// Initial global rw counter
    pub initial_rwc: usize,
    /// End global rw counter
    pub end_rwc: usize,
    /// tx range in block: [initial_tx_index, end_tx_index)
    pub initial_tx_index: usize,
    ///
    pub end_tx_index: usize,
    ///  copy range in block: [initial_copy_index, end_copy_index)
    pub initial_copy_index: usize,
    ///
    pub end_copy_index: usize,
}

impl Default for ChunkContext {
    fn default() -> Self {
        Self::new(1)
    }
}

impl ChunkContext {
    /// Create a new Self
    pub fn new(total_chunks: usize) -> Self {
        Self {
            rwc: RWCounter::new(),
            idx: 0,
            total_chunks,
            initial_rwc: 1, // rw counter start from 1
            end_rwc: 0,     // end_rwc should be set in later phase
            initial_tx_index: 0,
            end_tx_index: 0,
            initial_copy_index: 0,
            end_copy_index: 0,
        }
    }

    /// New chunking context with one chunk
    pub fn new_one_chunk() -> Self {
        Self {
            rwc: RWCounter::new(),
            idx: 0,
            total_chunks: 1,
            initial_rwc: 1, // rw counter start from 1
            end_rwc: 0,     // end_rwc should be set in later phase
            initial_tx_index: 0,
            end_tx_index: 0,
            initial_copy_index: 0,
            end_copy_index: 0,
        }
    }

    /// Proceed the context to next chunk, record the initial rw counter
    /// update the chunk idx and reset the inner rw counter
    pub fn bump(&mut self, initial_rwc: usize, initial_tx: usize, initial_copy: usize) {
        assert!(self.idx + 1 < self.total_chunks, "Exceed total chunks");
        self.idx += 1;
        self.rwc = RWCounter::new();
        self.initial_rwc = initial_rwc;
        self.initial_tx_index = initial_tx;
        self.initial_copy_index = initial_copy;
        self.end_rwc = 0;
        self.end_tx_index = 0;
        self.end_copy_index = 0;
    }

    /// Is first chunk
    pub fn is_first_chunk(&self) -> bool {
        self.idx == 0
    }

    /// Is last chunk
    pub fn is_last_chunk(&self) -> bool {
        self.total_chunks - self.idx - 1 == 0
    }
}
