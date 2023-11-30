use eth_types::{Word, U256};

use super::ExecStep;
use crate::operation::RWCounter;

#[derive(Debug, Default, Clone)]
pub struct Chunk {
    /// current context 
    pub ctx: ChunkContext,
    /// Begin op of a chunk
    pub begin_chunk: ExecStep,
    /// End op of a chunk
    pub end_chunk: Option<ExecStep>,
    /// 
    pub steps: Vec<ExecStep>,
    // Set in chunk_convert, used when converting the next chunk
    /// rw_table permutation fingerprint for this chunk
    pub rw_fingerprint: Word,
    /// rw_table permutation fingerprint for this chunk
    pub chrono_rw_fingerprint: Word,
}

/// Block-wise execution steps that don't belong to any Transaction.
#[derive(Debug, Default)]
pub struct ChunkSteps {
    /// Begin op of a chunk
    pub begin_chunk: ExecStep,
    /// End op of a chunk
    pub end_chunk: Option<ExecStep>,
}

/// Context of a [`ChunkContext`].
#[derive(Debug, Clone)]
pub struct ChunkContext {
    /// index of current chunk, start from 0
    pub idx: usize,
    /// Used to track the inner chunk counter in every operation in the chunk.
    /// Contains the next available value.
    pub rwc: RWCounter,
    /// number of chunks
    pub total_chunks: usize,
    /// initial rw counter
    pub initial_rwc: usize,
    /// end rw counter
    pub end_rwc: usize,
}

impl Default for ChunkContext {
    fn default() -> Self {
        Self::new(0, 1)
    }
}

impl ChunkContext {
    /// Create a new Self
    pub fn new(cur_idx: usize, total_chunks: usize) -> Self {
        Self {
            rwc: RWCounter::new(),
            idx: cur_idx,
            total_chunks,
            initial_rwc: 1, // rw counter start from 1
            end_rwc: 0,     // end_rwc should be set in later phase
        }
    }

    /// new Self with one chunk
    pub fn new_one_chunk() -> Self {
        Self {
            rwc: RWCounter::new(),
            idx: 0,
            total_chunks: 1,
            initial_rwc: 1, // rw counter start from 1
            end_rwc: 0,     // end_rwc should be set in later phase
        }
    }

    /// is first chunk
    pub fn is_first_chunk(&self) -> bool {
        self.idx == 0
    }

    /// is last chunk
    pub fn is_last_chunk(&self) -> bool {
        self.total_chunks - self.idx - 1 == 0
    }

    ///
    pub fn end_cur_chunk(&mut self) -> Self {
        self.end_rwc = self.rwc.0;
        let cur_ctx = self.clone();

        self.idx += 1;
        self.initial_rwc = self.rwc.0 + 1;
        self.rwc = RWCounter::new();

        cur_ctx
    }
}
