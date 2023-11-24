use crate::operation::RWCounter;
use super::{Block, ExecStep};

#[derive(Debug, Default)]
pub struct Chunk {
    /// index of current chunk, start from 0
    pub chunk_index: usize,
    /// number of chunks
    pub total_chunks: usize,
    /// initial rw counter
    pub initial_rwc: usize,
    /// end rw counter
    pub end_rwc: usize,
    /// ExecSteps in a chunk
    pub chunk_steps: ChunkSteps,
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
    /// Used to track the inner chunk counter in every operation in the chunk.
    /// Contains the next available value.
    pub rwc: RWCounter,
    /// index of current chunk, start from 0
    pub cur: usize,
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
            cur: cur_idx,
            total_chunks,
            initial_rwc: 1, // rw counter start from 1
            end_rwc: 0,     // end_rwc should be set in later phase
        }
    }

    /// new Self with one chunk
    pub fn new_one_chunk() -> Self {
        Self {
            rwc: RWCounter::new(),
            cur: 0,
            total_chunks: 1,
            initial_rwc: 1, // rw counter start from 1
            end_rwc: 0,     // end_rwc should be set in later phase
        }
    }

    /// is first chunk
    pub fn is_first_chunk(&self) -> bool {
        self.cur == 0
    }

    /// is last chunk
    pub fn is_last_chunk(&self) -> bool {
        self.total_chunks - self.cur - 1 == 0
    }
}
