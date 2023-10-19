use crate::operation::RWCounter;

/// Context of a [`ChunkContext`].
#[derive(Debug, Clone)]
pub struct ChunkContext {
    /// Used to track the inner chunk counter in every operation in the chunk.
    /// Contains the next available value.
    pub rwc: RWCounter,
    /// index of current chunk, start from 0
    pub chunk_index: usize,
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
    pub fn new(chunk_index: usize, total_chunks: usize) -> Self {
        Self {
            rwc: RWCounter::new(),
            chunk_index,
            total_chunks,
            initial_rwc: 1, // rw counter start from 1
            end_rwc: 0,     // end_rwc should be set in later phase
        }
    }

    /// new Self with one chunk
    pub fn new_one_chunk() -> Self {
        Self {
            rwc: RWCounter::new(),
            chunk_index: 0,
            total_chunks: 1,
            initial_rwc: 1, // rw counter start from 1
            end_rwc: 0,     // end_rwc should be set in later phase
        }
    }
}
