//! Doc this
use crate::eth_types::Word;
use crate::Error;
use std::collections::HashMap;

/// Represents a snapshot of the EVM stack state at a certain
/// execution step height.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Storage(pub(crate) HashMap<Word, Word>);

impl<T: Into<HashMap<Word, Word>>> From<T> for Storage {
    fn from(map: T) -> Self {
        Self(map.into())
    }
}

impl Default for Storage {
    fn default() -> Self {
        Self::empty()
    }
}

impl Storage {
    /// Generate an empty instance of EVM Storage.
    pub fn empty() -> Self {
        Storage(HashMap::new())
    }

    /// Generate an new instance of EVM storage given a `HashMap<Word, Word>`.
    pub fn new(map: HashMap<Word, Word>) -> Self {
        Self::from(map)
    }

    /// Get the word for a given key in the EVM storage
    pub fn get(&self, key: &Word) -> Option<&Word> {
        self.0.get(key)
    }

    /// Get the word for a given key in the EVM storage.  Returns error if key
    /// is not found.
    pub fn get_or_err(&self, key: &Word) -> Result<Word, Error> {
        self.get(key).cloned().ok_or(Error::InvalidStorageKey)
    }
}
