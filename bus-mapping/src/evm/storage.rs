//! Doc this
use crate::evm::EvmWord;
use crate::Error;
use std::collections::HashMap;

/// Represents a snapshot of the EVM stack state at a certain
/// execution step height.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Storage(pub(crate) HashMap<EvmWord, EvmWord>);

impl<T: Into<HashMap<EvmWord, EvmWord>>> From<T> for Storage {
    fn from(map: T) -> Self {
        Self(map.into())
    }
}

impl Storage {
    /// Generate an empty instance of EVM Storage.
    pub fn empty() -> Self {
        Storage(HashMap::new())
    }

    /// Generate an new instance of EVM storage given a `HashMap<EvmWord, EvmWord>`.
    pub fn new(map: HashMap<EvmWord, EvmWord>) -> Self {
        Self::from(map)
    }

    /// Get the word for a given key in the EVM storage
    pub fn get(&self, key: &EvmWord) -> Option<&EvmWord> {
        self.0.get(key)
    }

    /// Get the word for a given key in the EVM storage.  Returns error if key is not found.
    pub fn get_or_err(&self, key: &EvmWord) -> Result<&EvmWord, Error> {
        self.get(key).ok_or(Error::InvalidStorageKey)
    }
}
