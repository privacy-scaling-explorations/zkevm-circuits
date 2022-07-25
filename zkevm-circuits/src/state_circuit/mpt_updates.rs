use crate::evm_circuit::{table::AccountFieldTag, util::RandomLinearCombination, witness::Rw};
use eth_types::{Address, Field, ToLittleEndian, ToScalar, Word};
use itertools::Itertools;
use std::collections::HashMap;

#[derive(Default)]
pub struct MptUpdates(HashMap<Key, MptUpdate>);

impl MptUpdates {
    pub fn get(&self, row: &Rw) -> Option<MptUpdate> {
        key(row).map(|key| *self.0.get(&key).expect("missing asdfas in mpt updates"))
    }

    pub fn mock_from(rows: &[Rw]) -> Self {
        let map: HashMap<_, _> = rows
            .iter()
            .group_by(|row| key(row))
            .into_iter()
            .filter_map(|(key, rows)| key.map(|key| (key, rows)))
            .enumerate()
            .map(|(i, (key, mut rows))| {
                let first = rows.next().unwrap();
                let last = rows.last().unwrap_or(first);
                (
                    key,
                    MptUpdate {
                        key,
                        old_root: Word::from(i as u64),
                        new_root: Word::from(i as u64 + 1),
                        old_value: value_prev(first),
                        new_value: value(last),
                    },
                )
            })
            .collect();
        MptUpdates(map)
    }

    pub fn iter(&self) -> impl Iterator<Item = &MptUpdate> {
        self.0.values()
    }
}

#[derive(Debug, Clone, Copy)]
pub struct MptUpdate {
    key: Key,
    old_value: Word,
    new_value: Word,
    old_root: Word,
    new_root: Word,
}

impl MptUpdate {
    pub fn lookup_assignment<F: Field>(&self, word_randomness: F, lookup_randomness: F) -> F {
        let (new_root_assignment, old_root_assignment) = self.root_assignments(word_randomness);
        let (new_value_assignment, old_value_assignment) = self.value_assignments(word_randomness);

        [
            self.key.address(),
            self.key.storage_key(word_randomness),
            self.key.field_tag(),
            new_root_assignment,
            old_root_assignment,
            new_value_assignment,
            old_value_assignment,
        ]
        .iter()
        .rev()
        .fold(F::zero(), |result, a| lookup_randomness * result + a)
    }

    pub fn value_assignments<F: Field>(&self, word_randomness: F) -> (F, F) {
        let assign = |x: Word| {
            let mut result =
                RandomLinearCombination::random_linear_combine(x.to_le_bytes(), word_randomness);
            if let Key::Account { field_tag, .. } = self.key {
                if matches!(field_tag, AccountFieldTag::Nonce) {
                    result = x.to_scalar().unwrap()
                }
            }
            result
        };

        (assign(self.new_value), assign(self.old_value))
    }

    pub fn root_assignments<F: Field>(&self, word_randomness: F) -> (F, F) {
        (
            RandomLinearCombination::random_linear_combine(
                self.new_root.to_le_bytes(),
                word_randomness,
            ),
            RandomLinearCombination::random_linear_combine(
                self.old_root.to_le_bytes(),
                word_randomness,
            ),
        )
    }
}

#[derive(Eq, PartialEq, Hash, Clone, Debug, Copy)]
enum Key {
    Account {
        address: Address,
        field_tag: AccountFieldTag,
    },
    AccountStorage {
        tx_id: usize,
        address: Address,
        storage_key: Word,
    },
}

impl Key {
    fn address<F: Field>(&self) -> F {
        match self {
            Self::Account { address, .. } | Self::AccountStorage { address, .. } => {
                address.to_scalar().unwrap()
            }
        }
    }
    fn field_tag<F: Field>(&self) -> F {
        match self {
            Self::Account { field_tag, .. } => F::from(*field_tag as u64),
            Self::AccountStorage { .. } => F::zero(),
        }
    }
    fn storage_key<F: Field>(&self, randomness: F) -> F {
        match self {
            Self::Account { .. } => F::zero(),
            Self::AccountStorage { storage_key, .. } => {
                RandomLinearCombination::random_linear_combine(
                    storage_key.to_le_bytes(),
                    randomness,
                )
            }
        }
    }
}

fn key(row: &Rw) -> Option<Key> {
    match row {
        Rw::Account {
            account_address,
            field_tag,
            ..
        } => Some(Key::Account {
            address: *account_address,
            field_tag: *field_tag,
        }),
        Rw::AccountStorage {
            tx_id,
            account_address,
            storage_key,
            ..
        } => Some(Key::AccountStorage {
            tx_id: *tx_id,
            address: *account_address,
            storage_key: *storage_key,
        }),
        _ => None,
    }
}

fn value(row: &Rw) -> Word {
    match row {
        Rw::Account { value, .. } => *value,
        Rw::AccountStorage { value, .. } => *value,
        _ => unreachable!(),
    }
}

fn value_prev(row: &Rw) -> Word {
    match row {
        Rw::Account { value_prev, .. } => *value_prev,
        Rw::AccountStorage { value_prev, .. } => *value_prev,
        _ => unreachable!(),
    }
}
