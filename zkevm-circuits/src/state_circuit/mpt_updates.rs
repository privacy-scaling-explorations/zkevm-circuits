use crate::evm_circuit::{table::AccountFieldTag, util::RandomLinearCombination, witness::Rw};
use eth_types::{Address, Field, ToLittleEndian, ToScalar, Word};
use itertools::Itertools;
use std::collections::HashMap;

#[derive(Default)]
pub struct MptUpdates<F>(pub HashMap<MptKey, MptValue<F>>);

impl<F: Field> MptUpdates<F> {
    pub fn get(&self, row: &Rw) -> Option<MptValue<F>> {
        mpt_key(row).map(|key| *self.0.get(&key).expect("missing asdfas in mpt updates"))
    }
}

#[derive(Eq, PartialEq, Hash, Clone, Debug)]
pub enum MptKey {
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

// TODO make these all Words instead.... you need to switch to Key -> MptUpdate
// anyways
#[derive(Debug, Clone, Default, Copy)]
pub struct MptValue<F> {
    pub old_root: F,
    pub new_root: F,
    pub old_value: F,
    pub new_value: F,
}

impl<F: Field> MptValue<F> {
    fn new(row: &Rw, old_root: F, new_root: F, randomness: F) -> Self {
        Self {
            old_root,
            new_root,
            old_value: row.value_prev_assignment(randomness).unwrap(),
            new_value: row.value_assignment(randomness),
        }
    }
}

impl MptKey {
    pub fn address<F: Field>(&self) -> F {
        match self {
            Self::Account { address, .. } | Self::AccountStorage { address, .. } => {
                address.to_scalar().unwrap()
            }
        }
    }
    pub fn field_tag<F: Field>(&self) -> F {
        match self {
            Self::Account { field_tag, .. } => F::from(*field_tag as u64),
            Self::AccountStorage { .. } => F::zero(),
        }
    }
    pub fn storage_key<F: Field>(&self, randomness: F) -> F {
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

pub fn mpt_key(row: &Rw) -> Option<MptKey> {
    match row {
        Rw::Account {
            account_address,
            field_tag,
            ..
        } => Some(MptKey::Account {
            address: *account_address,
            field_tag: *field_tag,
        }),
        Rw::AccountStorage {
            tx_id,
            account_address,
            storage_key,
            ..
        } => Some(MptKey::AccountStorage {
            tx_id: *tx_id,
            address: *account_address,
            storage_key: *storage_key,
        }),
        _ => None,
    }
}

pub fn fake_mpt_updates<F: Field>(rows: &[Rw], randomness: F) -> MptUpdates<F> {
    let map: HashMap<_, _> = rows
        .iter()
        .group_by(|row| mpt_key(row))
        .into_iter()
        .filter_map(|(key, rows)| key.map(|key| (key, rows)))
        .enumerate()
        .map(|(i, (key, mut rows))| {
            let first = rows.next().unwrap();
            let mut value = MptValue::new(
                first,
                F::from(i as u64),
                F::from((i + 1) as u64),
                randomness,
            );
            value.new_value = rows.last().unwrap_or(first).value_assignment(randomness);
            (key, value)
        })
        .collect();
    MptUpdates(map)
}
