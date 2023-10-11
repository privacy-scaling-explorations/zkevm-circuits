pub use super::StateCircuit;

use crate::{
    state_circuit::{StateCircuitConfig, StateCircuitConfigArgs},
    table::{MptTable, RwTable, UXTable},
    util::{Challenges, SubCircuit, SubCircuitConfig},
};
use eth_types::Field;
use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner},
    plonk::{Circuit, ConstraintSystem, Error},
};

impl<F: Field> Circuit<F> for StateCircuit<F>
where
    F: Field,
{
    type Config = (StateCircuitConfig<F>, Challenges);
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let rw_table = RwTable::construct(meta);
        let mpt_table = MptTable::construct(meta);
        let challenges = Challenges::construct(meta);
        let u8_table = UXTable::construct(meta);
        let u10_table = UXTable::construct(meta);
        let u16_table = UXTable::construct(meta);

        let config = {
            let challenges = challenges.exprs(meta);
            StateCircuitConfig::new(
                meta,
                StateCircuitConfigArgs {
                    rw_table,
                    mpt_table,
                    u8_table,
                    u10_table,
                    u16_table,
                    challenges,
                },
            )
        };

        (config, challenges)
    }

    fn synthesize(
        &self,
        (config, challenges): Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let challenges = challenges.values(&mut layouter);
        config.mpt_table.load(&mut layouter, &self.updates)?;
        self.synthesize_sub(&config, &challenges, &mut layouter)
    }
}

#[cfg(test)]
use crate::util::word::Word;

#[cfg(test)]
use crate::state_circuit::HashMap;
#[cfg(test)]
use crate::witness::{rw::ToVec, Rw, RwMap, RwRow};
#[cfg(test)]
use gadgets::permutation::get_permutation_fingerprints;
#[cfg(test)]
use halo2_proofs::{
    circuit::Value,
    plonk::{Advice, Column},
};

#[cfg(test)]
#[derive(Hash, Eq, PartialEq, Clone, Debug)]
pub(crate) enum AdviceColumn {
    IsWrite,
    _Address,
    AddressLimb0,
    AddressLimb1,
    _StorageKeyLo,
    _StorageKeyHi,
    StorageKeyLimb0,
    _StorageKeyLimb1,
    ValueLo,
    ValueHi,
    ValuePrevLo,
    ValuePrevHi,
    RwCounter,
    RwCounterLimb0,
    _RwCounterLimb1,
    Tag,
    TagBit0,
    TagBit1,
    TagBit2,
    TagBit3,
    _LimbIndexBit0, // most significant bit
    LimbIndexBit1,
    LimbIndexBit2,
    _LimbIndexBit3,
    _LimbIndexBit4, // least significant bit
    InitialValueLo,
    InitialValueHi,
    IsZero, // committed_value and value are 0
    // NonEmptyWitness is the BatchedIsZero chip witness that contains the
    // inverse of the non-zero value if any in [committed_value, value]
    NonEmptyWitness,
}

#[cfg(test)]
impl AdviceColumn {
    pub(crate) fn value<F: Field>(&self, config: &StateCircuitConfig<F>) -> Column<Advice> {
        match self {
            Self::IsWrite => config.rw_table.is_write,
            Self::_Address => config.rw_table.address,
            Self::AddressLimb0 => config.sort_keys.address.limbs[0],
            Self::AddressLimb1 => config.sort_keys.address.limbs[1],
            Self::_StorageKeyLo => config.rw_table.storage_key.lo(),
            Self::_StorageKeyHi => config.rw_table.storage_key.hi(),
            Self::StorageKeyLimb0 => config.sort_keys.storage_key.limbs[0],
            Self::_StorageKeyLimb1 => config.sort_keys.storage_key.limbs[1],
            Self::ValueLo => config.rw_table.value.lo(),
            Self::ValueHi => config.rw_table.value.hi(),
            Self::ValuePrevLo => config.rw_table.value_prev.lo(),
            Self::ValuePrevHi => config.rw_table.value_prev.hi(),
            Self::RwCounter => config.rw_table.rw_counter,
            Self::RwCounterLimb0 => config.sort_keys.rw_counter.limbs[0],
            Self::_RwCounterLimb1 => config.sort_keys.rw_counter.limbs[1],
            Self::Tag => config.rw_table.tag,
            Self::TagBit0 => config.sort_keys.tag.bits[0],
            Self::TagBit1 => config.sort_keys.tag.bits[1],
            Self::TagBit2 => config.sort_keys.tag.bits[2],
            Self::TagBit3 => config.sort_keys.tag.bits[3],
            Self::_LimbIndexBit0 => config.lexicographic_ordering.first_different_limb.bits[0],
            Self::LimbIndexBit1 => config.lexicographic_ordering.first_different_limb.bits[1],
            Self::LimbIndexBit2 => config.lexicographic_ordering.first_different_limb.bits[2],
            Self::_LimbIndexBit3 => config.lexicographic_ordering.first_different_limb.bits[3],
            Self::_LimbIndexBit4 => config.lexicographic_ordering.first_different_limb.bits[4],
            Self::InitialValueLo => config.initial_value.lo(),
            Self::InitialValueHi => config.initial_value.hi(),
            Self::IsZero => config.is_non_exist.is_zero,
            Self::NonEmptyWitness => config.is_non_exist.nonempty_witness,
        }
    }

    pub(crate) fn rw_row_overrides<F: Field>(&self, row: &mut RwRow<Value<F>>, value: F) {
        match self {
            Self::IsWrite => row.is_write = Value::known(value),
            Self::_Address => row.address = Value::known(value),
            Self::_StorageKeyLo => {
                row.storage_key = Word::new([Value::known(value), row.storage_key.hi()])
            }
            Self::_StorageKeyHi => {
                row.storage_key = Word::new([row.storage_key.lo(), Value::known(value)])
            }
            Self::ValueLo => row.value = Word::new([Value::known(value), row.value.hi()]),
            Self::ValueHi => row.value = Word::new([row.value.lo(), Value::known(value)]),
            Self::ValuePrevLo => {
                row.value_prev = Word::new([Value::known(value), row.value_prev.hi()])
            }
            Self::ValuePrevHi => {
                row.value_prev = Word::new([row.value_prev.lo(), Value::known(value)])
            }
            Self::RwCounter => row.rw_counter = Value::known(value),
            Self::Tag => row.tag = Value::known(value),
            Self::InitialValueLo => {
                row.init_val = Word::new([Value::known(value), row.init_val.hi()])
            }
            Self::InitialValueHi => {
                row.init_val = Word::new([row.init_val.lo(), Value::known(value)])
            }
            _ => (),
        };
    }
}

#[cfg(test)]
pub(crate) fn rw_overrides_skip_first_padding<F: Field>(
    rws: &[Rw],
    overrides: &HashMap<(AdviceColumn, isize), F>,
) -> Vec<RwRow<Value<F>>> {
    let first_non_padding_index = 1;
    let mut rws: Vec<RwRow<Value<F>>> = rws.iter().map(|row| row.table_assignment()).collect();

    for ((column, row_offset), &f) in overrides {
        let offset =
            usize::try_from(isize::try_from(first_non_padding_index).unwrap() + *row_offset)
                .unwrap();
        column.rw_row_overrides(&mut rws[offset], f);
    }
    rws
}

#[cfg(test)]
pub(crate) fn get_permutation_fingerprint_of_rwmap<F: Field>(
    rwmap: &RwMap,
    max_row: usize,
    alpha: F,
    gamma: F,
    prev_continuous_fingerprint: F,
) -> F {
    get_permutation_fingerprint_of_rwvec(
        &rwmap.table_assignments(false),
        max_row,
        alpha,
        gamma,
        prev_continuous_fingerprint,
    )
}

#[cfg(test)]
pub(crate) fn get_permutation_fingerprint_of_rwvec<F: Field>(
    rwvec: &[Rw],
    max_row: usize,
    alpha: F,
    gamma: F,
    prev_continuous_fingerprint: F,
) -> F {
    get_permutation_fingerprint_of_rwrowvec(
        &rwvec
            .iter()
            .map(|row| row.table_assignment())
            .collect::<Vec<RwRow<Value<F>>>>(),
        max_row,
        alpha,
        gamma,
        prev_continuous_fingerprint,
    )
}

#[cfg(test)]
pub(crate) fn get_permutation_fingerprint_of_rwrowvec<F: Field>(
    rwrowvec: &[RwRow<Value<F>>],
    max_row: usize,
    alpha: F,
    gamma: F,
    prev_continuous_fingerprint: F,
) -> F {
    use crate::util::unwrap_value;

    let (rows, _) = RwRow::padding(rwrowvec, max_row, true);
    let x = rows.to2dvec();
    unwrap_value(
        get_permutation_fingerprints(
            &x,
            Value::known(alpha),
            Value::known(gamma),
            Value::known(prev_continuous_fingerprint),
            1,
        )
        .last()
        .cloned()
        .unwrap(),
    )
}
