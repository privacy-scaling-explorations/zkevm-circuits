//! The state circuit implementation.
mod constraint_builder;
mod lexicographic_ordering;
mod lookups;
mod multiple_precision_integer;
mod random_linear_combination;
#[cfg(test)]
mod test;

use crate::evm_circuit::{
    param::N_BYTES_WORD,
    table::{AccountFieldTag, RwTableTag},
    util::RandomLinearCombination,
    witness::{Rw, RwMap},
};
use constraint_builder::{ConstraintBuilder, Queries};
use eth_types::{Address, Field, ToLittleEndian, ToScalar, Word};
use gadgets::{
    binary_number::{BinaryNumberChip, BinaryNumberConfig},
    util::Expr,
};
use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner},
    plonk::{
        Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, Instance, VirtualCells,
    },
    poly::Rotation,
};
use itertools::Itertools;
use lexicographic_ordering::Config as LexicographicOrderingConfig;
use lookups::{Chip as LookupsChip, Config as LookupsConfig, Queries as LookupsQueries};
use multiple_precision_integer::{Chip as MpiChip, Config as MpiConfig, Queries as MpiQueries};
use random_linear_combination::{Chip as RlcChip, Config as RlcConfig, Queries as RlcQueries};
use std::collections::HashMap;
use std::iter::once;

const N_LIMBS_RW_COUNTER: usize = 2;
const N_LIMBS_ACCOUNT_ADDRESS: usize = 10;
const N_LIMBS_ID: usize = 2;

/// Config for StateCircuit
#[derive(Clone, Copy)]
pub struct StateConfig {
    selector: Column<Fixed>, // Figure out why you get errors when this is Selector.
    // https://github.com/privacy-scaling-explorations/zkevm-circuits/issues/407
    sort_keys: SortKeysConfig,
    is_write: Column<Advice>,
    value: Column<Advice>,
    initial_value: Column<Advice>, /* Assigned value at the start of the block. For Rw::Account
                                    * and Rw::AccountStorage rows this is the committed value in
                                    * the MPT, for others, it is 0. */
    state_root: Column<Advice>,
    lexicographic_ordering: LexicographicOrderingConfig,
    lookups: LookupsConfig,
    power_of_randomness: [Column<Instance>; N_BYTES_WORD - 1],
}

/// Keys for sorting the rows of the state circuit
#[derive(Clone, Copy)]
pub struct SortKeysConfig {
    tag: BinaryNumberConfig<RwTableTag, 4>,
    id: MpiConfig<u32, N_LIMBS_ID>,
    address: MpiConfig<Address, N_LIMBS_ACCOUNT_ADDRESS>,
    field_tag: Column<Advice>,
    storage_key: RlcConfig<N_BYTES_WORD>,
    rw_counter: MpiConfig<u32, N_LIMBS_RW_COUNTER>,
}

type Lookup<F> = (&'static str, Expression<F>, Expression<F>);

/// State Circuit for proving RwTable is valid
#[derive(Default)]
pub struct StateCircuit<F: Field, const N_ROWS: usize> {
    pub(crate) randomness: F,
    pub(crate) rows: Vec<Rw>,
    updates: HashMap<MptKey, MptValue<F>>,
    #[cfg(test)]
    overrides: HashMap<(test::AdviceColumn, isize), F>,
}

#[derive(Eq, PartialEq, Hash, Clone, Debug)]
enum MptKey {
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

impl MptKey {
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

#[derive(Debug, Clone)]
struct MptValue<F> {
    old_root: F,
    new_root: F,
    old_value: F,
    new_value: F,
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

impl<F: Field, const N_ROWS: usize> StateCircuit<F, N_ROWS> {
    /// make a new state circuit from an RwMap
    pub fn new(randomness: F, rw_map: RwMap) -> Self {
        let mut rows: Vec<_> = rw_map.0.into_values().flatten().collect();
        rows.sort_by_key(|row| {
            (
                row.tag() as u64,
                row.id().unwrap_or_default(),
                row.address().unwrap_or_default(),
                row.field_tag().unwrap_or_default(),
                row.storage_key().unwrap_or_default(),
                row.rw_counter(),
            )
        });
        // TODO: take real mpt updates in constructor.
        let updates = fake_mpt_updates(&rows, randomness);
        // dbg!(updates.clone());
        Self {
            randomness,
            rows,
            updates,
            #[cfg(test)]
            overrides: HashMap::new(),
        }
    }

    /// powers of randomness for instance columns
    pub fn instance(&self) -> Vec<Vec<F>> {
        (1..32)
            .map(|exp| vec![self.randomness.pow(&[exp, 0, 0, 0]); N_ROWS])
            .collect()
    }
}

impl<F: Field, const N_ROWS: usize> Circuit<F> for StateCircuit<F, N_ROWS> {
    type Config = StateConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let selector = meta.fixed_column();
        let lookups = LookupsChip::configure(meta);
        let power_of_randomness = [0; N_BYTES_WORD - 1].map(|_| meta.instance_column());

        let [is_write, field_tag, value, initial_value, state_root] =
            [0; 5].map(|_| meta.advice_column());

        let tag = BinaryNumberChip::configure(meta, selector);

        let id = MpiChip::configure(meta, selector, lookups.u16);
        let address = MpiChip::configure(meta, selector, lookups.u16);
        let storage_key = RlcChip::configure(meta, selector, lookups.u8, power_of_randomness);
        let rw_counter = MpiChip::configure(meta, selector, lookups.u16);

        let sort_keys = SortKeysConfig {
            tag,
            id,
            field_tag,
            address,
            storage_key,
            rw_counter,
        };

        let lexicographic_ordering = LexicographicOrderingConfig::configure(
            meta,
            sort_keys,
            lookups.u16,
            power_of_randomness,
        );

        let config = Self::Config {
            selector,
            sort_keys,
            is_write,
            value,
            initial_value,
            state_root,
            lexicographic_ordering,
            lookups,
            power_of_randomness,
        };

        let mut constraint_builder = ConstraintBuilder::new();
        meta.create_gate("state circuit constraints", |meta| {
            let queries = queries(meta, &config);
            constraint_builder.build(&queries);
            constraint_builder.gate(queries.selector)
        });
        for (name, expressions) in constraint_builder.lookups() {
            meta.lookup_any(name, |_| vec![expressions]);
        }

        config
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        LookupsChip::construct(config.lookups).load(
            &mut layouter,
            &self.updates,
            self.randomness,
        )?;

        let tag_chip = BinaryNumberChip::construct(config.sort_keys.tag);

        layouter.assign_region(
            || "rw table",
            |mut region| {
                let padding_length = N_ROWS - self.rows.len();
                let padding = (1..=padding_length).map(|rw_counter| Rw::Start { rw_counter });

                let rows = padding.chain(self.rows.iter().cloned());
                let prev_rows = once(None).chain(rows.clone().map(Some));

                let mut initial_value = F::zero();
                let mut state_root = F::zero();

                for (offset, (row, prev_row)) in rows.zip(prev_rows).enumerate() {
                    region.assign_fixed(|| "selector", config.selector, offset, || Ok(F::one()))?;
                    config.sort_keys.rw_counter.assign(
                        &mut region,
                        offset,
                        row.rw_counter() as u32,
                    )?;
                    region.assign_advice(
                        || "is_write",
                        config.is_write,
                        offset,
                        || Ok(if row.is_write() { F::one() } else { F::zero() }),
                    )?;
                    tag_chip.assign(&mut region, offset, &row.tag())?;
                    if let Some(id) = row.id() {
                        config.sort_keys.id.assign(&mut region, offset, id as u32)?;
                    }
                    if let Some(address) = row.address() {
                        config
                            .sort_keys
                            .address
                            .assign(&mut region, offset, address)?;
                    }
                    if let Some(field_tag) = row.field_tag() {
                        region.assign_advice(
                            || "field_tag",
                            config.sort_keys.field_tag,
                            offset,
                            || Ok(F::from(field_tag as u64)),
                        )?;
                    }
                    if let Some(storage_key) = row.storage_key() {
                        config.sort_keys.storage_key.assign(
                            &mut region,
                            offset,
                            self.randomness,
                            storage_key,
                        )?;
                    }
                    region.assign_advice(
                        || "value",
                        config.value,
                        offset,
                        || Ok(row.value_assignment(self.randomness)),
                    )?;

                    // TODO: Remove special case for initial values for Rw::CallContext and
                    // Rw::TxReceipt, which can only be determined by the value for the first
                    // access row.
                    if !matches!(row.tag(), RwTableTag::CallContext | RwTableTag::TxReceipt) {
                        initial_value = mpt_key(&row)
                            .map(|key| self.updates.get(&key).unwrap().old_value)
                            .unwrap_or_default();
                    }

                    if let Some(prev_row) = prev_row {
                        let is_first_access = config.lexicographic_ordering.assign(
                            &mut region,
                            offset,
                            &row,
                            &prev_row,
                        )?;

                        // For first access to a group, we possibly need to update the initial value
                        // for RwTableTag::CallContext and RwTableTag::TxReceipt rows and update the
                        // state root.
                        if is_first_access {
                            if matches!(row.tag(), RwTableTag::CallContext | RwTableTag::TxReceipt)
                            {
                                initial_value = row.value_assignment(self.randomness);
                            }

                            if let Some(update) =
                                mpt_key(&prev_row).map(|key| self.updates.get(&key).unwrap())
                            {
                                assert_eq!(state_root, update.old_root);
                                state_root = update.new_root;
                            }
                        }
                    }

                    region.assign_advice(
                        || "initial_value",
                        config.initial_value,
                        offset,
                        || Ok(initial_value),
                    )?;

                    // TODO: Switch from Rw::Start -> Rw::Padding to simplify this logic.
                    // State root assignment is at offset-1 because the state root changes on the
                    // last access row.
                    if offset != 0 {
                        region.assign_advice(
                            || "state_root",
                            config.state_root,
                            offset - 1,
                            || Ok(state_root),
                        )?;
                    }

                    if offset == N_ROWS - 1 {
                        // last row is always a last access, so we need to handle the case where the
                        // state root changes because of an mpt lookup on the last row.
                        if let Some(update) =
                            mpt_key(&row).map(|key| self.updates.get(&key).unwrap())
                        {
                            state_root = update.new_root;
                        }
                        region.assign_advice(
                            || "state_root",
                            config.state_root,
                            offset,
                            || Ok(state_root),
                        )?;
                    }
                }

                #[cfg(test)]
                for ((column, row_offset), &f) in &self.overrides {
                    let advice_column = column.value(&config);
                    let offset =
                        usize::try_from(isize::try_from(padding_length).unwrap() + *row_offset)
                            .unwrap();
                    region.assign_advice(|| "override", advice_column, offset, || Ok(f))?;
                }

                Ok(())
            },
        )
    }
}

fn queries<F: Field>(meta: &mut VirtualCells<'_, F>, c: &StateConfig) -> Queries<F> {
    let first_different_limb = c.lexicographic_ordering.first_different_limb;
    let final_bits_sum = meta.query_advice(first_different_limb.bits[3], Rotation::cur())
        + meta.query_advice(first_different_limb.bits[4], Rotation::cur());

    Queries {
        selector: meta.query_fixed(c.selector, Rotation::cur()),
        lexicographic_ordering_selector: meta
            .query_fixed(c.lexicographic_ordering.selector, Rotation::cur()),
        rw_counter: MpiQueries::new(meta, c.sort_keys.rw_counter),
        is_write: meta.query_advice(c.is_write, Rotation::cur()),
        tag: c.sort_keys.tag.value(Rotation::cur())(meta),
        tag_bits: c
            .sort_keys
            .tag
            .bits
            .map(|bit| meta.query_advice(bit, Rotation::cur())),
        id: MpiQueries::new(meta, c.sort_keys.id),
        // this isn't binary! only 0 if most significant 3 bits are all 0 and at most 1 of the two
        // least significant bits is 1.
        // TODO: this can mask off just the top 3 bits if you want, since the 4th limb index is
        // Address9, which is always 0 for Rw::Stack rows.
        is_tag_and_id_unchanged: 4.expr()
            * (meta.query_advice(first_different_limb.bits[0], Rotation::cur())
                + meta.query_advice(first_different_limb.bits[1], Rotation::cur())
                + meta.query_advice(first_different_limb.bits[2], Rotation::cur()))
            + final_bits_sum.clone() * (1.expr() - final_bits_sum),
        address: MpiQueries::new(meta, c.sort_keys.address),
        field_tag: meta.query_advice(c.sort_keys.field_tag, Rotation::cur()),
        storage_key: RlcQueries::new(meta, c.sort_keys.storage_key),
        value: meta.query_advice(c.value, Rotation::cur()),
        value_prev: meta.query_advice(c.value, Rotation::prev()),
        initial_value: meta.query_advice(c.initial_value, Rotation::cur()),
        initial_value_prev: meta.query_advice(c.initial_value, Rotation::prev()),
        lookups: LookupsQueries::new(meta, c.lookups),
        power_of_randomness: c
            .power_of_randomness
            .map(|c| meta.query_instance(c, Rotation::cur())),
        // this isn't binary! only 0 if most significant 4 bits are all 1.
        first_access: 4.expr()
            - meta.query_advice(first_different_limb.bits[0], Rotation::cur())
            - meta.query_advice(first_different_limb.bits[1], Rotation::cur())
            - meta.query_advice(first_different_limb.bits[2], Rotation::cur())
            - meta.query_advice(first_different_limb.bits[3], Rotation::cur()),
        // 1 if first_different_limb is in the rw counter, 0 otherwise (i.e. any of the 4 most
        // significant bits are 0)
        not_first_access: meta.query_advice(first_different_limb.bits[0], Rotation::cur())
            * meta.query_advice(first_different_limb.bits[1], Rotation::cur())
            * meta.query_advice(first_different_limb.bits[2], Rotation::cur())
            * meta.query_advice(first_different_limb.bits[3], Rotation::cur()),
        state_root: meta.query_advice(c.state_root, Rotation::cur()),
        state_root_prev: meta.query_advice(c.state_root, Rotation::prev()),
        state_root_next: meta.query_advice(c.state_root, Rotation::next()),
    }
}

fn mpt_key(row: &Rw) -> Option<MptKey> {
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

fn fake_mpt_updates<F: Field>(rows: &[Rw], randomness: F) -> HashMap<MptKey, MptValue<F>> {
    rows.iter()
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
        .collect()
}
