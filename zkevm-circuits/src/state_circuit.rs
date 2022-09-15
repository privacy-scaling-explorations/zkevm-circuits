//! The state circuit implementation.
mod constraint_builder;
mod lexicographic_ordering;
mod lookups;
mod multiple_precision_integer;
mod random_linear_combination;
#[cfg(test)]
mod test;

use crate::{
    evm_circuit::param::N_BYTES_WORD,
    table::{LookupTable, MptTable, RwTable, RwTableTag},
    util::{power_of_randomness_from_instance, Expr},
    witness::{MptUpdates, Rw, RwMap},
};
use constraint_builder::{ConstraintBuilder, Queries};
use eth_types::{Address, Field};
use gadgets::binary_number::{BinaryNumberChip, BinaryNumberConfig};
use halo2_proofs::{
    circuit::{Layouter, Region, SimpleFloorPlanner, Value},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, VirtualCells},
    poly::Rotation,
};
use lexicographic_ordering::Config as LexicographicOrderingConfig;
use lookups::{Chip as LookupsChip, Config as LookupsConfig, Queries as LookupsQueries};
use multiple_precision_integer::{Chip as MpiChip, Config as MpiConfig, Queries as MpiQueries};
use random_linear_combination::{Chip as RlcChip, Config as RlcConfig, Queries as RlcQueries};
#[cfg(test)]
use std::collections::HashMap;
use std::iter::once;

use self::constraint_builder::{MptUpdateTableQueries, RwTableQueries};

const N_LIMBS_RW_COUNTER: usize = 2;
const N_LIMBS_ACCOUNT_ADDRESS: usize = 10;
const N_LIMBS_ID: usize = 2;

/// Config for StateCircuit
#[derive(Clone)]
pub struct StateCircuitConfig<F> {
    selector: Column<Fixed>, // Figure out why you get errors when this is Selector.
    // https://github.com/privacy-scaling-explorations/zkevm-circuits/issues/407
    rw_table: RwTable,
    mpt_table: MptTable,
    sort_keys: SortKeysConfig,
    initial_value: Column<Advice>, /* Assigned value at the start of the block. For Rw::Account
                                    * and Rw::AccountStorage rows this is the committed value in
                                    * the MPT, for others, it is 0. */
    state_root: Column<Advice>,
    lexicographic_ordering: LexicographicOrderingConfig,
    lookups: LookupsConfig,
    power_of_randomness: [Expression<F>; N_BYTES_WORD - 1],
}

impl<F: Field> StateCircuitConfig<F> {
    /// Configure StateCircuit
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        power_of_randomness: [Expression<F>; 31],
        rw_table: &RwTable,
        mpt_table: &MptTable,
    ) -> Self {
        let selector = meta.fixed_column();
        let lookups = LookupsChip::configure(meta);

        let rw_counter = MpiChip::configure(meta, selector, rw_table.rw_counter, lookups);
        let tag = BinaryNumberChip::configure(meta, selector, Some(rw_table.tag));
        let id = MpiChip::configure(meta, selector, rw_table.id, lookups);
        let address = MpiChip::configure(meta, selector, rw_table.address, lookups);
        let storage_key = RlcChip::configure(
            meta,
            selector,
            rw_table.storage_key,
            lookups,
            power_of_randomness.clone(),
        );

        let initial_value = meta.advice_column();
        let state_root = meta.advice_column();

        let sort_keys = SortKeysConfig {
            tag,
            id,
            field_tag: rw_table.field_tag,
            address,
            storage_key,
            rw_counter,
        };

        let lexicographic_ordering = LexicographicOrderingConfig::configure(
            meta,
            sort_keys,
            lookups,
            power_of_randomness.clone(),
        );

        let config = Self {
            selector,
            sort_keys,
            initial_value,
            state_root,
            lexicographic_ordering,
            lookups,
            power_of_randomness,
            rw_table: *rw_table,
            mpt_table: *mpt_table,
        };

        let mut constraint_builder = ConstraintBuilder::new();
        meta.create_gate("state circuit constraints", |meta| {
            let queries = queries(meta, &config);
            constraint_builder.build(&queries);
            constraint_builder.gate(queries.selector)
        });
        for (name, lookup) in constraint_builder.lookups() {
            meta.lookup_any(name, |_| lookup);
        }

        config
    }

    /// load fixed tables
    pub(crate) fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        LookupsChip::construct(self.lookups).load(layouter)
    }
    /// Make the assignments to the StateCircuit
    pub fn assign(
        &self,
        layouter: &mut impl Layouter<F>,
        rows: &[Rw],
        n_rows: usize,
        randomness: F,
    ) -> Result<(), Error> {
        let updates = MptUpdates::mock_from(rows);
        layouter.assign_region(
            || "state circuit",
            |mut region| self.assign_with_region(&mut region, rows, &updates, n_rows, randomness),
        )
    }

    fn assign_with_region(
        &self,
        region: &mut Region<'_, F>,
        rows: &[Rw],
        updates: &MptUpdates,
        n_rows: usize,
        randomness: F,
    ) -> Result<(), Error> {
        let tag_chip = BinaryNumberChip::construct(self.sort_keys.tag);

        let (rows, padding_length) = RwMap::table_assignments_prepad(rows, n_rows);
        let rows = rows.into_iter();
        let prev_rows = once(None).chain(rows.clone().map(Some));

        let mut initial_value = F::zero();
        let mut state_root = F::zero();

        for (offset, (row, prev_row)) in rows.zip(prev_rows).enumerate() {
            if offset >= padding_length {
                log::trace!("state circuit assign offset:{} row:{:#?}", offset, row);
            }

            region.assign_fixed(
                || "selector",
                self.selector,
                offset,
                || Value::known(F::one()),
            )?;

            tag_chip.assign(region, offset, &row.tag())?;

            self.sort_keys
                .rw_counter
                .assign(region, offset, row.rw_counter() as u32)?;
            if let Some(id) = row.id() {
                self.sort_keys.id.assign(region, offset, id as u32)?;
            }
            if let Some(address) = row.address() {
                self.sort_keys.address.assign(region, offset, address)?;
            }
            if let Some(storage_key) = row.storage_key() {
                self.sort_keys
                    .storage_key
                    .assign(region, offset, randomness, storage_key)?;
            }

            if let Some(prev_row) = prev_row {
                let is_first_access = self
                    .lexicographic_ordering
                    .assign(region, offset, &row, &prev_row)?;

                if is_first_access {
                    // Update initial value for RwTableTag::CallContext rows.
                    if matches!(row.tag(), RwTableTag::CallContext) {
                        initial_value = row.value_assignment(randomness)
                    }

                    // If previous row was a last access, we need to update the state root.
                    if let Some(update) = updates.get(&prev_row) {
                        let (new_root, old_root) = update.root_assignments(randomness);
                        assert_eq!(state_root, old_root);
                        state_root = new_root;
                    }
                }
            }

            // For non-RwTableTag::CallContext rows, the initial value can be determined
            // from the mpt updates or is 0.
            if !matches!(row.tag(), RwTableTag::CallContext) {
                initial_value = updates
                    .get(&row)
                    .map(|u| u.value_assignments(randomness).1)
                    .unwrap_or_default();
            }
            region.assign_advice(
                || "initial_value",
                self.initial_value,
                offset,
                || Value::known(initial_value),
            )?;

            // TODO: Switch from Rw::Start -> Rw::Padding to simplify this logic.
            // State root assignment is at previous row (offset - 1) because the state root
            // changes on the last access row.
            if offset != 0 {
                region.assign_advice(
                    || "state_root",
                    self.state_root,
                    offset - 1,
                    || Value::known(state_root),
                )?;
            }

            if offset == n_rows - 1 {
                // The last row is always a last access, so we need to handle the case where the
                // state root changes because of an mpt lookup on the last row.
                if let Some(update) = updates.get(&row) {
                    let (new_root, old_root) = update.root_assignments(randomness);
                    assert_eq!(state_root, old_root);
                    state_root = new_root;
                }
                region.assign_advice(
                    || "last row state_root",
                    self.state_root,
                    offset,
                    || Value::known(state_root),
                )?;
            }
        }

        Ok(())
    }
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
#[derive(Default, Clone)]
pub struct StateCircuit<F> {
    pub(crate) rows: Vec<Rw>,
    updates: MptUpdates,
    pub(crate) n_rows: usize,
    pub(crate) randomness: F,
    #[cfg(test)]
    overrides: HashMap<(test::AdviceColumn, isize), F>,
}

impl<F: Field> StateCircuit<F> {
    /// make a new state circuit from an RwMap
    pub fn new(randomness: F, rw_map: RwMap, n_rows: usize) -> Self {
        let rows = rw_map.table_assignments();
        let updates = MptUpdates::mock_from(&rows);
        Self {
            randomness,
            rows,
            updates,
            n_rows,
            #[cfg(test)]
            overrides: HashMap::new(),
        }
    }

    /// powers of randomness for instance columns
    pub fn instance(&self) -> Vec<Vec<F>> {
        (1..32)
            .map(|exp| vec![self.randomness.pow(&[exp, 0, 0, 0]); self.n_rows])
            .collect()
    }
}

impl<F: Field> Circuit<F> for StateCircuit<F>
where
    F: Field,
{
    type Config = StateCircuitConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let rw_table = RwTable::construct(meta);
        let mpt_table = MptTable::construct(meta);
        let power_of_randomness: [Expression<F>; 31] = power_of_randomness_from_instance(meta);
        Self::Config::configure(meta, power_of_randomness, &rw_table, &mpt_table)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        config.load(&mut layouter)?;

        // Assigning to same columns in different regions should be avoided.
        // Here we use one single region to assign `overrides` to both rw table and
        // other parts.
        layouter.assign_region(
            || "state circuit",
            |mut region| {
                config.rw_table.load_with_region(
                    &mut region,
                    &self.rows,
                    self.n_rows,
                    self.randomness,
                )?;

                config
                    .mpt_table
                    .load_with_region(&mut region, &self.updates, self.randomness)?;

                config.assign_with_region(
                    &mut region,
                    &self.rows,
                    &self.updates,
                    self.n_rows,
                    self.randomness,
                )?;
                #[cfg(test)]
                {
                    let padding_length = RwMap::padding_len(&self.rows, self.n_rows);
                    for ((column, row_offset), &f) in &self.overrides {
                        let advice_column = column.value(&config);
                        let offset =
                            usize::try_from(isize::try_from(padding_length).unwrap() + *row_offset)
                                .unwrap();
                        region.assign_advice(
                            || "override",
                            advice_column,
                            offset,
                            || Value::known(f),
                        )?;
                    }
                }

                Ok(())
            },
        )
    }
}

fn queries<F: Field>(meta: &mut VirtualCells<'_, F>, c: &StateCircuitConfig<F>) -> Queries<F> {
    let first_different_limb = c.lexicographic_ordering.first_different_limb;
    let final_bits_sum = meta.query_advice(first_different_limb.bits[3], Rotation::cur())
        + meta.query_advice(first_different_limb.bits[4], Rotation::cur());
    let mpt_update_table_expressions = c.mpt_table.table_exprs(meta);

    Queries {
        selector: meta.query_fixed(c.selector, Rotation::cur()),
        // TODO: use LookupTable trait here.
        rw_table: RwTableQueries {
            rw_counter: meta.query_advice(c.rw_table.rw_counter, Rotation::cur()),
            prev_rw_counter: meta.query_advice(c.rw_table.rw_counter, Rotation::prev()),
            is_write: meta.query_advice(c.rw_table.is_write, Rotation::cur()),
            tag: meta.query_advice(c.rw_table.tag, Rotation::cur()),
            id: meta.query_advice(c.rw_table.id, Rotation::cur()),
            prev_id: meta.query_advice(c.rw_table.id, Rotation::prev()),
            address: meta.query_advice(c.rw_table.address, Rotation::cur()),
            prev_address: meta.query_advice(c.rw_table.address, Rotation::prev()),
            field_tag: meta.query_advice(c.rw_table.field_tag, Rotation::cur()),
            storage_key: meta.query_advice(c.rw_table.storage_key, Rotation::cur()),
            value: meta.query_advice(c.rw_table.value, Rotation::cur()),
            // TODO: we should constain value.prev() <-> value_prev.cur() later
            // see https://github.com/privacy-scaling-explorations/zkevm-specs/issues/202 for more details
            value_prev: meta.query_advice(c.rw_table.value, Rotation::prev()),
        },
        // TODO: clean this up
        mpt_update_table: MptUpdateTableQueries {
            address: mpt_update_table_expressions[0].clone(),
            storage_key: mpt_update_table_expressions[1].clone(),
            proof_type: mpt_update_table_expressions[2].clone(),
            new_root: mpt_update_table_expressions[3].clone(),
            old_root: mpt_update_table_expressions[4].clone(),
            new_value: mpt_update_table_expressions[5].clone(),
            old_value: mpt_update_table_expressions[6].clone(),
        },
        lexicographic_ordering_selector: meta
            .query_fixed(c.lexicographic_ordering.selector, Rotation::cur()),
        rw_counter: MpiQueries::new(meta, c.sort_keys.rw_counter),
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
        storage_key: RlcQueries::new(meta, c.sort_keys.storage_key),
        initial_value: meta.query_advice(c.initial_value, Rotation::cur()),
        initial_value_prev: meta.query_advice(c.initial_value, Rotation::prev()),
        lookups: LookupsQueries::new(meta, c.lookups),
        power_of_randomness: c.power_of_randomness.clone(),
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
        last_access: 1.expr()
            - meta.query_advice(first_different_limb.bits[0], Rotation::next())
                * meta.query_advice(first_different_limb.bits[1], Rotation::next())
                * meta.query_advice(first_different_limb.bits[2], Rotation::next())
                * meta.query_advice(first_different_limb.bits[3], Rotation::next()),
        state_root: meta.query_advice(c.state_root, Rotation::cur()),
        state_root_prev: meta.query_advice(c.state_root, Rotation::prev()),
    }
}
