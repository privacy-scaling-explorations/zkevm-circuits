//! The state circuit implementation.
mod binary_number;
mod constraint_builder;
mod lexicographic_ordering;
mod lookups;
mod multiple_precision_integer;
mod random_linear_combination;
#[cfg(test)]
mod test;

use crate::{
    evm_circuit::{
        param::N_BYTES_WORD,
        table::RwTableTag,
        util::RandomLinearCombination,
        witness::{Rw, RwMap, RwRow},
    },
    rw_table::RwTable,
};
use binary_number::{Chip as BinaryNumberChip, Config as BinaryNumberConfig};
use constraint_builder::{ConstraintBuilder, Queries};
use eth_types::{Address, Field, ToLittleEndian};
use gadgets::is_zero::{IsZeroChip, IsZeroConfig, IsZeroInstruction};
use halo2_proofs::{
    circuit::{Layouter, Region, SimpleFloorPlanner},
    plonk::{Circuit, Column, ConstraintSystem, Error, Expression, Fixed, Instance, VirtualCells},
    poly::Rotation,
};
use lexicographic_ordering::{
    Chip as LexicographicOrderingChip, Config as LexicographicOrderingConfig,
};
use lookups::{Chip as LookupsChip, Config as LookupsConfig, Queries as LookupsQueries};
use multiple_precision_integer::{Chip as MpiChip, Config as MpiConfig, Queries as MpiQueries};
use random_linear_combination::{Chip as RlcChip, Config as RlcConfig, Queries as RlcQueries};
#[cfg(test)]
use std::collections::HashMap;
use std::iter::once;

const N_LIMBS_RW_COUNTER: usize = 2;
const N_LIMBS_ACCOUNT_ADDRESS: usize = 10;
const N_LIMBS_ID: usize = 2;

/// Config for StateCircuit
#[derive(Clone)]
pub struct StateConfig<F, const QUICK_CHECK: bool> {
    // Figure out why you get errors when this is Selector.
    // https://github.com/privacy-scaling-explorations/zkevm-circuits/issues/407
    selector: Column<Fixed>,
    rw_table: RwTable,
    tag_bits: BinaryNumberConfig<RwTableTag, 4>,
    rw_counter_mpi: MpiConfig<u32, N_LIMBS_RW_COUNTER>,
    id_mpi: MpiConfig<u32, N_LIMBS_ID>,
    address_mpi: MpiConfig<Address, N_LIMBS_ACCOUNT_ADDRESS>,
    storage_key_rlc: RlcConfig<N_BYTES_WORD>,
    is_id_unchanged: IsZeroConfig<F>,
    is_storage_key_unchanged: IsZeroConfig<F>,
    lookups: LookupsConfig<QUICK_CHECK>,
    power_of_randomness: [Column<Instance>; N_BYTES_WORD - 1],
    lexicographic_ordering: LexicographicOrderingConfig<F>,
}

type Lookup<F> = (&'static str, Expression<F>, Expression<F>);

/// State Circuit for proving RwTable is valid
pub type StateCircuit<F, const N_ROWS: usize> = StateCircuitBase<F, false, N_ROWS>;
/// StateCircuit with lexicographic ordering u16 lookup disabled to allow
/// smaller `k`. It is almost impossible to trigger u16 lookup verification
/// error. So StateCircuitLight can be used in opcode gadgets test.
/// Normal opcodes constaints error can still be captured but cost much less
/// time.
pub type StateCircuitLight<F, const N_ROWS: usize> = StateCircuitBase<F, true, N_ROWS>;

/// State Circuit for proving RwTable is valid
#[derive(Default)]
pub struct StateCircuitBase<F, const QUICK_CHECK: bool, const N_ROWS: usize> {
    pub(crate) randomness: F,
    pub(crate) rows: Vec<RwRow<F>>,
    #[cfg(test)]
    overrides: HashMap<(test::AdviceColumn, isize), F>,
}

impl<F: Field, const QUICK_CHECK: bool, const N_ROWS: usize>
    StateCircuitBase<F, QUICK_CHECK, N_ROWS>
{
    /// make a new state circuit from an RwMap
    pub fn new(randomness: F, rw_map: RwMap) -> Self {
        let rows = rw_map.table_assignments(randomness);
        Self {
            randomness,
            rows,
            #[cfg(test)]
            overrides: HashMap::new(),
        }
    }
    /// estimate k needed to prover
    pub fn estimate_k(&self) -> u32 {
        let log2_ceil = |n| u32::BITS - (n as u32).leading_zeros() - (n & (n - 1) == 0) as u32;
        let k = if QUICK_CHECK { 12 } else { 18 };
        let k = k.max(log2_ceil(64 + self.rows.len()));
        log::debug!("state circuit uses k = {}", k);
        k
    }

    /// powers of randomness for instance columns
    pub fn instance(&self) -> Vec<Vec<F>> {
        (1..32)
            .map(|exp| vec![self.randomness.pow(&[exp, 0, 0, 0]); N_ROWS])
            .collect()
    }
    #[allow(clippy::too_many_arguments)]
    fn assign_row(
        &self,
        config: &StateConfig<F, QUICK_CHECK>,
        region: &mut Region<F>,
        tag_chip: &binary_number::Chip<F, RwTableTag, 4_usize>,
        is_storage_key_unchanged: &IsZeroChip<F>,
        is_id_unchanged: &IsZeroChip<F>,
        lexicographic_ordering_chip: &LexicographicOrderingChip<F>,
        offset: usize,
        row: RwRow<F>,
        prev_row: Option<RwRow<F>>,
    ) -> Result<(), Error> {
        region.assign_fixed(|| "selector", config.selector, offset, || Ok(F::one()))?;

        config
            .rw_table
            .assign_row(region, offset, self.randomness, &row)?;

        tag_chip.assign(region, offset, &row.tag)?;
        config
            .rw_counter_mpi
            .assign(region, offset, row.rw_counter as u32)?;
        config.id_mpi.assign(region, offset, row.id as u32)?;
        config.address_mpi.assign(region, offset, row.address)?;
        config
            .storage_key_rlc
            .assign(region, offset, self.randomness, row.storage_key)?;

        if offset != 0 {
            lexicographic_ordering_chip.assign(region, offset, &row, &prev_row.unwrap())?;

            // assign storage key diff
            let cur_storage_key = RandomLinearCombination::random_linear_combine(
                row.storage_key.to_le_bytes(),
                self.randomness,
            );
            let prev_storage_key = RandomLinearCombination::random_linear_combine(
                prev_row.unwrap_or_default().storage_key.to_le_bytes(),
                self.randomness,
            );
            is_storage_key_unchanged.assign(
                region,
                offset,
                Some(cur_storage_key - prev_storage_key),
            )?;

            // assign id diff
            let id_change =
                F::from(row.id as u64) - F::from(prev_row.unwrap_or_default().id as u64);
            is_id_unchanged.assign(region, offset, Some(id_change))?;
            let _storage_key_change = RandomLinearCombination::random_linear_combine(
                row.storage_key.to_le_bytes(),
                self.randomness,
            ) - RandomLinearCombination::random_linear_combine(
                prev_row.unwrap_or_default().storage_key.to_le_bytes(),
                self.randomness,
            );
        }

        Ok(())
    }
}

impl<F: Field, const QUICK_CHECK: bool, const N_ROWS: usize> Circuit<F>
    for StateCircuitBase<F, QUICK_CHECK, N_ROWS>
where
    F: Field,
{
    type Config = StateConfig<F, QUICK_CHECK>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let selector = meta.fixed_column();
        let lookups = LookupsChip::configure(meta);
        let power_of_randomness = [0; N_BYTES_WORD - 1].map(|_| meta.instance_column());

        let rw_table = RwTable::construct(meta);
        let is_storage_key_unchanged_column = meta.advice_column();
        let is_id_unchanged_column = meta.advice_column();
        let id_mpi = MpiChip::configure(meta, rw_table.id, selector, lookups);
        let address_mpi = MpiChip::configure(meta, rw_table.address, selector, lookups);
        let storage_key_rlc = RlcChip::configure(
            meta,
            selector,
            rw_table.storage_key,
            lookups,
            power_of_randomness,
        );
        let rw_counter_mpi = MpiChip::configure(meta, rw_table.rw_counter, selector, lookups);

        let tag_bits = BinaryNumberChip::configure(meta, selector);

        let lexicographic_ordering = LexicographicOrderingChip::configure(
            meta,
            tag_bits,
            rw_table.field_tag,
            id_mpi.limbs,
            address_mpi.limbs,
            storage_key_rlc.bytes,
            rw_counter_mpi.limbs,
            lookups,
        );

        let is_id_unchanged = IsZeroChip::configure(
            meta,
            |meta| meta.query_fixed(lexicographic_ordering.selector, Rotation::cur()),
            |meta| {
                meta.query_advice(rw_table.id, Rotation::cur())
                    - meta.query_advice(rw_table.id, Rotation::prev())
            },
            is_id_unchanged_column,
        );
        let is_storage_key_unchanged = IsZeroChip::configure(
            meta,
            |meta| meta.query_fixed(lexicographic_ordering.selector, Rotation::cur()),
            |meta| {
                meta.query_advice(rw_table.storage_key, Rotation::cur())
                    - meta.query_advice(rw_table.storage_key, Rotation::prev())
            },
            is_storage_key_unchanged_column,
        );

        let config = Self::Config {
            selector,
            rw_table,
            lexicographic_ordering,
            address_mpi,
            tag_bits,
            id_mpi,
            rw_counter_mpi,
            storage_key_rlc,
            is_id_unchanged,
            is_storage_key_unchanged,
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
        LookupsChip::construct(config.lookups).load(&mut layouter)?;

        let is_id_unchanged = IsZeroChip::construct(config.is_id_unchanged.clone());
        let is_storage_key_unchanged =
            IsZeroChip::construct(config.is_storage_key_unchanged.clone());
        let lexicographic_ordering_chip =
            LexicographicOrderingChip::construct(config.lexicographic_ordering.clone());

        let tag_chip = BinaryNumberChip::construct(config.tag_bits);

        layouter.assign_region(
            || "rw table",
            |mut region| {
                let padding_length = N_ROWS - self.rows.len();
                let padding = (1..=padding_length)
                    .map(|rw_counter| (Rw::Start { rw_counter }).table_assignment(self.randomness));

                let rows = padding.chain(self.rows.iter().cloned());
                let prev_rows = once(None).chain(rows.clone().map(Some));

                for (offset, (row, prev_row)) in rows.zip(prev_rows).enumerate() {
                    log::trace!("state citcuit assign offset:{} row:{:#?}", offset, row);
                    self.assign_row(
                        &config,
                        &mut region,
                        &tag_chip,
                        &is_storage_key_unchanged,
                        &is_id_unchanged,
                        &lexicographic_ordering_chip,
                        offset,
                        row,
                        prev_row,
                    )?;
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

fn queries<F: Field, const QUICK_CHECK: bool>(
    meta: &mut VirtualCells<'_, F>,
    c: &StateConfig<F, QUICK_CHECK>,
) -> Queries<F> {
    Queries {
        selector: meta.query_fixed(c.selector, Rotation::cur()),
        rw_counter: MpiQueries::new(meta, c.rw_counter_mpi),
        is_write: meta.query_advice(c.rw_table.is_write, Rotation::cur()),
        lexicographic_ordering_selector: meta
            .query_fixed(c.lexicographic_ordering.selector, Rotation::cur()),
        aux2: meta.query_advice(c.rw_table.aux2, Rotation::cur()),
        tag: c.tag_bits.value(Rotation::cur())(meta),
        tag_bits: c
            .tag_bits
            .bits
            .map(|bit| meta.query_advice(bit, Rotation::cur())),
        //prev_tag: meta.query_advice(c.rw_table.tag, Rotation::prev()),
        id: MpiQueries::new(meta, c.id_mpi),
        is_id_unchanged: c.is_id_unchanged.is_zero_expression.clone(),
        address: MpiQueries::new(meta, c.address_mpi),
        field_tag: meta.query_advice(c.rw_table.field_tag, Rotation::cur()),
        storage_key: RlcQueries::new(meta, c.storage_key_rlc),
        value: meta.query_advice(c.rw_table.value, Rotation::cur()),
        value_at_prev_rotation: meta.query_advice(c.rw_table.value, Rotation::prev()),
        value_prev: meta.query_advice(c.rw_table.value_prev, Rotation::cur()),
        lookups: LookupsQueries::new(meta, c.lookups),
        power_of_randomness: c
            .power_of_randomness
            .map(|c| meta.query_instance(c, Rotation::cur())),
        is_storage_key_unchanged: c.is_storage_key_unchanged.is_zero_expression.clone(),
        lexicographic_ordering_upper_limb_difference_is_zero: c
            .lexicographic_ordering
            .upper_limb_difference_is_zero
            .is_zero_expression
            .clone(),
    }
}
